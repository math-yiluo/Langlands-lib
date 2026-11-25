/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure

/-!
# Separable residue extensions of standard tame root charts

## References

* Stacks Project, Tag 0EYH, displayed local normal form
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem factor_field_map {ι : Type*} (A : ι → Type*)
    [∀ i, CommRing (A i)] [Finite ι] {L : Type*} [Field L]
    (φ : (∀ i, A i) →+* L) :
    ∃ (i : ι) (g : A i →+* L), g.comp (Pi.evalRingHom A i) = φ := by
  let p : PrimeSpectrum (∀ i, A i) := ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
  have hk : RingHom.ker (Pi.evalRingHom A i) ≤ RingHom.ker φ := by
    intro a ha
    have hqa : a ∈ (PrimeSpectrum.comap (Pi.evalRingHom A i) q).asIdeal := by
      change (Pi.evalRingHom A i) a ∈ q.asIdeal
      rw [RingHom.mem_ker] at ha
      simp [ha]
    simpa [hq, p] using hqa
  let hs : Function.Surjective (Pi.evalRingHom A i) := RingHomSurjective.is_surjective
  exact ⟨i, (Pi.evalRingHom A i).liftOfSurjective hs ⟨φ, hk⟩,
    RingHom.liftOfSurjective_comp _ hs ⟨φ, hk⟩⟩

private theorem root_isSeparable {K L : Type*} [Field K] [Field L] [Algebra K L]
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : K)) (a : K) (t : L)
    (ht : t ^ n = algebraMap K L a) : IsSeparable K t := by
  by_cases ha : a = 0
  · have hz : t = 0 := by
      apply (pow_eq_zero_iff (Nat.ne_of_gt hn)).mp
      simpa [ha] using ht
    subst t
    simpa using isSeparable_algebraMap (K := L) (0 : K)
  · exact (Polynomial.separable_X_pow_sub_C a hu.ne_zero ha).of_dvd
      (minpoly.dvd K t (by simp [ht]))

private theorem residue_mem_of_coefficients_mem (R : CommRingCat.{u}) (x : Spec R)
    {K : Type*} [Field K] [Algebra K ((Spec R).residueField x)]
    (S : IntermediateField K ((Spec R).residueField x))
    (hS : ∀ a : R,
      ((ΓSpecIso R).inv ≫ (Spec R).Γevaluation x) a ∈ S)
    (z : (Spec R).residueField x) : z ∈ S := by
  let E := Spec.residueFieldIso R x
  have hcoeff (a : R) : E.inv (algebraMap R x.asIdeal.ResidueField a) ∈ S := by
    have h := ConcreteCategory.congr_hom (Spec.algebraMap_residueFieldIso_inv R x) a
    exact h ▸ hS a
  have hquot (a : R ⧸ x.asIdeal) :
      E.inv (algebraMap (R ⧸ x.asIdeal) x.asIdeal.ResidueField a) ∈ S := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hcoeff a
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj
    (nonZeroDivisors (R ⧸ x.asIdeal)) (E.hom z)
  have hb : E.inv (algebraMap (R ⧸ x.asIdeal) x.asIdeal.ResidueField b) ≠ 0 := by
    exact ((IsLocalization.map_units x.asIdeal.ResidueField b).map E.inv.hom).ne_zero
  have heq : z * E.inv (algebraMap (R ⧸ x.asIdeal) x.asIdeal.ResidueField b) =
      E.inv (algebraMap (R ⧸ x.asIdeal) x.asIdeal.ResidueField a) := by
    have h' := congrArg E.inv.hom h
    rw [map_mul] at h'
    have hinv : E.inv.hom (E.hom z) = z :=
      ConcreteCategory.congr_hom E.hom_inv_id z
    simpa only [hinv] using h'
  rw [(eq_div_iff hb).mpr heq]
  exact S.div_mem (hquot a) (hquot b)

/-- Finite products of standard root charts have separable residue extensions. -/
theorem tameRootProduct_residue_separable (R : CommRingCat.{u})
    (m : ℕ) (f : R) (e : Fin m → ℕ)
    (he : ∀ k, 0 < e k ∧ IsUnit (e k : R)) :
    let D := CommRingCat.of (∀ k : Fin m,
      AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f))
    let π : Spec D ⟶ Spec R :=
      Spec.map (CommRingCat.ofHom (algebraMap R D))
    ∀ x : Spec D,
      letI := (π.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparable ((Spec R).residueField (π x)) ((Spec D).residueField x) := by
  classical
  dsimp only
  let D := CommRingCat.of (∀ k : Fin m,
    AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f))
  let π : Spec D ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R D))
  intro x
  let K := (Spec R).residueField (π x)
  let L := (Spec D).residueField x
  let := (π.residueFieldMap x).hom.toAlgebra
  let α : R →+* K := ((ΓSpecIso R).inv ≫ (Spec R).Γevaluation (π x)).hom
  let β : D →+* L := ((ΓSpecIso D).inv ≫ (Spec D).Γevaluation x).hom
  have hcompat (r : R) : β (algebraMap R D r) = algebraMap K L (α r) := by
    change ((CommRingCat.ofHom (algebraMap R D) ≫
      (ΓSpecIso D).inv ≫ (Spec D).Γevaluation x) r) =
      (((ΓSpecIso R).inv ≫ (Spec R).Γevaluation (π x) ≫ π.residueFieldMap x) r)
    congr 1
    rw [Γevaluation_naturality, ΓSpecIso_inv_naturality_assoc]
    rfl
  obtain ⟨i, g, hg⟩ := factor_field_map
    (fun k : Fin m => AdjoinRoot ((Polynomial.X : Polynomial R) ^ e k - Polynomial.C f)) β
  let p : Polynomial R := Polynomial.X ^ e i - Polynomial.C f
  let t : L := g (AdjoinRoot.root p)
  have hgcoeff (r : R) : g (algebraMap R (AdjoinRoot p) r) = algebraMap K L (α r) := by
    have h := DFunLike.congr_fun hg (algebraMap R D r)
    exact h.trans (hcompat r)
  have hpow : t ^ e i = algebraMap K L (α f) := by
    have h := congrArg g (AdjoinRoot.mk_self (f := p))
    change g (AdjoinRoot.mk p (Polynomial.X ^ e i - Polynomial.C f)) = g 0 at h
    simpa [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
      ← AdjoinRoot.algebraMap_eq, hgcoeff, sub_eq_zero, t] using h
  have hunit : IsUnit (e i : K) := by
    simpa using (he i).2.map α
  have ht : IsSeparable K t := root_isSeparable (e i) (he i).1 hunit (α f) t hpow
  let S := separableClosure K L
  have htS : t ∈ S := ht
  have hgS (a : AdjoinRoot p) : g a ∈ S := by
    induction a using AdjoinRoot.induction_on with
    | ih q =>
      induction q using Polynomial.induction_on' with
      | add q r hq hr => simpa using S.add_mem hq hr
      | monomial n r =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow]
        have hr : g (AdjoinRoot.mk p (Polynomial.C r)) ∈ S := by
          change g (algebraMap R (AdjoinRoot p) r) ∈ S
          rw [hgcoeff]
          exact S.algebraMap_mem (α r)
        exact S.mul_mem hr (S.toSubalgebra.pow_mem htS n)
  have hβS (a : D) : β a ∈ S := by
    rw [← hg]
    exact hgS (a i)
  exact ⟨fun z => residue_mem_of_coefficients_mem D x S hβS z⟩

end AlgebraicGeometry.Scheme
