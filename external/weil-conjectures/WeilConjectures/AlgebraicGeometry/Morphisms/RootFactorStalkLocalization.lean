/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! Base localization of a single root factor at a specified point.

## References

* Stacks Project, Tags 0EYH and 0EYI, base change of the affine root factors
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A coefficient localization induces a localization of every root quotient. -/
private theorem adjoinRoot_isLocalization_map (R : Type u) (S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (p : Polynomial R) :
    let g := AdjoinRoot.map (algebraMap R S) p (p.map (algebraMap R S)) dvd_rfl
    let := g.toAlgebra
    IsLocalization (M.map (AdjoinRoot.of p)) (AdjoinRoot (p.map (algebraMap R S))) := by
  let : Algebra (Polynomial R) (Polynomial S) := Polynomial.algebra R S
  let g := AdjoinRoot.map (algebraMap R S) p (p.map (algebraMap R S)) dvd_rfl
  let := g.toAlgebra
  let := Polynomial.isLocalization M S
  have h : (AdjoinRoot.mk (p.map (algebraMap R S))).comp
      (algebraMap (Polynomial R) (Polynomial S)) =
      (algebraMap (AdjoinRoot p) (AdjoinRoot (p.map (algebraMap R S)))).comp
        (AdjoinRoot.mk p) := by
    change (AdjoinRoot.mk _).comp (Polynomial.mapRingHom (algebraMap R S)) =
      g.comp (AdjoinRoot.mk p)
    ext x <;> simp [g]
  have hkR : RingHom.ker (AdjoinRoot.mk p) = Ideal.span {p} := by
    ext x
    simp [RingHom.mem_ker, AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton]
  have hkS : RingHom.ker (AdjoinRoot.mk (p.map (algebraMap R S))) =
      Ideal.span {p.map (algebraMap R S)} := by
    ext x
    simp [RingHom.mem_ker, AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton]
  have hk : RingHom.ker (AdjoinRoot.mk (p.map (algebraMap R S))) ≤
      (RingHom.ker (AdjoinRoot.mk p)).map
        (algebraMap (Polynomial R) (Polynomial S)) := by
    rw [hkR, hkS]
    change Ideal.span {p.map (algebraMap R S)} ≤
      (Ideal.span {p}).map (Polynomial.mapRingHom (algebraMap R S))
    apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton p))
  have hloc := IsLocalization.of_surjective (M.map Polynomial.C) (Polynomial S)
    (AdjoinRoot.mk p) (AdjoinRoot.mk_surjective (g := p))
    (AdjoinRoot.mk (p.map (algebraMap R S)))
    (AdjoinRoot.mk_surjective (g := p.map (algebraMap R S))) h hk
  have hm : M.map (AdjoinRoot.of p) = (M.map Polynomial.C).map (AdjoinRoot.mk p) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨Polynomial.C a, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
  exact hm ▸ hloc

private theorem spec_stalkMap_toStalk (R S : CommRingCat.{u}) (i : R →+* S)
    (q : Spec S ⟶ Spec R) (hq : q = Spec.map (CommRingCat.ofHom i))
    (w : Spec S) (a : R) :
    (q.stalkMap w).hom ((StructureSheaf.toStalk R (q w)).hom a) =
      (StructureSheaf.toStalk S w).hom (i a) := by
  subst q
  exact stalkMap_toStalk_apply (CommRingCat.ofHom i) w a

/-- Localization of a root algebra at a prime commutes with localization of its base. -/
theorem rootFactor_stalk_localization (R : CommRingCat.{u}) (f : R)
    (d : ℕ) (hd : 0 < d)
    (q : Spec (CommRingCat.of
      (AdjoinRoot ((Polynomial.X : Polynomial R) ^ d - Polynomial.C f))) ⟶ Spec R)
    (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R
      (AdjoinRoot ((Polynomial.X : Polynomial R) ^ d - Polynomial.C f)))))
    (w : Spec (CommRingCat.of
      (AdjoinRoot ((Polynomial.X : Polynomial R) ^ d - Polynomial.C f))))
    (hf : f ∈ (q w).asIdeal) :
    let R₀ := (Spec R).presheaf.stalk (q w)
    ∃ (f₀ : R₀), f₀ ∈ IsLocalRing.maximalIdeal R₀ ∧
      let p := (Polynomial.X : Polynomial R₀) ^ d - Polynomial.C f₀
      let D := AdjoinRoot p
      ∃ (P : Ideal D) (hP : P.IsMaximal),
        letI : P.IsPrime := hP.isPrime
        let E := Localization.AtPrime P
        ∃ θ : (Spec (CommRingCat.of
          (AdjoinRoot ((Polynomial.X : Polynomial R) ^ d - Polynomial.C f)))).presheaf.stalk w
            ≃+* E,
          θ.toRingHom.comp (q.stalkMap w).hom =
            (algebraMap D E).comp (AdjoinRoot.of p) := by
  classical
  let H := AdjoinRoot ((Polynomial.X : Polynomial R) ^ d - Polynomial.C f)
  let p := (Polynomial.X : Polynomial R) ^ d - Polynomial.C f
  let r := (q w).asIdeal
  let R₀ := (Spec R).presheaf.stalk (q w)
  let : Algebra R R₀ := StructureSheaf.stalkAlgebra R _
  let : IsLocalization.AtPrime R₀ r := StructureSheaf.IsLocalization.to_stalk R _
  let f₀ : R₀ := algebraMap R R₀ f
  refine ⟨f₀, ?_, ?_⟩
  · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R₀ r f).mpr hf
  let p₀ := p.map (algebraMap R R₀)
  have hp₀ : (Polynomial.X : Polynomial R₀) ^ d - Polynomial.C f₀ = p₀ := by
    simp [p₀, p, f₀]
  dsimp only
  rw [hp₀]
  let D := AdjoinRoot p₀
  let g : H →+* D := AdjoinRoot.map (algebraMap R R₀) p p₀ dvd_rfl
  let : Algebra H D := g.toAlgebra
  let M : Submonoid H := r.primeCompl.map (AdjoinRoot.of p)
  let : IsLocalization M D := adjoinRoot_isLocalization_map R R₀ r.primeCompl p
  have hcon : w.asIdeal.comap (AdjoinRoot.of p) = r := by
    change (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p)) w).asIdeal = (q w).asIdeal
    exact congrArg (fun t : Spec (CommRingCat.of H) ⟶ Spec R ↦ (t w).asIdeal) hq.symm
  have hdis : Disjoint (M : Set H) (w.asIdeal : Set H) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, rfl⟩ hw
    apply ha
    rw [← hcon]
    exact hw
  let P : Ideal D := w.asIdeal.map g
  have hPprime : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M D w.asIdeal w.isPrime hdis
  have hPw : P.comap g = w.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint M D w.isPrime hdis
  have hcoeff : g.comp (AdjoinRoot.of p) = (AdjoinRoot.of p₀).comp (algebraMap R R₀) := by
    ext a
    exact AdjoinRoot.map_of (algebraMap R R₀) p p₀ dvd_rfl a
  have hbase : P.comap (AdjoinRoot.of p₀) = IsLocalRing.maximalIdeal R₀ := by
    apply (IsLocalization.orderEmbedding r.primeCompl R₀).injective
    change (P.comap (AdjoinRoot.of p₀)).comap (algebraMap R R₀) =
      (IsLocalRing.maximalIdeal R₀).comap (algebraMap R R₀)
    rw [Ideal.comap_comap, ← hcoeff, ← Ideal.comap_comap, hPw, hcon]
    exact (IsLocalization.AtPrime.under_maximalIdeal R₀ r).symm
  have hmonic : p₀.Monic := by
    rw [← hp₀]
    exact Polynomial.monic_X_pow_sub_C _ (Nat.ne_of_gt hd)
  let : Module.Finite R₀ D := hmonic.finite_adjoinRoot
  have hb : (P.comap (algebraMap R₀ D)).IsMaximal := by
    change (P.comap (AdjoinRoot.of p₀)).IsMaximal
    rw [hbase]
    exact IsLocalRing.maximalIdeal.isMaximal R₀
  have hP : P.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R₀) P hb
  refine ⟨P, hP, ?_⟩
  let E := Localization.AtPrime P
  have hloc : IsLocalization.AtPrime E w.asIdeal := by
    have h : IsLocalization.AtPrime E (P.comap g) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M E P
    simpa only [hPw] using h
  let : IsLocalization.AtPrime E w.asIdeal := hloc
  let S := (Spec (CommRingCat.of H)).presheaf.stalk w
  let : Algebra H S := StructureSheaf.stalkAlgebra H w
  let : IsLocalization.AtPrime S w.asIdeal := StructureSheaf.IsLocalization.to_stalk H w
  let θ : S ≃ₐ[H] E := IsLocalization.algEquiv w.asIdeal.primeCompl S E
  refine ⟨θ.toRingEquiv, ?_⟩
  apply IsLocalization.ringHom_ext r.primeCompl
  ext a
  change θ ((q.stalkMap w).hom (algebraMap R R₀ a)) =
    algebraMap D E (AdjoinRoot.of p₀ (algebraMap R R₀ a))
  have hs : (q.stalkMap w).hom (algebraMap R R₀ a) =
      algebraMap H S (AdjoinRoot.of p a) := by
    exact spec_stalkMap_toStalk R (CommRingCat.of H) (algebraMap R H) q hq w a
  rw [hs, θ.commutes]
  change algebraMap D E (g (AdjoinRoot.of p a)) = _
  rw [show g (AdjoinRoot.of p a) = AdjoinRoot.of p₀ (algebraMap R R₀ a) from
    AdjoinRoot.map_of (algebraMap R R₀) p p₀ dvd_rfl a]

end AlgebraicGeometry.Scheme
