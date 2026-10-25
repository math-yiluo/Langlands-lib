import Langlands.AlgebraicGeometry.FiniteEtale.InvariantAlgebraStatements
import Mathlib.RingTheory.Invariant.Basic

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open Polynomial

private theorem exists_orbit_value
    {A K G : Type*} [CommRing A] [CommRing K] [IsDomain K]
    [Group G] [Fintype G] [MulSemiringAction G A]
    (x y : A →+* K)
    (h : ∀ a : A, (∀ g : G, g • a = a) → x a = y a) (a : A) :
    ∃ g : G, y a = x (g • a) := by
  have hp : (MulSemiringAction.charpoly G a).map x =
      (MulSemiringAction.charpoly G a).map y := by
    ext n
    simpa only [coeff_map] using h _ (MulSemiringAction.smul_coeff_charpoly a n)
  have hz : ((MulSemiringAction.charpoly G a).map x).eval (y a) = 0 := by
    rw [hp, eval_map, eval₂_at_apply, MulSemiringAction.eval_charpoly, map_zero]
  simpa [MulSemiringAction.charpoly, Polynomial.map_prod, Polynomial.eval_prod,
    sub_eq_zero, Finset.prod_eq_zero_iff] using hz

private theorem exists_orbit_hom
    {A K G : Type*} [CommRing A] [CommRing K] [IsDomain K]
    [Group G] [Finite G] [MulSemiringAction G A]
    (x y : A →+* K)
    (h : ∀ a : A, (∀ g : G, g • a = a) → x a = y a) :
    ∃ g : G, ∀ a : A, y a = x (g • a) := by
  classical
  let := Fintype.ofFinite G
  by_contra hn
  push Not at hn
  choose a ha using hn
  let e := Fintype.equivFin G
  let p : A[X] := ∑ g : G, monomial (e g).val (a g)
  have hc (g : G) : p.coeff (e g).val = a g := by
    simp only [p, finsetSum_coeff, coeff_monomial]
    rw [Finset.sum_eq_single g]
    · simp
    · intro b _ hb
      have he : (e b).val ≠ (e g).val := fun he ↦ hb (e.injective (Fin.ext he))
      simp [he]
    · simp
  obtain ⟨g, hg⟩ := exists_orbit_value (Polynomial.mapRingHom x)
    (Polynomial.mapRingHom y) (fun q hq ↦ by
      ext n
      simp only [coe_mapRingHom, coeff_map]
      apply h
      intro g
      simpa only [coeff_smul] using congrArg (fun q : A[X] ↦ q.coeff n) (hq g)) p
  have he := congrArg (fun q : K[X] ↦ q.coeff (e g).val) hg
  simp only [coe_mapRingHom, coeff_map, coeff_smul, hc] at he
  exact ha g he

private theorem exists_extension_of_integral
    {C A K : Type*} [CommRing C] [CommRing A] [Field K] [IsAlgClosed K]
    [Algebra C A] [Algebra.IsIntegral C A] [FaithfulSMul C A]
    (f : C →+* K) : ∃ x : A →+* K, x.comp (algebraMap C A) = f := by
  let P := RingHom.ker f
  have : P.IsPrime := RingHom.ker_isPrime f
  obtain ⟨Q, hQ, hQP⟩ := (inferInstance : Nonempty (P.primesOver A))
  have : Q.IsPrime := hQ
  have : Q.LiesOver P := hQP
  let j : (C ⧸ P) →+* K := f.kerLift
  let : Algebra (C ⧸ P) K := j.toAlgebra
  have : FaithfulSMul (C ⧸ P) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective f)
  let k : (A ⧸ Q) →ₐ[C ⧸ P] K := IsAlgClosed.lift
  refine ⟨k.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext c
  change k (Ideal.Quotient.mk Q (algebraMap C A c)) = f c
  exact k.commutes (Ideal.Quotient.mk P c)

/-- Geometric points of a finite invariant algebra form the group-orbit quotient. -/
theorem invariantAlgebraGeometricPoints (R A G Ω : Type u)
    [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] :
    InvariantAlgebraGeometricPoints R A G Ω := by
  let C := FixedPoints.subalgebra R A G
  have : Algebra.IsInvariant C A G := ⟨fun a ha ↦ ⟨⟨a, ha⟩, rfl⟩⟩
  have : Algebra.IsIntegral C A := Algebra.IsInvariant.isIntegral C A G
  constructor
  · intro f
    obtain ⟨x, hx⟩ := exists_extension_of_integral (A := A) f.toRingHom
    let x' : A →ₐ[R] Ω :=
      { x with
        commutes' := fun r ↦ by
          have hr := DFunLike.congr_fun hx (algebraMap R C r)
          exact hr.trans (f.commutes r) }
    refine ⟨x', ?_⟩
    ext c
    exact DFunLike.congr_fun hx c
  · intro x y
    constructor
    · intro h
      obtain ⟨g, hg⟩ := exists_orbit_hom (G := G) x.toRingHom y.toRingHom
        (fun a ha ↦ DFunLike.congr_fun h ⟨a, ha⟩)
      exact ⟨g, AlgHom.ext hg⟩
    · rintro ⟨g, rfl⟩
      ext c
      exact congrArg x (c.property g).symm

end Langlands.AlgebraicGeometry.FiniteEtale
