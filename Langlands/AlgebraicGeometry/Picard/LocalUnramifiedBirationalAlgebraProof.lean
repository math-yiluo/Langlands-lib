import Mathlib.RingTheory.Unramified.LocalStructure
import Langlands.AlgebraicGeometry.Picard.LocalUnramifiedBirationalAlgebraStatement

/-! # Local algebra for birational unramified morphisms -/

universe u v w

open IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry

private theorem surjective_of_finite_unramified_of_surjective_residue
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]
    [Module.Finite R A] [Algebra.FormallyUnramified R A]
    (hres : Function.Surjective (algebraMap (ResidueField R) (ResidueField A))) :
    Function.Surjective (algebraMap R A) := by
  change Function.Surjective (Algebra.linearMap R A)
  rw [← LinearMap.range_eq_top, ← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (maximalIdeal_le_jacobson _)
  rw [Ideal.smul_top_eq_map, Algebra.FormallyUnramified.map_maximalIdeal]
  rintro x -
  obtain ⟨a, ha⟩ := hres (residue A x)
  obtain ⟨a, rfl⟩ := residue_surjective a
  rw [ResidueField.algebraMap_residue, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at ha
  rw [← sub_sub_self (algebraMap R A a) x]
  exact sub_mem (Submodule.mem_sup_left ⟨a, rfl⟩) (Submodule.mem_sup_right ha)

private theorem isLocalRing_of_integral_embedding_fractionRing
    (R C : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing C] [Algebra R C] [Algebra.IsIntegral R C]
    (hR : GeometricallyUnibranchDomain R)
    (g : C →ₐ[R] FractionRing R) (hg : Function.Injective g) : IsLocalRing C := by
  obtain ⟨hB, _, _⟩ := hR
  let B := integralClosure R (FractionRing R)
  let : IsLocalRing B := hB
  let f : C →ₐ[R] B := g.codRestrict B fun c =>
    (Algebra.IsIntegral.isIntegral c).map g
  let : Algebra C B := f.toAlgebra
  let : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have hf : Function.Injective (algebraMap C B) := by
    intro a b hab
    apply hg
    exact congrArg (fun z : B => (z : FractionRing R)) hab
  let : FaithfulSMul C B := (faithfulSMul_iff_algebraMap_injective C B).mpr hf
  have : Algebra.IsIntegral C B := Algebra.IsIntegral.tower_top (R := R)
  exact (algebraMap C B).domain_isLocalRing

/-- A finite unramified subalgebra of the fraction field of a geometrically
unibranch local domain consists only of elements from the base ring. -/
theorem finiteUnramifiedSubalgebra_eq_bot
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    (hR : GeometricallyUnibranchDomain R)
    (A : Subalgebra R (FractionRing R)) [Module.Finite R A]
    [Algebra.FormallyUnramified R A] : A = ⊥ := by
  obtain ⟨hB, hlocal, hpure⟩ := hR
  let B := integralClosure R (FractionRing R)
  let : IsLocalRing B := hB
  let : IsLocalHom (algebraMap R B) := hlocal
  have hle : A ≤ B := le_integralClosure_iff_isIntegral.mpr inferInstance
  let f : A →ₐ[R] B := Subalgebra.inclusion hle
  let : Algebra A B := f.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have hf : Function.Injective (algebraMap A B) := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : B => (z : FractionRing R)) hab
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hf
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.tower_top (R := R)
  let : IsLocalRing A := (algebraMap A B).domain_isLocalRing
  have : IsLocalHom (algebraMap R A) := inferInstance
  have hmap : ResidueField.map (algebraMap R B) =
      algebraMap (ResidueField R) (ResidueField B) := by
    ext x
    obtain ⟨x, rfl⟩ := residue_surjective x
    rfl
  have : IsPurelyInseparable (ResidueField R) (ResidueField B) := by
    rw [← RingHom.isPurelyInseparable_algebraMap_iff, ← hmap]
    exact hpure
  have : IsPurelyInseparable (ResidueField R) (ResidueField A) :=
    IsPurelyInseparable.tower_bot (ResidueField R) (ResidueField A) (ResidueField B)
  have hsurj : Function.Surjective (algebraMap R A) :=
    surjective_of_finite_unramified_of_surjective_residue R A
      (IsPurelyInseparable.surjective_algebraMap_of_isSeparable _ _)
  apply bot_unique
  intro a ha
  obtain ⟨r, hr⟩ := hsurj ⟨a, ha⟩
  exact Algebra.mem_bot.mpr ⟨r, congrArg Subtype.val hr⟩

/-- The finite type local birational algebra conclusion, using algebraic
Zariski's Main Theorem to reduce to the finite subalgebra case. -/
theorem localUnramifiedBirationalAlgebra : LocalUnramifiedBirationalAlgebraStatement.{u} := by
  intro R _ _ _ hR A _ _ q _ _
  let C := integralClosure R A
  let : Algebra C A := C.toAlgebra
  let : IsScalarTower R C A := Subalgebra.isScalarTower_mid C
  let g : C →ₐ[R] FractionRing R := A.val.comp C.val
  have hg : Function.Injective g := Subtype.val_injective.comp Subtype.val_injective
  let : IsLocalRing C := isLocalRing_of_integral_embedding_fractionRing R C hR g hg
  have hqC : (q.under C).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) (S := C) (q.under C) (by
      simpa only [Ideal.under_under, q.over_def (maximalIdeal R)] using maximalIdeal.isMaximal R)
  have heq : q.under C = maximalIdeal C := eq_maximalIdeal hqC
  obtain ⟨r, hrq, hr, hmul⟩ := Algebra.zariskisMainProperty_iff.mp
    (Algebra.ZariskisMainProperty.of_finiteType (R := R) q)
  let rC : C := ⟨r, hr⟩
  have hrC : IsUnit rC := notMem_maximalIdeal.mp (by
    rw [← heq]
    exact hrq)
  have hinv : ((↑(hrC.unit⁻¹) : C) : A) * r = 1 := by
    change C.val ((↑(hrC.unit⁻¹) : C) * rC) = 1
    simpa only [hrC.unit_spec, map_one] using congrArg C.val (Units.inv_mul hrC.unit)
  have : Algebra.IsIntegral R A := ⟨fun x => by
    obtain ⟨n, hn⟩ := hmul x
    have hi : IsIntegral R (((↑(hrC.unit⁻¹) : C) : A) ^ n * (r ^ n * x)) :=
      (((↑(hrC.unit⁻¹) : C).property).pow n).mul hn
    rwa [← mul_assoc, ← mul_pow, hinv, one_pow, one_mul] at hi⟩
  have : Module.Finite R A := Algebra.IsIntegral.finite
  exact finiteUnramifiedSubalgebra_eq_bot R hR A

/-- The same local conclusion for an algebra embedding into any fraction ring:
the actual structure map from the base ring is surjective. -/
theorem algebraMap_surjective_of_unramified_fractionRing_embedding
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    (hR : GeometricallyUnibranchDomain R)
    (B : Type v) [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] [Algebra.FormallyUnramified R B]
    (K : Type w) [CommRing K] [Algebra R K] [IsFractionRing R K]
    (j : B →ₐ[R] K) (hj : Function.Injective j)
    (q : Ideal B) [q.IsPrime] [q.LiesOver (maximalIdeal R)] :
    Function.Surjective (algebraMap R B) := by
  let f : B →ₐ[R] FractionRing R := (FractionRing.algEquiv R K).symm.toAlgHom.comp j
  have hf : Function.Injective f := (FractionRing.algEquiv R K).symm.injective.comp hj
  let e : B ≃ₐ[R] f.range := AlgEquiv.ofInjective f hf
  let : Algebra.FiniteType R f.range := Algebra.FiniteType.of_surjective e.toAlgHom e.surjective
  let : Algebra.FormallyUnramified R f.range := Algebra.FormallyUnramified.of_equiv e
  let p : Ideal f.range := q.comap e.symm.toRingHom
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have : p.LiesOver (maximalIdeal R) :=
    Ideal.comap_liesOver q (maximalIdeal R) e.symm.toAlgHom
  have hbot : f.range = ⊥ := localUnramifiedBirationalAlgebra R hR f.range p
  intro b
  have hb : f b ∈ (⊥ : Subalgebra R (FractionRing R)) := by
    rw [← hbot]
    exact f.mem_range_self b
  obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hb
  exact ⟨r, hf ((f.commutes r).trans hr)⟩

/-- An essentially finite type unramified local algebra that embeds in a fraction
ring of a geometrically unibranch local domain has surjective structure map. -/
theorem algebraMap_surjective_of_essFiniteType_unramified_fractionRing_embedding
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    (hR : GeometricallyUnibranchDomain R)
    (B : Type v) [CommRing B] [IsLocalRing B] [Algebra R B]
    [IsLocalHom (algebraMap R B)]
    [Algebra.EssFiniteType R B] [Algebra.FormallyUnramified R B]
    (K : Type w) [CommRing K] [Algebra R K] [IsFractionRing R K]
    (j : B →ₐ[R] K) (hj : Function.Injective j) :
    Function.Surjective (algebraMap R B) := by
  let A := Algebra.EssFiniteType.subalgebra R B
  let M := Algebra.EssFiniteType.submonoid R B
  let p : Ideal A := (maximalIdeal B).under A
  have : p.IsPrime := inferInstance
  have hM : M = p.primeCompl := by
    ext a
    change IsUnit (a : B) ↔ (a : B) ∉ maximalIdeal B
    exact notMem_maximalIdeal.symm
  let : IsLocalization p.primeCompl B := by
    rw [← hM]
    exact Algebra.EssFiniteType.isLocalization R B
  let e : Localization.AtPrime p ≃ₐ[R] B :=
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) B).restrictScalars R
  let : Algebra.IsUnramifiedAt R p := Algebra.FormallyUnramified.of_equiv e.symm
  obtain ⟨f, hfp, hf⟩ := Algebra.exists_unramified_of_isUnramifiedAt (R := R) p
  let : Algebra.Unramified R (Localization.Away f) := hf
  have hfu : IsUnit (algebraMap A B f) := notMem_maximalIdeal.mp hfp
  let l : Localization.Away f →ₐ[R] B :=
    IsLocalization.Away.liftAlgHom f (f := IsScalarTower.toAlgHom R A B) hfu
  have hlA (a : A) : l (algebraMap A (Localization.Away f) a) = (a : B) := by
    change IsLocalization.Away.lift f hfu (algebraMap A (Localization.Away f) a) = _
    exact IsLocalization.Away.lift_eq f hfu a
  have hl : Function.Injective l := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (.powers f) l.toRingHom).mpr
    intro a b
    change algebraMap A (Localization.Away f) a = algebraMap A (Localization.Away f) b ↔
      l (algebraMap A (Localization.Away f) a) = l (algebraMap A (Localization.Away f) b)
    rw [hlA, hlA]
    exact ⟨fun h => by simpa only [hlA] using congrArg l h,
      fun h => congrArg (algebraMap A (Localization.Away f)) (Subtype.ext h)⟩
  let q : Ideal (Localization.Away f) := (maximalIdeal B).comap l.toRingHom
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : q.LiesOver (maximalIdeal R) :=
    Ideal.comap_liesOver (maximalIdeal B) (maximalIdeal R) l
  have hsurj := algebraMap_surjective_of_unramified_fractionRing_embedding
    R hR (Localization.Away f) K (j.comp l) (hj.comp hl) q
  have hA (a : A) : ∃ r : R, algebraMap R B r = (a : B) := by
    obtain ⟨r, hr⟩ := hsurj (algebraMap A (Localization.Away f) a)
    refine ⟨r, ?_⟩
    have h := congrArg l hr
    simpa only [l.commutes, hlA] using h
  intro b
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj M b
  change b * (s : B) = (a : B) at hs
  obtain ⟨r, hr⟩ := hA a
  obtain ⟨t, ht⟩ := hA s
  have htu : IsUnit t := isUnit_of_map_unit (algebraMap R B) t (ht.symm ▸ s.property)
  refine ⟨r * (↑(htu.unit⁻¹) : R), ?_⟩
  have heq : algebraMap R B r = b * algebraMap R B t := by
    simpa only [hr, ht] using hs.symm
  have htinv : t * (↑(htu.unit⁻¹) : R) = 1 := by
    simpa only [htu.unit_spec] using Units.mul_inv htu.unit
  rw [map_mul, heq, mul_assoc, ← map_mul, htinv, map_one, mul_one]

end Langlands.AlgebraicGeometry
