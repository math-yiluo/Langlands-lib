import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Split standard etale algebras and local isomorphisms -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- Monic polynomials split in an integrally closed domain with algebraically
closed fraction field. -/
theorem monic_splits_of_isAlgClosed_fractionField
    {R K : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [IsAlgClosed K] [Algebra R K] [IsFractionRing R K]
    {f : R[X]} (hf : f.Monic) : f.Splits := by
  apply (IsAlgClosed.splits (f.map (algebraMap R K))).of_splits_map_of_injective
    (IsFractionRing.injective R K)
  intro a ha
  apply IsIntegrallyClosed.isIntegral_iff.mp
  refine ⟨f, hf, ?_⟩
  rw [eval₂_eq_eval_map]
  exact (Polynomial.mem_roots (hf.map (algebraMap R K)).ne_zero).mp ha

namespace SplitStandardEtale

variable {R B : Type u} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    (P : StandardEtalePresentation R B)

/-- A root of the split presentation on a field-valued test is the image of
one of the roots in the base ring. -/
theorem exists_baseRoot_of_splits (hsplit : P.f.Splits)
    {L : Type u} [Field L] [Algebra R L] (φ : B →ₐ[R] L) :
    ∃ a : R, P.f.eval a = 0 ∧ φ P.x = algebraMap R L a := by
  classical
  have hroot := (P.hasMap.map φ).1
  have hprod : (P.f.roots.map (fun a => φ P.x - algebraMap R L a)).prod = 0 := by
    rw [hsplit.eq_prod_roots_of_monic P.monic_f] at hroot
    simpa only [map_multiset_prod, Multiset.map_map, Function.comp_def, map_sub,
      aeval_X, aeval_C] using hroot
  obtain ⟨a, ha, he⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod)
  exact ⟨a, (Polynomial.mem_roots P.monic_f.ne_zero).mp ha, sub_eq_zero.mp he⟩

/-- A base root supplies an actual map to the localization where its g-value
is invertible. -/
def rootSection (a : R) (ha : P.f.eval a = 0) :
    B →ₐ[R] Localization.Away (P.g.eval a) := by
  let A := Localization.Away (P.g.eval a)
  have hmap : P.P.HasMap (algebraMap R A a) := by
    constructor
    · rw [aeval_algebraMap_apply]
      change algebraMap R A (P.f.eval a) = 0
      rw [ha, map_zero]
    · rw [aeval_algebraMap_apply]
      change IsUnit (algebraMap R A (P.g.eval a))
      exact IsLocalization.Away.algebraMap_isUnit (P.g.eval a)
  exact (P.P.lift _ hmap).comp P.equivRing.toAlgHom

omit [IsDomain R] in
@[simp]
theorem rootSection_x (a : R) (ha : P.f.eval a = 0) :
    rootSection P a ha P.x = algebraMap R (Localization.Away (P.g.eval a)) a := by
  simp [rootSection]

/-- Every field-valued point factors through one of the actual root sections. -/
theorem exists_rootSection_factor (hsplit : P.f.Splits)
    {L : Type u} [Field L] [Algebra R L] (φ : B →ₐ[R] L) :
    ∃ (a : R) (ha : P.f.eval a = 0)
      (ρ : Localization.Away (P.g.eval a) →ₐ[R] L),
      ρ.comp (rootSection P a ha) = φ := by
  obtain ⟨a, ha, he⟩ := exists_baseRoot_of_splits P hsplit φ
  have hunit : IsUnit (algebraMap R L (P.g.eval a)) := by
    have h := (P.hasMap.map φ).2
    rw [he, aeval_algebraMap_apply] at h
    exact h
  let ρ : Localization.Away (P.g.eval a) →ₐ[R] L :=
    IsLocalization.Away.liftAlgHom (P.g.eval a) (f := Algebra.ofId R L) hunit
  refine ⟨a, ha, ρ, P.hom_ext ?_⟩
  rw [AlgHom.comp_apply, rootSection_x]
  change IsLocalization.Away.lift (P.g.eval a) hunit
    (algebraMap R (Localization.Away (P.g.eval a)) a) = φ P.x
  rw [IsLocalization.Away.lift_eq]
  exact he.symm

/-- The actual scheme map of a root section. -/
def rootSectionMap (a : R) (ha : P.f.eval a = 0) :
    Spec (CommRingCat.of (Localization.Away (P.g.eval a))) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (rootSection P a ha).toRingHom)

omit [IsDomain R] in
/-- The root-section map is a section relative to the principal base open. -/
theorem rootSectionMap_comp_base (a : R) (ha : P.f.eval a = 0) :
    rootSectionMap P a ha ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (P.g.eval a)))) := by
  rw [rootSectionMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (rootSection P a ha).comp_algebraMap

omit [IsDomain R] in
/-- Root sections are actual open immersions. -/
theorem rootSectionMap_isOpenImmersion (a : R) (ha : P.f.eval a = 0) :
    IsOpenImmersion (rootSectionMap P a ha) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let v := rootSectionMap P a ha
  let : Algebra.IsStandardEtale R B := ⟨⟨P⟩⟩
  let : Etale f := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  have he : v ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (P.g.eval a)))) :=
    rootSectionMap_comp_base P a ha
  let : IsOpenImmersion (v ≫ f) := by rw [he]; infer_instance
  let : Mono v := mono_of_mono_fac he
  let : Etale v := Etale.of_comp v f
  exact IsOpenImmersion.of_flat_of_mono v

/-- A standard etale algebra with split monic presentation polynomial is an
actual Zariski local isomorphism over the base. -/
theorem isLocalIso_of_splits (hsplit : P.f.Splits) :
    IsLocalIso (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  change IsLocalIso f
  constructor
  intro x
  let L := (Spec (CommRingCat.of B)).residueField x
  let β : CommRingCat.of B ⟶ L :=
    Spec.preimage ((Spec (CommRingCat.of B)).fromSpecResidueField x)
  let : Algebra R L := (β.hom.comp (algebraMap R B)).toAlgebra
  let φ : B →ₐ[R] L := ⟨β.hom, fun r => rfl⟩
  obtain ⟨a, ha, ρ, hρ⟩ := exists_rootSection_factor P hsplit φ
  let v := rootSectionMap P a ha
  let w : Spec L ⟶ Spec (CommRingCat.of (Localization.Away (P.g.eval a))) :=
    Spec.map (CommRingCat.ofHom ρ.toRingHom)
  let : IsOpenImmersion v := rootSectionMap_isOpenImmersion P a ha
  have hfac : w ≫ v = (Spec (CommRingCat.of B)).fromSpecResidueField x := by
    dsimp only [w, v, rootSectionMap]
    rw [← Spec.map_comp]
    convert Spec.map_preimage ((Spec (CommRingCat.of B)).fromSpecResidueField x) using 1
    congr 1
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom hρ
  have hx : x ∈ v.opensRange := by
    refine ⟨w (IsLocalRing.closedPoint L), ?_⟩
    rw [← Scheme.Hom.comp_apply, hfac]
    exact Scheme.fromSpecResidueField_apply x _
  refine ⟨v.opensRange, hx, ?_⟩
  rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
  have he : v ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (P.g.eval a)))) :=
    rootSectionMap_comp_base P a ha
  rw [he]
  infer_instance

end SplitStandardEtale
end Langlands.AlgebraicGeometry
