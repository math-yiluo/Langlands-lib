import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsOpenProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsCompactProof
import Langlands.Global.AdelicSpaceLevelTopology

/-!
# Integral points of algebraic spaces over a general base

Corollary 5.7 of Conrad is stated for algebraic spaces over the valuation ring `O` itself.
For an algebraic space `X` over `Spec C` and a `C`-algebra structure on `O ⊆ K`, the map
`X(O) → X_K(K)` of `fieldValuedPointMap` is the corresponding map for the base change of `X`
to `O`, up to the homeomorphism of iterated base change. Its image is therefore open, and
quasi-compact when `K` is locally compact and `X` is of finite type. For separated `X`,
change of coefficients along an injective algebra map is injective on points.
-/

noncomputable section

universe u

open CategoryTheory Opposite Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace RelativeIntegralPoints

variable {C : Type u} [CommRing C] {X : AlgebraicSpace (Spec (CommRingCat.of C))}

/-- **Injectivity.** For a separated space, change of coefficients along an injective algebra
map is injective: the equalizer of two points is a closed subscheme of `Spec A` through which
`Spec B → Spec A` factors, and an injective ring map has no kernel. -/
theorem changeRing_injective (hX : IsSeparated X) {A B : Type u} [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] (φ : A →ₐ[C] B) (hφ : Function.Injective φ) :
    Function.Injective (RingPoints.changeRing (X := X) φ) := by
  intro p q hpq
  obtain ⟨Z, j, hj, hcl⟩ :=
    exists_representsEqualizer_of_relative_diag
      (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u}) hX (U := ringTest C A) p q
  obtain ⟨z, hz⟩ : ∃ z : ringTest C B ⟶ Z, z ≫ j = ringTestMap C φ :=
    (hj (ringTestMap C φ)).2 hpq
  have : _root_.AlgebraicGeometry.IsClosedImmersion j.left := hcl
  have : IsAffine (ringTest C A).left := inferInstanceAs (IsAffine (Spec _))
  have hcomp : z.left ≫ j.left = Spec.map (CommRingCat.ofHom φ.toRingHom) :=
    congrArg CommaMorphism.left hz
  have hSpec : Function.Injective (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop := by
    have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom)
    have h2 : Function.Injective
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ.toRingHom) := by
      intro a b hab
      apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
      apply hφ
      exact hab
    rw [← hn] at h2
    intro a b hab
    apply h2
    change (Scheme.ΓSpecIso _).hom ((Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop a) =
      (Scheme.ΓSpecIso _).hom ((Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop b)
    rw [hab]
  have hinj : Function.Injective j.left.appTop := by
    intro a b hab
    apply hSpec
    have e : (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop =
        j.left.appTop ≫ z.left.appTop := by
      rw [← Scheme.Hom.comp_appTop, hcomp]
      rfl
    rw [e]
    change z.left.appTop (j.left.appTop a) = z.left.appTop (j.left.appTop b)
    rw [hab]
  have : IsIso j.left :=
    _root_.AlgebraicGeometry.IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  let s : ringTest C A ⟶ Z := Over.homMk (inv j.left) (by
    rw [IsIso.inv_comp_eq, ← Over.w j])
  have hs : s ≫ j = 𝟙 _ := by
    ext1
    simp [s]
  have h := (hj (𝟙 _)).1 ⟨s, hs⟩
  rw [op_id, X.presheaf.map_id] at h
  exact h

section Valued

variable {K : Type u} [NontriviallyNormedField K] [Algebra C K] (O : Subring K) [Algebra C O]
  [IsScalarTower C O K]

variable (X) in
/-- The map `X(O) → X_K(K)` for the base change of `X` to `O`. -/
def integralPointMap :
    RingPoints O (baseChange (Spec.algebraMap C O) X) O →
      RingPoints K (baseChange (Spec.algebraMap O K)
        (baseChange (Spec.algebraMap C O) X)) K :=
  fun x => (baseChangeRingPointsEquiv O K K _).symm (RingPoints.changeRing (Algebra.ofId O K) x)

/-- Iterated base change identifies the two maps `X(O) → X_K(K)`. -/
theorem towerIso_integralPointMap
    (y : RingPoints O (baseChange (Spec.algebraMap C O) X) O) :
    RingPoints.map (towerIso C O K X).hom (integralPointMap X O y) =
      fieldValuedPointMap C X (IsScalarTower.toAlgHom C O K)
        (baseChangeRingPointsEquiv C O O X y) := by
  apply (baseChangeRingPointsEquiv C K K X).injective
  rw [fieldValuedPointMap, Equiv.apply_symm_apply, baseChangeRingPointsEquiv_towerIso,
    integralPointMap, Equiv.apply_symm_apply, baseChangeRingPointsEquiv_changeRing]
  rfl

theorem range_fieldValuedPointMap :
    Set.range (fieldValuedPointMap C X (IsScalarTower.toAlgHom C O K)) =
      RingPoints.map (towerIso C O K X).hom '' Set.range (integralPointMap X O) := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨integralPointMap X O ((baseChangeRingPointsEquiv C O O X).symm x), ⟨_, rfl⟩, ?_⟩
    rw [towerIso_integralPointMap, Equiv.apply_symm_apply]
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨_, (towerIso_integralPointMap O y).symm⟩

/-- **Corollary 5.7, openness, over a general base.** -/
theorem isOpen_range_fieldValuedPointMap (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)
    (hhen : HenselianLocalRing O) (hX : IsQuasiSeparated X)
    (hlft : LocallyOfFiniteTypeOverBase X) :
    IsOpen[etaleChartTopology K (baseChange (Spec.algebraMap C K) X)]
      (Set.range (fieldValuedPointMap C X (IsScalarTower.toAlgHom C O K))) := by
  rw [range_fieldValuedPointMap]
  exact @IsHomeomorph.isOpenMap _ _ (etaleChartTopology K _) (etaleChartTopology K _) _
    (isHomeomorph_ringPointsMap_of_iso (towerIso C O K X)) _
    (henselianIntegralPointsOpen K O hO hhen _ hX.baseChange hlft.baseChange)

/-- **Corollary 5.7, quasi-compactness, over a general base.** -/
theorem isCompact_range_fieldValuedPointMap (hO : ∀ x : K, x ∈ O ↔ ‖x‖ ≤ 1)
    (hhen : HenselianLocalRing O) [LocallyCompactSpace K] (hX : IsQuasiSeparated X)
    (hft : FiniteTypeOverRing C X) :
    @IsCompact _ (etaleChartTopology K (baseChange (Spec.algebraMap C K) X))
      (Set.range (fieldValuedPointMap C X (IsScalarTower.toAlgHom C O K))) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType.{u} ⊓ @QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  rw [range_fieldValuedPointMap]
  exact @IsCompact.image _ _ (etaleChartTopology K _) (etaleChartTopology K _) _ _
    (henselianIntegralPointsCompact K O hO hhen inferInstance _ hX.baseChange hft.baseChange)
    (@IsHomeomorph.continuous _ _ (etaleChartTopology K _) (etaleChartTopology K _) _
      (isHomeomorph_ringPointsMap_of_iso (towerIso C O K X)))

end Valued

end RelativeIntegralPoints

end Langlands.AlgebraicGeometry.AlgebraicSpace
