import Langlands.Geometry.Building.TorusFiltration.RadicalStatement
import Langlands.Geometry.Building.TorusFiltration.ZeroPlusRadicalComparison
import Langlands.GroupScheme.Absolute.CentralizerProductClosedness

/-! # The zero-plus subgroup and the special-fibre radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 180000

namespace Langlands.Geometry.Building

section Models

set_option maxHeartbeats 1400000

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  [IsAffine T.X.left] (hT : IsTorus T.toGrp)

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "κ" => IsLocalRing.ResidueField O
local notation "M₀" => connectedNeronModel F T hT
local notation "P" => minimalCongruentPoints F T hT
local notation "StandardPlus" =>
  (⋃ r : Set.Ioi (0 : ℝ≥0), (localTorusFiltration F T hT r : Set (rationalPoints T.toGrp)))

private def radicalPreimage {U : GroupScheme (Spec (CommRingCat.of κ))}
    (i : U ⟶ (M₀).specialFibre) : Subgroup (rationalPoints T.toGrp) :=
  ((rationalPoints.map i).range.comap (M₀).reduction).map (M₀).integralPointMap

private theorem firstCongruence_le_radicalPreimage {U : GroupScheme (Spec (CommRingCat.of κ))}
    (i : U ⟶ (M₀).specialFibre) :
    (M₀).congruenceSubgroup ≤ radicalPreimage F T hT i := by
  rintro _ ⟨x, hx, rfl⟩
  have he := ((M₀).mem_congruenceKernel x).mp hx
  refine ⟨x, ?_, rfl⟩
  change (M₀).reduction x ∈ (rationalPoints.map i).range
  rw [he]
  exact Subgroup.one_mem _

private theorem minimalPlus_le_radicalPreimage {U : GroupScheme (Spec (CommRingCat.of κ))}
    (i : U ⟶ (M₀).specialFibre)
    (hPreimage : (radicalPreimage F T hT i : Set (rationalPoints T.toGrp)) =
      ((M₀).integralPoints : Set (rationalPoints T.toGrp)) ∩ StandardPlus) :
    minimalCongruentPlus F T hT 0 ⊆ radicalPreimage F T hT i := by
  intro t ht
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ht
  let r := min (s : ℝ≥0) (1 / 2)
  have hr : 0 < r := lt_min s.property (by norm_num)
  have hr₁ : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let q : Set.Iio (1 : ℝ≥0) := ⟨r, hr₁⟩
  have hq : t ∈ P q := minimalCongruentPoints_antitone F T hT (min_le_left _ _) hs
  rw [minimalCongruentPoints_of_lt_one, minimalCongruentShallowSubgroup, ite_eq_right hr.ne'] at hq
  have hStd : inducedTorusStandardImages F T r ≤ radicalPreimage F T hT i := by
    intro x hx
    have hxr : x ∈ localTorusFiltration F T hT r :=
      inducedImages_le_standard_at_positiveDepth F T hT hr hx
    change x ∈ (radicalPreimage F T hT i : Set (rationalPoints T.toGrp))
    rw [hPreimage, Set.mem_inter_iff, connectedNeronModel_integralPoints]
    exact ⟨localTorusFiltration_antitone F T hT zero_le hxr,
      Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hxr⟩⟩
  exact sup_le (firstCongruence_le_radicalPreimage F T hT i) hStd hq

private theorem radicalPreimage_le_minimalPlus {U : GroupScheme (Spec (CommRingCat.of κ))}
    (i : U ⟶ (M₀).specialFibre)
    (hLift : ∀ x : (M₀).integralSections, (M₀).reduction x ∈ (rationalPoints.map i).range →
      ∃ r : ℝ≥0, 0 < r ∧ r < 1 ∧ (M₀).integralPointMap x ∈ inducedTorusStandardImages F T r) :
    (radicalPreimage F T hT i : Set (rationalPoints T.toGrp)) ⊆ minimalCongruentPlus F T hT 0 := by
  rintro t ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hr₁, hx'⟩ := hLift x hx
  let q : Set.Iio (1 : ℝ≥0) := ⟨r, hr₁⟩
  refine Set.mem_iUnion.mpr ⟨⟨r, hr⟩, ?_⟩
  change (M₀).integralPointMap x ∈ P q
  rw [minimalCongruentPoints_of_lt_one, minimalCongruentShallowSubgroup, ite_eq_right hr.ne']
  exact (le_sup_right : inducedTorusStandardImages F T r ≤
    (M₀).congruenceSubgroup ⊔ inducedTorusStandardImages F T r) hx'

end Models

set_option maxHeartbeats 1400000 in
private theorem surjective_of_surjective_rationalPoints {k : Type u} [Field k] [IsAlgClosed k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom] (f : G ⟶ H)
    (hf : Function.Surjective (rationalPoints.map f)) : Surjective f.hom.hom.left := by
  let a := f.hom.hom.left
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  let : IsNoetherian G.X.left := ⟨⟩
  let : IsNoetherian H.X.left := ⟨⟩
  let : LocallyOfFiniteType (a ≫ H.X.hom) := by
    change LocallyOfFiniteType (f.hom.hom.left ≫ H.X.hom)
    rw [Over.w]
    infer_instance
  let : LocallyOfFiniteType a := locallyOfFiniteType_of_comp a H.X.hom
  let : JacobsonSpace H.X.left := LocallyOfFiniteType.jacobsonSpace H.X.hom
  have hc : IsConstructible (Set.range a) := by
    simpa only [Set.image_univ] using a.isConstructible_image (s := Set.univ) IsConstructible.univ
  refine ⟨fun y => ?_⟩
  by_contra hy
  have hyn : (Set.range a)ᶜ.Nonempty := ⟨y, hy⟩
  obtain ⟨z, hzn, hzc⟩ := CentralizerProduct.constructible_nonempty_inter_closedPoints hc.compl hyn
  let w : rationalPoints H := Over.homMk (pointOfClosedPoint H.X.hom z hzc)
    (pointOfClosedPoint_comp H.X.hom z hzc)
  obtain ⟨v, hv⟩ := hf w
  apply hzn
  refine ⟨v.left (IsLocalRing.closedPoint k), ?_⟩
  have hv' := congrArg (fun s : rationalPoints H => s.left (IsLocalRing.closedPoint k)) hv
  change a (v.left (IsLocalRing.closedPoint k)) = pointOfClosedPoint H.X.hom z hzc (IsLocalRing.closedPoint k) at hv'
  exact hv'.trans (pointOfClosedPoint_apply H.X.hom z hzc (IsLocalRing.closedPoint k))

section Dilatation

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  [IsAffine T.X.left] (hT : IsTorus T.toGrp)

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "κ" => IsLocalRing.ResidueField O
local notation "M₀" => connectedNeronModel F T hT

set_option maxHeartbeats 1900000 in
private theorem exists_radicalDilatation {U : GroupScheme (Spec (CommRingCat.of κ))}
    (i : U ⟶ (M₀).specialFibre) (hi : IsUnipotentRadical i) :
    ∃ (N : IntegralModel O K T.toGrp) (φ : N.Hom M₀ (𝟙 T.toGrp)), N.IsSmooth ∧
      N.integralPoints = (((rationalPoints.map i).range.comap (M₀).reduction).map (M₀).integralPointMap) ∧
        ∃ j : N.specialFibre ⟶ U, j ≫ i = φ.specialFibreMap ∧ Surjective j.hom.hom.left := by
  let : IsDiscreteValuationRing O := (fixedFieldIntegers_strictHenselian F).1
  let : HenselianLocalRing O := (fixedFieldIntegers_strictHenselian F).2.1
  let : IsAlgClosed κ := (fixedFieldResidueIsAlgClosure F).isAlgClosed
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : Smooth U.X.hom := hi.smooth
  let : IsAffineHom U.X.hom := by rw [← Over.w i.hom.hom]; infer_instance
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let N := (M₀).dilatation hπ i
  let φ := (M₀).dilatationHom hπ i
  have hM := connectedNeronModel_isSmooth F T hT
  have hN : N.IsSmooth := (IntegralModel.dilatationStructure.1 O K T.toGrp M₀ π hπ U i hM hi.smooth).1
  let : Smooth N.group.X.hom := hN
  let : IsReduced N.specialFibre.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field κ _ N.specialFibre.X.hom
  have hsections := (M₀).range_dilatationIntegralSections hπ i
  have hfac : (rationalPoints.map φ.specialFibreMap).range ≤ (rationalPoints.map i).range := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := N.reduction_surjective hN y
    rw [← φ.reduction_naturality]
    have hx : rationalPoints.map φ.hom x ∈ (rationalPoints.map φ.hom).range := ⟨x, rfl⟩
    exact hsections.le hx
  obtain ⟨j, hj⟩ := SubgroupFunctor.exists_factor_of_algClosed_points hi.isClosedSubgroup hfac
  refine ⟨N, φ, hN, (M₀).integralPoints_dilatation hπ i, j, hj, ?_⟩
  apply surjective_of_surjective_rationalPoints
  intro y
  obtain ⟨x, hx⟩ := (M₀).reduction_surjective hM (rationalPoints.map i y)
  have hxr : x ∈ (rationalPoints.map φ.hom).range := by
    apply hsections.ge
    exact ⟨y, hx.symm⟩
  obtain ⟨z, rfl⟩ := hxr
  refine ⟨N.reduction z, ?_⟩
  apply (cancel_mono i.hom.hom).mp
  change ((N.reduction z) ≫ j.hom.hom) ≫ i.hom.hom = _
  rw [Category.assoc, ← Grp.comp_hom_hom, hj]
  exact (φ.reduction_naturality z).symm.trans hx

end Dilatation

set_option maxHeartbeats 1900000 in
/-- The zero-plus term is the standard positive union inside the connected
Néron points and the inverse image of the special-fibre radical. -/
theorem minimalCongruentZeroPlus : MinimalCongruentZeroPlusStatement.{u} := by
  intro F _ _ _ _ T _ hT
  dsimp only
  obtain ⟨U, i, hi, hpre, hLift⟩ := exists_standardZeroPlus_radicalPreimage F T hT
  have hp := Set.Subset.antisymm (minimalPlus_le_radicalPreimage F T hT i hpre.symm)
    (radicalPreimage_le_minimalPlus F T hT i hLift)
  refine ⟨hp.trans hpre.symm, U, i, hi, hp, ?_⟩
  obtain ⟨N, φ, hN, hpts, j, hj, hsurj⟩ := exists_radicalDilatation F T hT i hi
  exact ⟨N, φ, hN, (congrArg SetLike.coe hpts).trans hp.symm, j, hj, hsurj⟩

end Langlands.Geometry.Building
