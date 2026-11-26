import Langlands.Geometry.Building.TorusFiltration.Points
import Langlands.GroupScheme.Absolute.BorelExistenceCoordinates
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.IntegralModel.ConnectedGenerationFieldGeneration
import Langlands.GroupScheme.IntegralModel.HenselianReduction

/-! # Integral models of the minimal congruent torus subgroups -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal ValuativeRel

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

set_option maxHeartbeats 800000 in
private theorem exists_closedGeneratedImage
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {I : Type v} {A : I → GroupScheme (Spec (CommRingCat.of k))}
    (a : ∀ j, A j ⟶ G)
    (hA : ∀ j, Smooth (A j).X.hom ∧ IsAffineHom (A j).X.hom ∧
      ConnectedSpace (A j).X.left) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
      Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧ IsClosedSubgroup i ∧
        (rationalPoints.map i).range = ⨆ j, (rationalPoints.map (a j)).range := by
  classical
  choose H i hsmooth haffine hconn hclosed hpoints using
    ConnectedGenerationField.exists_generated_subfamily_points a hA
  let height (s : Finset I) := (BorelExistence.coordinateKernel (i s)).height.toNat
  let HasHeight (n : ℕ) := ∃ s, height s = n
  have hex : ∃ n, HasHeight n := ⟨height ∅, ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  let : Smooth (H s).X.hom := hsmooth s
  let : ConnectedSpace (H s).X.left := hconn s
  let : IsLocallyNoetherian (H s).X.left := LocallyOfFiniteType.isLocallyNoetherian (H s).X.hom
  let : IsIntegral (H s).X.left :=
    CharacterLatticeProof.isIntegral_of_smooth k (H s).X.hom
  refine ⟨H s, i s, hsmooth s, hconn s, hclosed s, le_antisymm ?_ ?_⟩
  · rw [hpoints s]
    exact iSup_le fun j => iSup_le fun _ => le_iSup (fun j =>
      (rationalPoints.map (a j)).range) j
  · apply iSup_le
    intro j
    let t := insert j s
    let : Smooth (H t).X.hom := hsmooth t
    let : ConnectedSpace (H t).X.left := hconn t
    have hnst : (rationalPoints.map (i s)).range ≤ (rationalPoints.map (i t)).range := by
      rw [hpoints, hpoints]
      refine iSup_le fun l => iSup_le fun hl => ?_
      exact le_iSup_of_le l (le_iSup_of_le (Finset.mem_insert_of_mem hl) le_rfl)
    obtain ⟨b, hb⟩ := SubgroupFunctor.exists_factor_of_algClosed_points
      (i := i s) (j := i t) (hclosed t) hnst
    have hheight : (BorelExistence.coordinateKernel (i s)).height ≤
        (BorelExistence.coordinateKernel (i t)).height := by
      have hnat : height s ≤ height t :=
        hs.trans_le (Nat.find_min' hex (show HasHeight (height t) from ⟨t, rfl⟩))
      rw [← ENat.natCast_toNat (BorelExistence.coordinateKernel_height_ne_top (i s)),
        ← ENat.natCast_toNat (BorelExistence.coordinateKernel_height_ne_top (i t))]
      exact_mod_cast hnat
    let : IsIso b := BorelExistence.isIso_of_coordinateKernel_height_le
      _ _ b (hclosed s) (hclosed t) hb hheight
    have hi : inv b ≫ i s = i t := by rw [← hb, IsIso.inv_hom_id_assoc]
    have hj : (rationalPoints.map (a j)).range ≤ (rationalPoints.map (i t)).range := by
      rw [hpoints]
      exact le_iSup_of_le j (le_iSup_of_le (Finset.mem_insert_self _ _) le_rfl)
    intro x hx
    obtain ⟨y, rfl⟩ := hj hx
    refine ⟨rationalPoints.map (inv b) y, ?_⟩
    change (y ≫ (inv b).hom.hom) ≫ (i s).hom.hom = y ≫ (i t).hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hi]

section Shallow

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  [IsAffine T.X.left] (hT : IsTorus T.toGrp)
  (q : Set.Iio (1 : ℝ≥0)) (hq : 0 < (q : ℝ≥0))

local notation "K" => inertiaFixedField F
local notation "O" => fixedFieldIntegers F
local notation "κ" => IsLocalRing.ResidueField (fixedFieldIntegers F)
local notation "M" => connectedNeronModel F T hT

variable (hStd : ∀ (S : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))),
  IsInducedTorus S →
    ∃ N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) S.toGrp,
      N.IsSmooth ∧ N.HasGeometricallyConnectedFibres ∧
        N.integralPoints = localGeometricCharacterCongruence F S q)

include hStd hq in
set_option maxHeartbeats 2200000 in
private theorem exists_shallowReductionCentre :
    ∃ (H : GroupScheme (Spec (CommRingCat.of κ))) (i : H ⟶ (M).specialFibre),
      IsClosedSubgroup i ∧ Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧
        minimalCongruentShallowSubgroup F T hT q =
          (((rationalPoints.map i).range.comap (M).reduction).map (M).integralPointMap) := by
  classical
  let I := Σ S : {S : CommGroupScheme (Spec (CommRingCat.of K)) // IsInducedTorus S}, S.val ⟶ T
  let N (j : I) := (hStd j.1.val j.1.property).choose
  have hN (j : I) : (N j).IsSmooth ∧ (N j).HasGeometricallyConnectedFibres ∧
      (N j).integralPoints = localGeometricCharacterCongruence F j.1.val q :=
    (hStd j.1.val j.1.property).choose_spec
  have hmap (j : I) : (N j).integralPoints.map
      (rationalPoints.map (CommGroupScheme.groupHom j.2)) ≤ (M).integralPoints := by
    rw [(hN j).2.2]
    have hgen : (localGeometricCharacterCongruence F j.1.val q).map
        (rationalPoints.map (CommGroupScheme.groupHom j.2)) ≤ inducedTorusStandardImages F T q :=
      le_iSup_of_le j.1.val (le_iSup_of_le j.1.property (le_iSup_of_le j.2 le_rfl))
    refine hgen.trans (le_trans ?_ (minimalCongruentShallowSubgroup_le_integralPoints F T hT q))
    rw [minimalCongruentShallowSubgroup, ite_eq_right hq.ne']
    exact le_sup_right
  have hφ (j : I) : Nonempty ((N j).Hom M (CommGroupScheme.groupHom j.2)) :=
    exists_hom_of_map_integralPoints_le IntegralModel.smoothHomExtension F
      (hN j).1 rfl (hmap j)
  let φ (j : I) := (hφ j).some
  let U : Subgroup (M).integralSections :=
    (M).congruenceKernel ⊔ ⨆ j : I, (rationalPoints.map (φ j).hom).range
  have hUmap : U.map (M).integralPointMap = minimalCongruentShallowSubgroup F T hT q := by
    have himages (j : I) :
        (rationalPoints.map (φ j).hom).range.map (M).integralPointMap =
          (localGeometricCharacterCongruence F j.1.val q).map
            (rationalPoints.map (CommGroupScheme.groupHom j.2)) := by
      rw [← (hN j).2.2, MonoidHom.map_range, IntegralModel.integralPoints, MonoidHom.map_range]
      congr 1
      exact MonoidHom.ext (φ j).integralPointMap_naturality
    simp only [U, Subgroup.map_sup, Subgroup.map_iSup, himages,
      IntegralModel.congruenceSubgroup, minimalCongruentShallowSubgroup, ite_eq_right hq.ne']
    rw [inducedTorusStandardImages, iSup_sigma, iSup_subtype]
  obtain ⟨_, hHenselian, _⟩ := fixedFieldIntegers_strictHenselian F
  let : HenselianLocalRing O := hHenselian
  have hUred : U.map (M).reduction =
      ⨆ j : I, (rationalPoints.map (φ j).specialFibreMap).range := by
    have hred (j : I) :
        (rationalPoints.map (φ j).hom).range.map (M).reduction =
          (rationalPoints.map (φ j).specialFibreMap).range := by
      ext g
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨(N j).reduction x, ((φ j).reduction_naturality x).symm⟩
      · rintro ⟨y, rfl⟩
        obtain ⟨x, rfl⟩ := (N j).reduction_surjective (hN j).1 y
        exact ⟨_, ⟨x, rfl⟩, (φ j).reduction_naturality x⟩
    simp only [U, Subgroup.map_sup, Subgroup.map_iSup, hred, IntegralModel.congruenceKernel,
      Subgroup.map_ker_self, bot_sup_eq]
  let : IsAlgClosed κ := (fixedFieldResidueIsAlgClosure F).isAlgClosed
  let : Smooth (M).group.X.hom := connectedNeronModel_isSmooth F T hT
  have hspecial (j : I) :
      Smooth (N j).specialFibre.X.hom ∧ IsAffineHom (N j).specialFibre.X.hom ∧
        ConnectedSpace (N j).specialFibre.X.left := by
    let : Smooth (N j).group.X.hom := (hN j).1
    exact ⟨inferInstance, inferInstance,
      (N j).hasConnectedSpecialFibre_of_geometricallyConnected
        ((N j).hasGeometricallyConnectedSpecialFibre_of_geometricallyConnected (hN j).2.1)⟩
  obtain ⟨H, i, hsm, hcon, hi, hrange⟩ :=
    exists_closedGeneratedImage (fun j : I => (φ j).specialFibreMap) hspecial
  refine ⟨H, i, hi, hsm, hcon, ?_⟩
  rw [← hUmap, hrange, ← hUred, Subgroup.comap_map_eq_self]
  exact le_sup_left

end Shallow

section AllDepths

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  [IsAffine T.X.left] (hT : IsTorus T.toGrp)

local notation "K" => inertiaFixedField F
local notation "O" => fixedFieldIntegers F
local notation "κ" => IsLocalRing.ResidueField (fixedFieldIntegers F)
local notation "Model" => IntegralModel O K T.toGrp
local notation "M₀" => connectedNeronModel F T hT

set_option maxHeartbeats 1600000 in
/-- Construct the smooth model by dilating the actual closed subgroup
generated in the special fibre, then taking the required congruence model.
The input operations are the standard models for induced tori, smooth
dilatation in the connected Néron model, and formation of congruence models. -/
def minimalCongruentModelFromDilatation
    (hStd : ∀ (S : CommGroupScheme (Spec (CommRingCat.of K))), IsInducedTorus S →
      ∀ (q : Set.Iio (1 : ℝ≥0)), 0 < (q : ℝ≥0) →
        ∃ N : IntegralModel O K S.toGrp, N.IsSmooth ∧ N.HasGeometricallyConnectedFibres ∧
          N.integralPoints = localGeometricCharacterCongruence F S q)
    (hDil : ∀ (H : GroupScheme (Spec (CommRingCat.of κ))) (i : H ⟶ (M₀).specialFibre),
      IsClosedSubgroup i → Smooth H.X.hom → ConnectedSpace H.X.left →
        ∃ N : Model, N.IsSmooth ∧ N.HasGeometricallyConnectedFibres ∧
          N.integralPoints =
            (((rationalPoints.map i).range.comap (M₀).reduction).map (M₀).integralPointMap))
    (hLevel : ∀ (N : Model) (n : ℕ+), N.IsSmooth → N.HasGeometricallyConnectedFibres →
      ∃ P : Model, P.IsSmooth ∧ P.HasGeometricallyConnectedFibres ∧
        P.integralPoints = N.congruenceSubgroupAt n)
    (r : ℝ≥0) :
    { N : Model // N.IsSmooth ∧ N.HasGeometricallyConnectedFibres ∧
      N.integralPoints = minimalCongruentPoints F T hT r } := by
  let q : Set.Iio (1 : ℝ≥0) := ⟨r - (⌊r⌋₊ : ℝ≥0), Set.mem_Iio.mpr
    ((tsub_lt_iff_right (Nat.floor_le (show 0 ≤ r from zero_le))).mpr
      (by simpa only [add_comm] using Nat.lt_floor_add_one r))⟩
  have hr : (q : ℝ≥0) + (⌊r⌋₊ : ℝ≥0) = r := tsub_add_cancel_of_le (Nat.floor_le zero_le)
  let B : { N : Model // N.IsSmooth ∧ N.HasGeometricallyConnectedFibres ∧
      N.integralPoints = minimalCongruentShallowSubgroup F T hT q } := by
    by_cases hq : (q : ℝ≥0) = 0
    · exact ⟨M₀, connectedNeronModel_isSmooth F T hT,
        connectedNeronModel_hasGeometricallyConnectedFibres F T hT,
        by simp only [minimalCongruentShallowSubgroup, ite_eq_left hq]⟩
    · have hq' : 0 < (q : ℝ≥0) := pos_of_ne_zero hq
      have hEx : ∃ N : Model, N.IsSmooth ∧ N.HasGeometricallyConnectedFibres ∧
          N.integralPoints = minimalCongruentShallowSubgroup F T hT q := by
        obtain ⟨H, i, hclosed, hsm, hcon, hP⟩ :=
          exists_shallowReductionCentre F T hT q hq' (fun S hS => hStd S hS q hq')
        obtain ⟨N, hN, hNc, hNp⟩ := hDil H i hclosed hsm hcon
        exact ⟨N, hN, hNc, hNp.trans hP.symm⟩
      exact ⟨hEx.choose, hEx.choose_spec⟩
  cases hn : ⌊r⌋₊ with
  | zero =>
    have hqr : (q : ℝ≥0) = r := by simpa only [hn, Nat.cast_zero, add_zero] using hr
    refine ⟨B.val, B.property.1, B.property.2.1, ?_⟩
    rw [← hqr, minimalCongruentPoints_of_lt_one]
    exact B.property.2.2
  | succ k =>
    let n := Nat.succPNat k
    let h := hLevel B.val n B.property.1 B.property.2.1
    have hr' : (q : ℝ≥0) + ((n : ℕ) : ℝ≥0) = r := by
      simpa only [hn, n, Nat.succPNat_coe] using hr
    refine ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2.trans ?_⟩
    rw [← hr']
    exact (minimalCongruentPoints_add_pnat F T hT q n B.val B.property.1 B.property.2.2).symm

/-- The subgroup generated by the terms at strictly greater depths. -/
def minimalCongruentPlusSubgroup (r : ℝ≥0) : Subgroup (rationalPoints T.toGrp) :=
  ⨆ s : Set.Ioi r, minimalCongruentPoints F T hT s

/-- For a decreasing filtration this subgroup consists exactly of the union
of the terms at strictly greater depths. -/
theorem coe_minimalCongruentPlusSubgroup
    (h : Antitone (minimalCongruentPoints F T hT)) (r : ℝ≥0) :
    (minimalCongruentPlusSubgroup F T hT r : Set (rationalPoints T.toGrp)) =
      minimalCongruentPlus F T hT r :=
  (minimalCongruentPlus_eq_coe_iSup F T hT h r).symm

end AllDepths

end Langlands.Geometry.Building
