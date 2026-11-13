import Langlands.Geometry.Building.SmoothRootModelLifting

/-! # Reduction compatibility from deeper integral root models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [HenselianLocalRing R]
  {S : CommGroupScheme (Spec (CommRingCat.of K))}
  {G U : GroupScheme (Spec (CommRingCat.of K))}
  (i : S.toGrp ⟶ G) (a : characterLattice S) (j : U ⟶ G)
  (M : IntegralModel R K U) (φ : RootFunctionFamily S G)
  {Q : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
  (q : M.specialFibre ⟶ Q)

/-- An actual integral model mapping to the base root model, with the prescribed
depth filtration as its generic point image and trivial residue composite. -/
structure RootModelDepthComparison (r : ℝ) where
  genericGroup : GroupScheme (Spec (CommRingCat.of K))
  genericMap : genericGroup ⟶ U
  model : IntegralModel R K genericGroup
  toBase : model.Hom M genericMap
  integralPoints_image :
    (model.integralPoints.map (rationalPoints.map (genericMap ≫ j)) :
      Set (rationalPoints G)) = rootFiltration i φ a r
  residue_trivial : toBase.specialFibreMap.hom.hom ≫ q.hom.hom = 1

variable {i a j M φ q}

namespace RootModelDepthComparison

variable {r : ℝ} (C : RootModelDepthComparison i a j M φ q r)

/-- A base section whose generic point has the comparison depth comes from an
integral section of the deeper model. -/
theorem exists_section (hj : Mono j.hom.hom) (x : M.integralSections)
    (hx : rationalPoints.map j (M.integralPointMap x) ∈ rootFiltration i φ a r) :
    ∃ y : C.model.integralSections, rationalPoints.map C.toBase.hom y = x := by
  have hxImage :
      rationalPoints.map j (M.integralPointMap x) ∈
        (C.model.integralPoints.map (rationalPoints.map (C.genericMap ≫ j)) :
          Set (rationalPoints G)) := by
    rw [C.integralPoints_image]
    exact hx
  obtain ⟨g, ⟨y, rfl⟩, hy⟩ := hxImage
  refine ⟨y, M.integralPointMap_injective ?_⟩
  have : Mono j.hom.hom := hj
  apply (cancel_mono j.hom.hom).mp
  change rationalPoints.map j
      (M.integralPointMap (rationalPoints.map C.toBase.hom y)) =
    rationalPoints.map j (M.integralPointMap x)
  rw [C.toBase.integralPointMap_naturality]
  simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using hy

include C in
/-- The special-fibre quotient kills every base section whose generic point
belongs to the comparison depth. -/
theorem quotientReduction_eq_one (hj : Mono j.hom.hom) (x : M.integralSections)
    (hx : rationalPoints.map j (M.integralPointMap x) ∈ rootFiltration i φ a r) :
    rationalPoints.map q (M.reduction x) = 1 := by
  obtain ⟨y, hy⟩ := C.exists_section hj x hx
  rw [← hy, C.toBase.reduction_naturality]
  change (C.model.reduction y ≫ C.toBase.specialFibreMap.hom.hom) ≫ q.hom.hom = 1
  rw [Category.assoc, C.residue_trivial, MonObj.comp_one]

end RootModelDepthComparison

variable (i a j M φ q)

/-- Actual depth comparisons at a cofinal collection of strictly positive
depths. No existence of these models is asserted by this definition. -/
def HasCofinalRootModelDepthComparisons : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧
    Nonempty (RootModelDepthComparison i a j M φ q r)

variable {i a j M φ q}

/-- Exact depth-zero points and cofinal positive-depth comparisons imply the
value and reduction conditions used by smooth root-model lifting. -/
theorem rootModelReductionCompatible_of_depthComparisons
    (hj : (RelativeRoot.subgroup i a).IsRepresentedBy j)
    (hzero : (M.integralPoints.map (rationalPoints.map j) : Set (rationalPoints G)) =
      rootFiltration i φ a 0)
    (hdepth : HasCofinalRootModelDepthComparisons i a j M φ q) :
    RootModelReductionCompatible a j M φ q := by
  have hbase (x : M.integralSections) :
      rationalPoints.map j (M.integralPointMap x) ∈ rootFiltration i φ a 0 := by
    rw [← hzero]
    exact ⟨M.integralPointMap x, ⟨x, rfl⟩, rfl⟩
  constructor
  · intro x
    simpa only [WithTop.coe_zero] using (hbase x).2
  · intro x hpos
    obtain ⟨ε, hε, hεφ⟩ := WithTop.lt_iff_exists_coe_btwn.mp hpos
    have hεpos : 0 < ε := WithTop.coe_lt_coe.mp
      (show ((0 : ℝ) : WithTop ℝ) < (ε : WithTop ℝ) from hε)
    obtain ⟨r, _, hrε, ⟨C⟩⟩ := hdepth ε hεpos
    exact C.quotientReduction_eq_one hj.1 x
      ⟨(hbase x).1, (WithTop.coe_le_coe.mpr hrε).trans hεφ.le⟩

end Langlands.Geometry.Building
