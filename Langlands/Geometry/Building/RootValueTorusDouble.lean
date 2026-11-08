import Langlands.Geometry.Building.RootValueTorusRestriction
import Langlands.Geometry.Building.SelectedRootDepthIntersection

/-! # Doubling for the actual torus-restricted valuation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
    {φ : RootFunctionFamily T G}

/-- Doubling both the lower character and depth leaves the auxiliary additive
upper depth unchanged. -/
theorem torusRestrictionDepth_double
    (f : S ⟶ T) (α : characterLattice S) (ν : cocharacterLattice S)
    (hν : latticePairing S α ν ≠ 0) (r : ℝ) :
    torusRestrictionDepth f (2 • α) ν (2 * r) =
      torusRestrictionDepth f α ν r := by
  ext χ
  simp only [torusRestrictionDepth_apply, two_nsmul, map_add,
    LinearMap.add_apply, Int.cast_add]
  have hd : (latticePairing S α ν : ℝ) ≠ 0 := by exact_mod_cast hν
  field_simp
  ring

variable [Smooth G.X.hom]

/-- The doubled restricted depth subgroup is exactly the original depth
subgroup intersected with the actual doubled root group. -/
theorem torusRestrictedRootDepthSubgroup_double_eq
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S) (hα : α ≠ 0) (r : ℝ) :
    torusRestrictedRootDepthSubgroup hφ f (2 • α) (2 * r) =
      torusRestrictedRootDepthSubgroup hφ f α r ⊓
        rootGroupPoints (CommGroupScheme.groupHom f ≫ i) (2 • α) := by
  obtain ⟨D, hD, ν, hν⟩ := hS.exists_pairing_eq_pos hα
  have hνpos : 0 < latticePairing S α ν := by rw [hν]; exact_mod_cast hD
  have h2ν : latticePairing S (2 • α) ν ≠ 0 := by
    rw [two_nsmul, map_add, LinearMap.add_apply]
    omega
  have h2α : 2 • α ≠ 0 := hS.nsmul_ne_zero hα (by omega)
  let A := RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail α 1)
  let B := RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail (2 • α) 1)
  have hBA : B ≤ A := by
    rintro χ ⟨m, hm, hm0, heq⟩
    exact ⟨m * 2, by omega, by omega, by rw [mul_comm, mul_nsmul]; exact heq⟩
  rw [torusRestrictedRootDepthSubgroup_eq_selectedRootDepthSubgroup hφ f
      (2 • α) ν h2ν (2 * r),
    torusRestrictionDepth_double f α ν (ne_of_gt hνpos) r,
    torusRestrictedRootDepthSubgroup_eq_selectedRootDepthSubgroup hφ f α ν
      (ne_of_gt hνpos) r]
  change _ = _ ⊓ (RelativeRoot.subgroup (CommGroupScheme.groupHom f ≫ i)
    (2 • α)).carrier (Over.mk (𝟙 _))
  rw [RelativeRoot.subgroup_comp_torusHom_eq_semigroupSubgroup hS hT f i
    (2 • α) h2α]
  exact (selectedRootDepthSubgroup_inf_semigroup_eq hT hE hφ A B
    (RelativeRoot.zero_notMem_characterSemigroupPreimage_cyclicTail hS f α hα)
    hBA (ν ≫ f)
    (fun χ _ hχ => latticePairing_pos_of_mem_torusRestriction f α ν hνpos hχ)
    (torusRestrictionDepth f α ν r)).symm

/-- The doubled depth identification preserves the original rational point. -/
def torusRestrictedRootDepthDoublePointsEquiv
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S) (hα : α ≠ 0) (r : ℝ) :
    ↥(torusRestrictedRootDepthSubgroup hφ f (2 • α) (2 * r)) ≃*
      ↥(torusRestrictedRootDepthSubgroup hφ f α r ⊓
        rootGroupPoints (CommGroupScheme.groupHom f ≫ i) (2 • α) :
          Subgroup (rationalPoints G)) :=
  MulEquiv.subgroupCongr
    (torusRestrictedRootDepthSubgroup_double_eq hS hT hE hφ f α hα r)

@[simp] theorem torusRestrictedRootDepthDoublePointsEquiv_val
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S) (hα : α ≠ 0) (r : ℝ)
    (x : ↥(torusRestrictedRootDepthSubgroup hφ f (2 • α) (2 * r))) :
    (torusRestrictedRootDepthDoublePointsEquiv hS hT hE hφ f α hα r x).val =
      x.val := rfl

/-- The actual restricted scalar family satisfies precisely the original
valuation axiom V4 on every actual doubled root group. -/
theorem torusRestrictedRootFunctionFamily_double
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S)
    (hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i))
    (h2α : 2 • α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i))
    (g : rationalPoints G)
    (hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) (2 • α)) :
    torusRestrictedRootFunctionFamily hS hT hE hφ f (2 • α) g =
      2 • torusRestrictedRootFunctionFamily hS hT hE hφ f α g := by
  have hga : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α :=
    RelativeRoot.double_subgroup_le (CommGroupScheme.groupHom f ≫ i) α
      (Over.mk (𝟙 _)) hg
  have hbound (r : ℝ) :
      ((2 * r : ℝ) : WithTop ℝ) ≤
          torusRestrictedRootFunctionFamily hS hT hE hφ f (2 • α) g ↔
        (r : WithTop ℝ) ≤ torusRestrictedRootFunctionFamily hS hT hE hφ f α g := by
    rw [le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f (2 • α) h2α g hg,
      torusRestrictedRootDepthSubgroup_double_eq hS hT hE hφ f α hα.1,
      le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f α hα g hga]
    exact and_iff_left hg
  by_cases hg1 : g = 1
  · subst g
    simp only [torusRestrictedRootFunctionFamily_one, two_nsmul, WithTop.top_add]
  have haTop : torusRestrictedRootFunctionFamily hS hT hE hφ f α g ≠ ⊤ := by
    exact fun h => hg1 ((torusRestrictedRootFunctionFamily_eq_top_iff
      hS hT hE hφ f α hα g hga).mp h)
  have h2Top : torusRestrictedRootFunctionFamily hS hT hE hφ f (2 • α) g ≠ ⊤ := by
    exact fun h => hg1 ((torusRestrictedRootFunctionFamily_eq_top_iff
      hS hT hE hφ f (2 • α) h2α g hg).mp h)
  induction haVal : torusRestrictedRootFunctionFamily hS hT hE hφ f α g
      using WithTop.recTopCoe with
  | top => exact (haTop haVal).elim
  | coe t =>
    induction h2Val : torusRestrictedRootFunctionFamily hS hT hE hφ f (2 • α) g
        using WithTop.recTopCoe with
    | top => exact (h2Top h2Val).elim
    | coe s =>
      rw [two_nsmul, ← WithTop.coe_add]
      apply congrArg (fun x : ℝ => (x : WithTop ℝ))
      have hlo := (hbound t).mpr (by rw [haVal])
      have hhi := (hbound (s / 2)).mp (by
        rw [h2Val, WithTop.coe_le_coe]
        linarith)
      rw [h2Val, WithTop.coe_le_coe] at hlo
      rw [haVal, WithTop.coe_le_coe] at hhi
      linarith

end Langlands.Geometry.Building
