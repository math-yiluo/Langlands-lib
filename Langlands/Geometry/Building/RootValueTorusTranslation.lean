import Langlands.Geometry.Building.RootValueTorusRestriction
import Langlands.Geometry.Building.CentralIsogenyTranslation

/-! # Translations of actual torus-restricted root functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

private theorem coe_le_add_real_iff (q : WithTop ℝ) (r c : ℝ) :
    (r : WithTop ℝ) ≤ q + (c : WithTop ℝ) ↔
      ((r - c : ℝ) : WithTop ℝ) ≤ q := by
  induction q using WithTop.recTopCoe with
  | top => simp
  | coe q =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  {φ : RootFunctionFamily T G}

/-- Translation by an actual lower-torus vector shifts the entire canonical
restricted filtration by the evaluation of its lower character. -/
theorem torusRestrictedRootDepthSubgroup_vadd
    (hφ : IsRootDatumValuation i φ) (f : S ⟶ T)
    (v : V S) (α : characterLattice S) (r : ℝ) :
    torusRestrictedRootDepthSubgroup (hφ.vadd (cocharacterMapReal f v)) f α r =
      torusRestrictedRootDepthSubgroup hφ f α (r - eval S α v) := by
  unfold torusRestrictedRootDepthSubgroup
  congr 1
  funext χ
  congr 1
  funext hχ
  congr 1
  funext m
  congr 1
  funext hm
  congr 1
  funext hχf
  apply Subgroup.ext
  intro g
  change (g ∈ rootGroupPoints i χ ∧
      ((m * r : ℝ) : WithTop ℝ) ≤
        φ χ g + ((eval T χ (cocharacterMapReal f v) : ℝ) : WithTop ℝ)) ↔
    (g ∈ rootGroupPoints i χ ∧
      ((m * (r - eval S α v) : ℝ) : WithTop ℝ) ≤ φ χ g)
  have hr : (m : ℝ) * r - m * eval S α v =
      m * (r - eval S α v) := by ring
  rw [eval_cocharacterMapReal, hχf, eval_nsmul_char,
    coe_le_add_real_iff, hr]

/-- The translation comparison preserves the original ambient rational point. -/
def torusRestrictedRootDepthTranslationPointsEquiv
    (hφ : IsRootDatumValuation i φ) (f : S ⟶ T)
    (v : V S) (α : characterLattice S) (r : ℝ) :
    ↥(torusRestrictedRootDepthSubgroup (hφ.vadd (cocharacterMapReal f v)) f α r) ≃*
      ↥(torusRestrictedRootDepthSubgroup hφ f α (r - eval S α v)) :=
  MulEquiv.subgroupCongr (torusRestrictedRootDepthSubgroup_vadd hφ f v α r)

@[simp] theorem torusRestrictedRootDepthTranslationPointsEquiv_val
    (hφ : IsRootDatumValuation i φ) (f : S ⟶ T)
    (v : V S) (α : characterLattice S) (r : ℝ)
    (g : ↥(torusRestrictedRootDepthSubgroup
      (hφ.vadd (cocharacterMapReal f v)) f α r)) :
    (torusRestrictedRootDepthTranslationPointsEquiv
      (i := i) (φ := φ) hφ f v α r g).val = g.val := by
  exact MulEquiv.subgroupCongr_apply
    (torusRestrictedRootDepthSubgroup_vadd hφ f v α r) g

variable [Smooth G.X.hom]

/-- The constructed scalar restriction commutes with every translation
coming from the actual lower torus, on all characters and ambient points. -/
theorem torusRestrictedRootFunctionFamily_vadd
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (v : V S) :
    torusRestrictedRootFunctionFamily hS hT hE
        (hφ.vadd (cocharacterMapReal f v)) f =
      v +ᵥ torusRestrictedRootFunctionFamily hS hT hE hφ f := by
  ext α g
  by_cases hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)
  · by_cases hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α
    · apply WithTop.eq_of_forall_coe_le_iff
      intro r
      rw [RootFunctionFamily.vadd_apply, coe_le_add_real_iff,
        le_torusRestrictedRootFunctionFamily_iff hS hT hE
          (hφ.vadd (cocharacterMapReal f v)) f α hα g hg r,
        torusRestrictedRootDepthSubgroup_vadd,
        le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f α hα g hg]
    · rw [torusRestrictedRootFunctionFamily_eq_top_of_not_mem hS hT hE
          (hφ.vadd (cocharacterMapReal f v)) f α g hg,
        RootFunctionFamily.vadd_apply,
        torusRestrictedRootFunctionFamily_eq_top_of_not_mem hS hT hE hφ f α g hg,
        WithTop.top_add]
  · rw [torusRestrictedRootFunctionFamily_eq_top_of_not_mem_roots hS hT hE
        (hφ.vadd (cocharacterMapReal f v)) f α hα g,
      RootFunctionFamily.vadd_apply,
      torusRestrictedRootFunctionFamily_eq_top_of_not_mem_roots hS hT hE hφ f α hα g,
      WithTop.top_add]

end Langlands.Geometry.Building
