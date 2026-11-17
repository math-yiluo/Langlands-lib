import Langlands.GroupScheme.HomScheme.TorusChartOpen
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Descending subgroup parameters to open neighbourhoods along fppf maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme.FppfParameterDescent

open TorusChart

variable {S₀ : Scheme.{u}} {G : GroupScheme S₀} {U M : Over S₀}
  {K : GroupScheme U.left} {L : GroupScheme M.left}

/-- An actual parameter for a subgroup family over an open neighbourhood of a point. -/
structure OpenParameter (j : K ⟶ (GroupScheme.baseChange U.hom).obj G)
    (i : L ⟶ (GroupScheme.baseChange M.hom).obj G) {T : Over S₀}
    (b₀ : T ⟶ M) (t : T.left) where
  neighbourhood : T.left.Opens
  mem : t ∈ neighbourhood
  parameter : Over.mk (neighbourhood.ι ≫ T.hom) ⟶ U
  evaluate_eq : TorusSubgroupModuli.evaluate j parameter =
    TorusSubgroupModuli.evaluate i
      ((Over.homMk neighbourhood.ι rfl : Over.mk (neighbourhood.ι ≫ T.hom) ⟶ T) ≫ b₀)

/-- Parameters over a flat map locally of finite presentation from an affine scheme descend to an open neighbourhood of
any point of its image, given injectivity on affine tests. -/
theorem exists_good_open_of_flat (j : K ⟶ (GroupScheme.baseChange U.hom).obj G)
    (hj : IsClosedSubgroup j)
    (hinj : ∀ T : Over S₀, IsAffine T.left → ∀ a b : T ⟶ U,
      TorusSubgroupModuli.evaluate j a = TorusSubgroupModuli.evaluate j b → a = b)
    (i : L ⟶ (GroupScheme.baseChange M.hom).obj G) (hi : IsClosedSubgroup i)
    {T : Over S₀} (hT : IsAffine T.left) (b₀ : T ⟶ M) {E : Over S₀} (hE : IsAffine E.left)
    (e : E ⟶ T) [Flat e.left] [LocallyOfFinitePresentation e.left] (aE : E ⟶ U)
    (h : TorusSubgroupModuli.evaluate j aE = TorusSubgroupModuli.evaluate i (e ≫ b₀))
    (t : T.left) (ht : t ∈ Set.range e.left.base) :
    ∃ W : T.left.Opens, t ∈ W ∧ ∃ aW : Over.mk (W.ι ≫ T.hom) ⟶ U,
      TorusSubgroupModuli.evaluate j aW =
        TorusSubgroupModuli.evaluate i ((Over.homMk W.ι rfl : Over.mk (W.ι ≫ T.hom) ⟶ T) ≫ b₀) := by
  let O : T.left.Opens := ⟨Set.range e.left.base, e.left.isOpenMap.isOpen_range⟩
  obtain ⟨hf, hle, htW⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := O) ⟨t, ht⟩
    (Set.mem_univ t)
  let W := T.left.basicOpen hf
  have hW : IsAffineOpen W := (isAffineOpen_top T.left).basicOpen hf
  have : IsAffine W.toScheme := hW
  refine ⟨W, htW, ?_⟩
  let π := pullback.snd e.left W.ι
  let πE := pullback.fst e.left W.ι
  have : Surjective π := by
    refine ⟨fun w => ?_⟩
    have hw : W.ι w ∈ O := hle (by simp)
    obtain ⟨x, hx⟩ := hw
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback x w hx
    exact ⟨z, hz⟩
  let WO : Over S₀ := Over.mk (W.ι ≫ T.hom)
  let ιO : WO ⟶ T := Over.homMk W.ι rfl
  let PO : Over S₀ := Over.mk (π ≫ W.ι ≫ T.hom)
  let πO : PO ⟶ WO := Over.homMk π rfl
  have hπE : πE ≫ E.hom = PO.hom := by
    change πE ≫ E.hom = π ≫ W.ι ≫ T.hom
    rw [← Over.w e, ← Category.assoc, pullback.condition, Category.assoc]
  let πEO : PO ⟶ E := Over.homMk πE hπE
  have hcomm : πEO ≫ e = πO ≫ ιO := Over.OverMorphism.ext pullback.condition
  let aP := πEO ≫ aE
  have haP : TorusSubgroupModuli.evaluate j aP =
      TorusSubgroupModuli.evaluate i (πO ≫ ιO ≫ b₀) := by
    have := TorusSubgroupModuli.evaluate_eq_comp j i aE (e ≫ b₀) h πEO
    rwa [← Category.assoc, hcomm, Category.assoc] at this
  have hc : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ pullback e.left W.ι), g₁ ≫ π = g₂ ≫ π →
      g₁ ≫ aP.left = g₂ ≫ aP.left := by
    intro Z g₁ g₂ hg
    let ZO : Over S₀ := Over.mk (g₁ ≫ PO.hom)
    let g₁O : ZO ⟶ PO := Over.homMk g₁ rfl
    let g₂O : ZO ⟶ PO := Over.homMk g₂ (by
      change g₂ ≫ π ≫ W.ι ≫ T.hom = g₁ ≫ π ≫ W.ι ≫ T.hom
      rw [← Category.assoc, ← hg, Category.assoc])
    have hg' : g₁O ≫ πO = g₂O ≫ πO := Over.OverMorphism.ext hg
    have he := injective_all_of_affine j hinj ZO (g₁O ≫ aP) (g₂O ≫ aP) (by
      rw [TorusSubgroupModuli.evaluate_eq_comp j i aP (πO ≫ ιO ≫ b₀) haP g₁O,
        TorusSubgroupModuli.evaluate_eq_comp j i aP (πO ≫ ιO ≫ b₀) haP g₂O,
        ← Category.assoc, hg', Category.assoc])
    exact congrArg (fun f => f.left) he
  let dW := EffectiveEpi.desc π aP.left hc
  have hfac : π ≫ dW = aP.left := EffectiveEpi.fac π aP.left hc
  have hw : dW ≫ U.hom = WO.hom := by
    apply (cancel_epi π).mp
    rw [← Category.assoc, hfac, Over.w aP]
    rfl
  let aW : WO ⟶ U := Over.homMk dW hw
  refine ⟨aW, ?_⟩
  have hπa : πO ≫ aW = aP := Over.OverMorphism.ext hfac
  have : IsAffine (pullback e.left W.ι) := inferInstance
  have : QuasiCompact πO.left := by
    change QuasiCompact π
    infer_instance
  have : Flat πO.left := by
    change Flat π
    infer_instance
  have : Surjective πO.left := by
    change Surjective π
    infer_instance
  apply evaluate_eq_of_comp_fpqc j i hj hi πO aW (ιO ≫ b₀)
  rw [hπa]
  exact haP

/-- Construct a neighbourhood parameter from a parameter over a flat affine test
map locally of finite presentation, using uniqueness on affine tests. -/
def openParameterOfFlat (j : K ⟶ (GroupScheme.baseChange U.hom).obj G)
    (hj : IsClosedSubgroup j)
    (hinj : ∀ T : Over S₀, IsAffine T.left → ∀ a b : T ⟶ U,
      TorusSubgroupModuli.evaluate j a = TorusSubgroupModuli.evaluate j b → a = b)
    (i : L ⟶ (GroupScheme.baseChange M.hom).obj G) (hi : IsClosedSubgroup i)
    {T : Over S₀} (hT : IsAffine T.left) (b₀ : T ⟶ M) {E : Over S₀} (hE : IsAffine E.left)
    (e : E ⟶ T) [Flat e.left] [LocallyOfFinitePresentation e.left] (aE : E ⟶ U)
    (h : TorusSubgroupModuli.evaluate j aE = TorusSubgroupModuli.evaluate i (e ≫ b₀))
    (t : T.left) (ht : t ∈ Set.range e.left.base) : OpenParameter j i b₀ t :=
  Classical.choice <| by
    obtain ⟨W, htW, aW, haW⟩ :=
      exists_good_open_of_flat j hj hinj i hi hT b₀ hE e aE h t ht
    exact ⟨⟨W, htW, aW, haW⟩⟩

end Langlands.GroupScheme.HomScheme.FppfParameterDescent
