import Langlands.GroupScheme.Torus.MultiplicativeTypeExtensionBaseChange
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeSubgroupReduction
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Torus.MultiplicativeTypeFpqcReduction

/-! # reduction of the extension clause to split endpoints on an affine base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ExtensionReduction

/-- The remaining affine split-endpoint case. This is an explicit premise
of the conditional reduction, not an established theorem. -/
def AffineSplitExtensionStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsAffine S] (N G Q : GroupScheme S)
    [Flat N.X.hom] [LocallyOfFinitePresentation N.X.hom] [IsAffineHom N.X.hom]
    [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] [IsAffineHom G.X.hom]
    [Flat Q.X.hom] [LocallyOfFinitePresentation Q.X.hom] [IsAffineHom Q.X.hom]
    (i : N ⟶ G) (q : G ⟶ Q),
    Mono i.hom.hom → RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q →
      RelativeMultiplicativeType.IsDiagonalizable N →
      RelativeMultiplicativeType.IsDiagonalizable Q →
      ConnectedOrCommutativeFibers G →
      RelativeMultiplicativeType.IsMultiplicativeType G

private theorem baseChange_geometry {S T : Scheme.{u}} (b : T ⟶ S)
    (G : GroupScheme S) [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [IsAffineHom G.X.hom] :
    Flat ((baseChange b).obj G).X.hom ∧
      LocallyOfFinitePresentation ((baseChange b).obj G).X.hom ∧
      IsAffineHom ((baseChange b).obj G).X.hom := by
  change Flat (pullback.snd G.X.hom b) ∧
    LocallyOfFinitePresentation (pullback.snd G.X.hom b) ∧
      IsAffineHom (pullback.snd G.X.hom b)
  exact ⟨inferInstance, inferInstance,
    MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom G.X.hom))⟩

/-- The original extension clause follows from the remaining affine
split-endpoint case, without changing its fibre alternative. -/
theorem extension_of_affineSplit
    (hSplit : AffineSplitExtensionStatement.{u})
    {S : Scheme.{u}} (N G Q : GroupScheme S)
    [Flat N.X.hom] [LocallyOfFinitePresentation N.X.hom] [IsAffineHom N.X.hom]
    [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] [IsAffineHom G.X.hom]
    [Flat Q.X.hom] [LocallyOfFinitePresentation Q.X.hom] [IsAffineHom Q.X.hom]
    (i : N ⟶ G) (q : G ⟶ Q) (hi : Mono i.hom.hom)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hN : RelativeMultiplicativeType.IsMultiplicativeType N)
    (hQ : RelativeMultiplicativeType.IsMultiplicativeType Q)
    (hfib : ConnectedOrCommutativeFibers G) :
    RelativeMultiplicativeType.IsMultiplicativeType G := by
  let := hi
  let 𝒞 := commonAffineDiagonalizingCover hN hQ
  apply RelativeMultiplicativeType.IsMultiplicativeType.of_fppfCover 𝒞.cover
  intro t
  let b := 𝒞.cover.f t
  let N₁ := (baseChange b).obj N
  let G₁ := (baseChange b).obj G
  let Q₁ := (baseChange b).obj Q
  have : IsAffine (𝒞.cover.X t) := 𝒞.affine t
  have : Flat N₁.X.hom := (baseChange_geometry b N).1
  have : LocallyOfFinitePresentation N₁.X.hom := (baseChange_geometry b N).2.1
  have : IsAffineHom N₁.X.hom := (baseChange_geometry b N).2.2
  have : Flat G₁.X.hom := (baseChange_geometry b G).1
  have : LocallyOfFinitePresentation G₁.X.hom := (baseChange_geometry b G).2.1
  have : IsAffineHom G₁.X.hom := (baseChange_geometry b G).2.2
  have : Flat Q₁.X.hom := (baseChange_geometry b Q).1
  have : LocallyOfFinitePresentation Q₁.X.hom := (baseChange_geometry b Q).2.1
  have : IsAffineHom Q₁.X.hom := (baseChange_geometry b Q).2.2
  have hi₁ : Mono ((baseChange b).map i).hom.hom := by
    change Mono ((Over.pullback b).map i.hom.hom)
    infer_instance
  have hq₁ : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange b).map i)) ((baseChange b).map q) := by
    simpa only [SubgroupFunctor.range_baseChangeHom] using hq.baseChange b
  exact hSplit (𝒞.cover.X t) N₁ G₁ Q₁ ((baseChange b).map i) ((baseChange b).map q)
    hi₁ hq₁ (𝒞.left_diagonalizable t) (𝒞.right_diagonalizable t) (hfib.baseChange b)

/-- Both clauses of the original exact target follow from the two
remaining explicit premises. This is a conditional reduction only. -/
theorem fpqcExtension_of_fibral_and_affineSplit
    (hcrit : MultiplicativeTypeFibralCriterionStatement.{u})
    (hSplit : AffineSplitExtensionStatement.{u}) :
    MultiplicativeTypeFpqcExtensionStatement.{u} := by
  intro S
  constructor
  · intro H _ _ _ T b _ _ _ hH
    exact FpqcMultiplicativeType.of_fpqcBaseChange_of_fibralCriterion hcrit H b hH
  · intro N G Q _ _ _ _ _ _ _ _ _ i q hi hq hN hQ hfib
    exact extension_of_affineSplit hSplit N G Q i q hi hq hN hQ hfib

end Langlands.GroupScheme.ExtensionReduction
