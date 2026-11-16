import Langlands.GroupScheme.Descent.SquareSemilinear

/-! # Inverse projection for commuting pullback squares -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Descent

/-- The inverse square comparison preserves the same original projection. -/
@[reassoc] theorem squareComparison_inv_fst_fst {B S U V : Scheme.{u}}
    (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d) (G : GroupScheme B) :
    (squareComparison b c d e h G).inv.hom.hom.left ≫
        pullback.fst ((baseChange b).obj G).X.hom c ≫ pullback.fst G.X.hom b =
      pullback.fst ((baseChange d).obj G).X.hom e ≫ pullback.fst G.X.hom d := by
  simp only [squareComparison, Iso.trans_inv, Iso.symm_inv, Grp.comp_hom_hom,
    Over.comp_left, Category.assoc, pullbackComparison_inv_fst,
    pullbackComparison_hom_fst]

end Langlands.GroupScheme.Descent
