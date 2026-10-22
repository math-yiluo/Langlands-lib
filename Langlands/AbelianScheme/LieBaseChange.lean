import Langlands.AbelianScheme.Lie
import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChange

/-! # Cotangent modules at the identity under base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open scoped CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S T : AlgebraicGeometry.Scheme.{u}}

/-- The identity section of the base-changed group maps to the original identity. -/
@[reassoc (attr := simp)]
lemma identitySection_baseChange_fst (b : T ⟶ S) (G : GroupScheme S) :
    ((baseChange b).obj G).identitySection ≫ Limits.pullback.fst G.X.hom b =
      b ≫ G.identitySection := by
  change (Functor.LaxMonoidal.ε (Over.pullback b)).left ≫
    ((Over.pullback b).map η[G.X]).left ≫ Limits.pullback.fst G.X.hom b = _
  rw [Over.ε_pullback_left]
  have hm : ((Over.pullback b).map η[G.X]).left ≫ Limits.pullback.fst G.X.hom b =
      Limits.pullback.fst (𝟙 S) b ≫ G.identitySection := by
    exact Limits.pullback.lift_fst _ _ _
  rw [hm]
  have h : inv (Limits.pullback.snd (𝟙 S) b) ≫ Limits.pullback.fst (𝟙 S) b = b := by
    rw [← Category.comp_id (Limits.pullback.fst (𝟙 S) b),
      Limits.pullback.condition, IsIso.inv_hom_id_assoc]
  rw [← Category.assoc, h]

/-- Canonical identification of the two pullbacks to the new identity section. -/
def cotangentBaseChangePullbackIso (b : T ⟶ S) (G : GroupScheme S) :
    pullback G.identitySection ⋙ pullback b ≅
      pullback (Limits.pullback.fst G.X.hom b) ⋙
        pullback ((baseChange b).obj G).identitySection :=
  pullbackComp b G.identitySection ≪≫
    (pullbackCongr (identitySection_baseChange_fst b G)).symm ≪≫
    (pullbackComp ((baseChange b).obj G).identitySection
      (Limits.pullback.fst G.X.hom b)).symm

/-- The canonical base-change comparison for the cotangent module at the identity. -/
def cotangentBaseChangeMap (b : T ⟶ S) (G : GroupScheme S) :
    (pullback b).obj G.cotangentAtIdentity ⟶
      ((baseChange b).obj G).cotangentAtIdentity :=
  (cotangentBaseChangePullbackIso b G).hom.app
      (Langlands.Scheme.relativeDifferentials G.X.hom) ≫
    (pullback ((baseChange b).obj G).identitySection).map
      (Langlands.Scheme.relativeDifferentialsBaseChangeMap G.X.hom b)

end Langlands.GroupScheme
