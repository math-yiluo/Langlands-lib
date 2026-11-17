import Langlands.GroupScheme.Descent.FppfLocalSolutionGluing
import Langlands.GroupScheme.Descent.ReindexTransport
import Langlands.GroupScheme.Descent.FppfSchemeSolutionGroup

/-! # Effective gluing of supplied local fppf solutions -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxRecDepth 2500

namespace Langlands.GroupScheme.Descent.FppfLocalSolutionGluing

variable {B S Z : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}
  (D : Datum p G)
  (𝒰 : B.OpenCover) [Category 𝒰.I₀] [𝒰.LocallyDirected]
  [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  (s : ∀ i : 𝒰.I₀, Solution (D.baseChange (𝒰.f i)))
  [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]

/-- Above any base chart, transport has equal images under the glued projection. -/
theorem move_proj_of_chart (i : 𝒰.I₀) (a : Z ⟶ G.X.left) (b : Z ⟶ S)
    (h : a ≫ G.X.hom ≫ p = b ≫ p) (z : Z ⟶ 𝒰.X i)
    (hz : (a ≫ G.X.hom) ≫ p = z ≫ 𝒰.f i) :
    a ≫ proj D 𝒰 s = D.move a b h ≫ proj D 𝒰 s := by
  let q := pullback.fst p (𝒰.f i)
  let t := pullback.snd p (𝒰.f i)
  let v₁ : Z ⟶ pullback p (𝒰.f i) := pullback.lift (a ≫ G.X.hom) z hz
  let v₂ : Z ⟶ pullback p (𝒰.f i) := pullback.lift b z (by
    simpa only [Category.assoc] using h.symm.trans (by
      simpa only [Category.assoc] using hz))
  let a' : Z ⟶ ((GroupScheme.baseChange q).obj G).X.left :=
    pullback.lift a v₁ (by simp [v₁, q])
  have ha' : a' ≫ ((GroupScheme.baseChange q).obj G).X.hom ≫ t = v₂ ≫ t := by
    change a' ≫ pullback.snd G.X.hom q ≫ t = v₂ ≫ t
    simp [a', v₁, v₂, t]
  have hm : (D.baseChange (𝒰.f i)).move a' v₂ ha' ≫ pullback.fst G.X.hom q =
      D.move a b h := by
    simpa only [a', v₁, v₂, q, t, Datum.baseChange, pullback.lift_fst] using
      D.move_reindex_fst t q (𝒰.f i) pullback.condition a' v₂ ha'
  calc
    a ≫ proj D 𝒰 s = a' ≫ pullback.fst G.X.hom q ≫ proj D 𝒰 s := by
      simp only [a', pullback.lift_fst_assoc]
    _ = a' ≫ (s i).schemeProj ≫ colimit.ι (functor D 𝒰 s) i := by
      rw [local_proj]
    _ = (D.baseChange (𝒰.f i)).move a' v₂ ha' ≫ (s i).schemeProj ≫
        colimit.ι (functor D 𝒰 s) i := by
      exact congrArg (· ≫ colimit.ι (functor D 𝒰 s) i)
        ((s i).schemeSolution.move_proj a' v₂ ha')
    _ = (D.baseChange (𝒰.f i)).move a' v₂ ha' ≫
        pullback.fst G.X.hom q ≫ proj D 𝒰 s := by
      rw [local_proj]
    _ = D.move a b h ≫ proj D 𝒰 s := by rw [← Category.assoc, hm]

/-- The glued quotient map is invariant under the original actual relation. -/
theorem relation : D.source ≫ proj D 𝒰 s = D.target ≫ proj D 𝒰 s := by
  apply (𝒰.pullback₁ (D.source ≫ G.X.hom ≫ p)).hom_ext
  intro i
  let r : (𝒰.pullback₁ (D.source ≫ G.X.hom ≫ p)).X i ⟶ D.relationScheme :=
    pullback.fst (D.source ≫ G.X.hom ≫ p) (𝒰.f i)
  change r ≫ D.source ≫ proj D 𝒰 s = r ≫ D.target ≫ proj D 𝒰 s
  have hh := move_proj_of_chart D 𝒰 s i (r ≫ D.source)
    (r ≫ D.target ≫ G.X.hom) (D.relation_point_base r)
    (pullback.snd (D.source ≫ G.X.hom ≫ p) (𝒰.f i)) (by
      simpa only [Category.assoc] using
        pullback.condition (f := D.source ≫ G.X.hom ≫ p) (g := 𝒰.f i))
  simpa only [D.move_relation, Category.assoc] using hh

/-- Actual underlying scheme descent from supplied local solutions. -/
def schemeSolution : SchemeSolution D where
  obj := obj D 𝒰 s
  proj := proj D 𝒰 s
  square := square D 𝒰 s
  relation := relation D 𝒰 s

/-- Actual group-scheme descent from supplied local solutions. -/
def solution : Solution D := (schemeSolution D 𝒰 s).fppfSolution

end Langlands.GroupScheme.Descent.FppfLocalSolutionGluing
