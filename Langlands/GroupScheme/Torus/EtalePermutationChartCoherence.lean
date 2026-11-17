import Langlands.GroupScheme.Torus.EtalePermutationAtlasRefinement

/-! # Coherence of successive normalized chart restrictions -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.EtalePermutationAtlas

/-- Restricting a normalized chart twice equals restriction along the composite,
as an equality of actual group-scheme isomorphisms. -/
theorem restrictChart_trans
    {S U V W : Scheme.{u}} {D : GroupScheme S} {I : Type u} [Finite I]
    (f : U ⟶ S) (e : (baseChange f).obj D ≅ splitTorus U I)
    (a : V ⟶ U) (r : V ⟶ S) (ha : a ≫ f = r)
    (b : W ⟶ V) (s : W ⟶ S) (hb : b ≫ r = s) :
    restrictChart r (restrictChart f e a r ha) b s hb =
      restrictChart f e (b ≫ a) s (by rw [Category.assoc, ha]; exact hb) := by
  apply Iso.ext
  apply Grp.hom_ext
  apply (splitTorus.pointsEquiv I (((baseChange s).obj D).X)).injective
  let T : Over W := ((baseChange s).obj D).X
  let x : T ⟶ ((baseChange s).obj D).X := 𝟙 _
  have h₁ := restrictChart_coordinates r (restrictChart f e a r ha) b s hb T x
  have h₂ := restrictChart_coordinates f e (b ≫ a) s
    (by rw [Category.assoc, ha]; exact hb) T x
  rw [coordinates_restrictChart] at h₁
  simpa only [x, Category.id_comp] using h₁.trans
    ((coordinates_congr f e _ _ (Category.assoc T.hom b a) rfl).trans h₂.symm)

/-- Universal successive-restriction coherence for the actual normalized charts. -/
def ChartRestrictionCoherenceStatement : Prop :=
  ∀ {S U V W : Scheme.{u}} {D : GroupScheme S} {I : Type u} [Finite I]
    (f : U ⟶ S) (e : (baseChange f).obj D ≅ splitTorus U I)
    (a : V ⟶ U) (r : V ⟶ S) (ha : a ≫ f = r)
    (b : W ⟶ V) (s : W ⟶ S) (hb : b ≫ r = s),
    restrictChart r (restrictChart f e a r ha) b s hb =
      restrictChart f e (b ≫ a) s (by rw [Category.assoc, ha]; exact hb)

/-- The normalized chart operation satisfies its universal coherence statement. -/
theorem chartRestrictionCoherence : ChartRestrictionCoherenceStatement.{u} :=
  @restrictChart_trans

end Langlands.GroupScheme.EtalePermutationAtlas
