import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionGeometry
import Langlands.GroupScheme.Dynamic.ConnectedProof

/-! # Connectedness of the centralizer intersection with a Borel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G M B : GroupScheme (Spec (CommRingCat.of k))}

/-- The connected-space structure on the actual intersection obtained by applying
dynamic connectedness inside the prescribed Borel. -/
abbrev IsBorelSubgroup.connectedSpace_centralizer_intersection
    [IsAffineHom G.X.hom] {b : B ⟶ G} (hb : IsBorelSubgroup b)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
    (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j) :
    ConnectedSpace (subgroupIntersection j b).X.left := by
  have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  have : Mono b.hom.hom := Over.mono_of_mono_left _
  have : Smooth B.X.hom := hb.smooth
  have : IsAffineHom B.X.hom := by
    rw [← Over.w b.hom.hom]
    infer_instance
  have hr : (Dynamic.centralizer (Dynamic.restrictCocharacter b χ hχ)).IsRepresentedBy
      (subgroupIntersectionSnd j b) :=
    Dynamic.isRepresentedBy_intersectionSnd b hb.isClosedSubgroup
      (Dynamic.restrictCocharacter b χ hχ) j hj (by
        rwa [Dynamic.restrictCocharacter_comp])
  exact ((dynamicConnected k B (Dynamic.restrictCocharacter b χ hχ)
    (subgroupIntersection j b) (subgroupIntersectionSnd j b)).2 hb.connectedSpace).2 hr

/-- Connectedness removes the additional premise from the actual-intersection
Borel criterion. -/
theorem IsBorelSubgroup.centralizer_intersection_isBorel_iff
    [IsAffineHom G.X.hom] {b : B ⟶ G} (hb : IsBorelSubgroup b)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
    (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j) :
    IsBorelSubgroup (subgroupIntersectionFst j b) ↔
      ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ M),
        IsBorelSubgroup c ∧ SubgroupFunctor.range (c ≫ j) ≤ SubgroupFunctor.range b :=
  hb.centralizer_intersection_borel_iff χ hχ j hj hrep
    (hb.connectedSpace_centralizer_intersection χ hχ j hj hrep)

/-- The exact existence statement upgrades to Borel maximality of the actual
first projection to the chosen centralizer. -/
theorem IsBorelSubgroup.centralizer_intersection_isBorel_of_statement
    (hIntersection : CentralizerBorelIntersectionStatement.{u})
    [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {b : B ⟶ G} (hb : IsBorelSubgroup b)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
    (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j)
    (hsm : Smooth M.X.hom) (hconn : ConnectedSpace M.X.left) :
    IsBorelSubgroup (subgroupIntersectionFst j b) :=
  (hb.centralizer_intersection_isBorel_iff χ hχ j hj hrep).2
    (hIntersection k G χ M j hj hrep hsm hconn B b hb hχ)

end Langlands.GroupScheme
