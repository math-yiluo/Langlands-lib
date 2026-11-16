import Langlands.GroupScheme.Lie.SmoothBaseChange
import Langlands.AlgebraicGeometry.Picard.FiniteLocallyFreeDeterminantPullback

/-! # Determinant line of the actual Lie sheaf of a smooth group scheme -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S T : Scheme.{u}}

/-- The determinant of the actual Lie sheaf, using its proved finite local bases. -/
def smoothLieDeterminant (G : GroupScheme S) (hG : Smooth G.X.hom) : LineBundle S :=
  finiteLocallyFreeDeterminant (G.lie_hasFiniteLocalBasis hG)

/-- An actual group isomorphism induces an isomorphism of the Lie determinants. -/
def smoothLieDeterminantIso {G H : GroupScheme S}
    (hG : Smooth G.X.hom) (hH : Smooth H.X.hom) (e : G ≅ H) :
    smoothLieDeterminant G hG ≅ smoothLieDeterminant H hH :=
  finiteLocallyFreeDeterminantIso (G.lie_hasFiniteLocalBasis hG)
    (H.lie_hasFiniteLocalBasis hH) ((lieFunctor S).mapIso e)

@[simp]
lemma smoothLieDeterminantIso_refl (G : GroupScheme S) (hG : Smooth G.X.hom) :
    smoothLieDeterminantIso hG hG (Iso.refl G) = Iso.refl _ := by
  simp only [smoothLieDeterminantIso, Functor.mapIso_refl]
  exact finiteLocallyFreeDeterminantIso_refl (G.lie_hasFiniteLocalBasis hG)

/-- Determinants preserve composition of actual smooth-group isomorphisms. -/
lemma smoothLieDeterminantIso_comp {G H K : GroupScheme S}
    (hG : Smooth G.X.hom) (hH : Smooth H.X.hom) (hK : Smooth K.X.hom)
    (e : G ≅ H) (f : H ≅ K) :
    smoothLieDeterminantIso hG hH e ≪≫ smoothLieDeterminantIso hH hK f =
      smoothLieDeterminantIso hG hK (e ≪≫ f) := by
  simp only [smoothLieDeterminantIso, finiteLocallyFreeDeterminantIso_comp,
    Functor.mapIso_trans]

private lemma smoothBaseChange (b : T ⟶ S) (G : GroupScheme S)
    (hG : Smooth G.X.hom) : Smooth ((baseChange b).obj G).X.hom := by
  let : Smooth G.X.hom := hG
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- The determinant of the actual Lie sheaf commutes with arbitrary base change. -/
def smoothLieDeterminantBaseChangeIso (b : T ⟶ S) (G : GroupScheme S)
    (hG : Smooth G.X.hom) :
    (LineBundle.pullback b).obj (smoothLieDeterminant G hG) ≅
      smoothLieDeterminant ((baseChange b).obj G) (smoothBaseChange b G hG) :=
  finiteLocallyFreeDeterminantPullbackIso (G.lie_hasFiniteLocalBasis hG) b ≪≫
    finiteLocallyFreeDeterminantIso (HasFiniteLocalBasis.pullback (G.lie_hasFiniteLocalBasis hG) b)
      (((baseChange b).obj G).lie_hasFiniteLocalBasis (smoothBaseChange b G hG))
      (smoothLieBaseChangeIso b G hG)

/-- Base change of actual Lie determinants is natural in group isomorphisms. -/
lemma smoothLieDeterminantBaseChangeIso_naturality (b : T ⟶ S)
    {G H : GroupScheme S} (hG : Smooth G.X.hom) (hH : Smooth H.X.hom)
    (e : G ≅ H) :
    (LineBundle.pullback b).mapIso (smoothLieDeterminantIso hG hH e) ≪≫
        smoothLieDeterminantBaseChangeIso b H hH =
      smoothLieDeterminantBaseChangeIso b G hG ≪≫
        smoothLieDeterminantIso (smoothBaseChange b G hG) (smoothBaseChange b H hH)
          ((baseChange b).mapIso e) := by
  have hn : (Scheme.Modules.pullback b).mapIso ((lieFunctor S).mapIso e) ≪≫
        smoothLieBaseChangeIso b H hH =
      smoothLieBaseChangeIso b G hG ≪≫
        (lieFunctor T).mapIso ((baseChange b).mapIso e) := by
    apply Iso.ext
    exact smoothLieBaseChangeIso_naturality b G hG hH e.hom
  dsimp only [smoothLieDeterminantBaseChangeIso, smoothLieDeterminantIso]
  rw [← Iso.trans_assoc, finiteLocallyFreeDeterminantPullbackIso_naturality,
    Iso.trans_assoc, finiteLocallyFreeDeterminantIso_comp, hn,
    ← finiteLocallyFreeDeterminantIso_comp, Iso.trans_assoc]

end Langlands.GroupScheme
