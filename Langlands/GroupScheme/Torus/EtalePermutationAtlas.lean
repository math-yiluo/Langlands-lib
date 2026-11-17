import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Torus.WeilRestriction
import Mathlib.RingTheory.Etale.Basic

/-! # Étale permutation atlases and their Weil-presentation target -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace EtalePermutationAtlas

variable {S U V : Scheme.{u}} {D : GroupScheme S}
  {I J : Type u} [Finite I] [Finite J]

/-- Restrict a split coordinate chart, with its source expressed as a direct
pullback along the specified equal composite. -/
def restrictChart (f : U ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (q : V ⟶ U) (r : V ⟶ S) (h : q ≫ f = r) :
    (GroupScheme.baseChange r).obj D ≅ splitTorus V I :=
  (Descent.pullbackComparison f q r h D).symm ≪≫
    (GroupScheme.baseChange q).mapIso e ≪≫ splitTorus.baseChangeIso q I

/-- Two normalized charts agree by the supplied coordinate permutation on
every relative test scheme. -/
def AgreeBy {U' : Scheme.{u}} (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (q : V ⟶ U) (q' : V ⟶ U') (r : V ⟶ S)
    (h : q ≫ f = r) (h' : q' ≫ g = r) (σ : J ≃ I) : Prop :=
  ∀ (Z : Over V) (x : Z ⟶ ((GroupScheme.baseChange r).obj D).X) (j : J),
    splitTorus.pointsEquiv J Z (x ≫ (restrictChart g e' q' r h').hom.hom.hom) j =
      splitTorus.pointsEquiv I Z (x ≫ (restrictChart f e q r h).hom.hom.hom) (σ j)

/-- On the actual overlap, the chart transition is a coordinate permutation
on an open neighbourhood of every point. The permutation may vary with
the neighbourhood. -/
def LocallyPermutes {U' : Scheme.{u}} (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J) : Prop :=
  ∀ w : (pullback f g : Scheme.{u}),
    ∃ (O : (pullback f g).Opens) (_ : w ∈ O) (σ : J ≃ I),
      AgreeBy f g e e' (O.ι ≫ pullback.fst f g) (O.ι ≫ pullback.snd f g)
        (O.ι ≫ pullback.fst f g ≫ f) (by simp only [Category.assoc])
        (by rw [Category.assoc, pullback.condition, ← Category.assoc]) σ

end EtalePermutationAtlas

/-- A small jointly surjective étale cover supplies actual split coordinates
whose transitions are locally coordinate permutations. Ranks may differ
between cover members, and empty coordinate types are allowed. -/
def HasEtalePermutationAtlas {S : Scheme.{u}} (D : GroupScheme S) : Prop :=
  ∃ (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (I : 𝒰.I₀ → Type u) (hI : ∀ a, Finite (I a)),
    letI : ∀ a, Finite (I a) := hI
    ∃ e : ∀ a, (GroupScheme.baseChange (𝒰.f a)).obj D ≅ splitTorus (𝒰.X a) (I a),
      ∀ a b, EtalePermutationAtlas.LocallyPermutes (𝒰.f a) (𝒰.f b) (e a) (e b)

/-- A group scheme over an arbitrary affine base with an étale permutation
atlas is the Weil restriction of the multiplicative group from a finite,
projective, étale algebra. No affineness hypothesis on the group scheme
is supplied. -/
def PermutationAtlasWeilPresentationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (D : GroupScheme (Spec (CommRingCat.of R))),
    HasEtalePermutationAtlas D →
      ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E)
        (_ : Module.Finite R E) (_ : Module.Projective R E),
        Algebra.Etale R E ∧
          Nonempty (D ≅ WeilGm.groupScheme (CommRingCat.of R) E)

end Langlands.GroupScheme
