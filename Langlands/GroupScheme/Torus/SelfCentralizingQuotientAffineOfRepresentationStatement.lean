import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.RelativeIdentityComponent

/-! # Statement: the normalizer quotient is affine, given local central-kernel representations -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Affineness of `G / N_G(T)` from local representations with central
kernel** (SGA 3, Exposé XVI, Proposition 3.1(c), Lemma 3.2, Theorem 3.3(c)
and Theorem 4.1(c), with the proof of 4.1(d)).

Let `G` be a smooth, separated, quasi-compact group scheme over an arbitrary
scheme `S`, with connected affine residue-field fibres, and suppose that every
point of `S` lies in an affine open `Spec R ⟶ S` over which `G` has a finite
free matrix representation with central kernel. Let `t : T.toGrp ⟶ G` be a
closed relative torus which is a maximal torus on every residue-field fibre and
represents its own full centralizer. Then every `S`-scheme `Y` receiving a
flat, surjective morphism `p : G.X ⟶ Y` locally of finite presentation, whose
fibres on every test scheme are exactly the left cosets of the normalizer of
`T`, is affine over `S`. -/
def SelfCentralizingQuotientAffineOfRepresentationStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S),
    Smooth G.X.hom → IsSeparated G.X.hom → QuasiCompact G.X.hom →
    (∀ s : S,
      ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left ∧
        IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom) →
    (∀ s : S, ∃ (R : CommRingCat.{u}) (i : Spec R ⟶ S),
      IsOpenImmersion i ∧ s ∈ Set.range i.base ∧
      ∃ (m : ℕ) (ρ : MatrixRepresentation ((GroupScheme.baseChange i).obj G) (Fin m)),
        ∀ (U : Over (Spec R)) (g h : U ⟶ ((GroupScheme.baseChange i).obj G).X),
          g ≫ ρ.hom.hom = 1 → g * h = h * g) →
    ∀ (T : CommGroupScheme S) (t : T.toGrp ⟶ G),
      RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t →
      IsFibrewiseMaximalTorus t → (torusCentralizer t).IsRepresentedBy t →
      ∀ (Y : Over S) (p : G.X ⟶ Y),
        Flat p.left → Surjective p.left → LocallyOfFinitePresentation p.left →
        (∀ (U : Over S) (g h : U ⟶ G.X),
          g ≫ p = h ≫ p ↔ g⁻¹ * h ∈ (torusNormalizer t).carrier U) →
        IsAffineHom Y.hom

end Langlands.GroupScheme
