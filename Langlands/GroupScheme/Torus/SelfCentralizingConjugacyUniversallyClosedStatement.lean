import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli
import Langlands.GroupScheme.SubgroupFunctor.ConjugateFamily

/-! # Statement: the conjugacy map from `G / N_G(T)` to the subtori of `GL_m` is universally closed -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Universal closedness of the conjugacy map from `G / N_G(T)` to the subtori of `GL_m`**
(SGA 3, Exposé XVI, Lemma 3.2 and Theorem 3.3(c), with Exposé XV, 7.3(iv), and the
proof of Exposé XVI, Theorem 4.1(d), in the setting of
`SelfCentralizingConjugacyClosedEmbeddingStatement`).

The hypotheses are exactly those of
`SelfCentralizingConjugacyClosedEmbeddingStatement`: over `Spec R`, a smooth,
separated, quasi-compact group `G` with connected affine residue-field fibres, a
representation `ρ : G ⟶ GL_m` with central kernel, a closed self-centralizing
fibrewise-maximal torus `t : T.toGrp ⟶ G`, its image torus `e : D.toGrp ⟶ GL_m`
with `t ≫ ρ = π ≫ e`, a universal family `j` of closed subtori of `GL_m` with
parameter scheme `M`, the morphism `f : G.X ⟶ M` classifying the conjugates
`g ↦ ρ(g) D ρ(g)⁻¹`, and an fppf quotient `p : G.X ⟶ Y` whose fibres are exactly the
left cosets of the normalizer of `T`. The conclusion: every `φ : Y ⟶ M` with
`p ≫ φ = f` has universally closed underlying morphism. -/
def SelfCentralizingConjugacyUniversallyClosedStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (G : GroupScheme (Spec R)),
    Smooth G.X.hom → IsSeparated G.X.hom → QuasiCompact G.X.hom →
    (∀ s : Spec R,
      ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left ∧
        IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom) →
    ∀ (m : ℕ) (ρ : MatrixRepresentation G (Fin m)),
      (∀ (U : Over (Spec R)) (g h : U ⟶ G.X), g ≫ ρ.hom.hom = 1 → g * h = h * g) →
    ∀ (T : CommGroupScheme (Spec R)) (t : T.toGrp ⟶ G),
      RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t →
      IsFibrewiseMaximalTorus t → (torusCentralizer t).IsRepresentedBy t →
    ∀ (D : CommGroupScheme (Spec R)) (π : T.toGrp ⟶ D.toGrp)
      (e : D.toGrp ⟶ GeneralLinear.groupScheme (Fin m) R),
      RelativeTorus.IsTorus D.toGrp → IsClosedSubgroup e →
      Flat π.hom.hom.left → Surjective π.hom.hom.left →
      LocallyOfFinitePresentation π.hom.hom.left → π ≫ e = t ≫ ρ →
    ∀ (M : Over (Spec R)) (K : GroupScheme M.left)
      (j : K ⟶ (GroupScheme.baseChange M.hom).obj (GeneralLinear.groupScheme (Fin m) R)),
      IsClosedSubgroup j → RelativeTorus.IsTorus K → TorusSubgroupModuli.IsUniversal j →
    ∀ f : G.X ⟶ M,
      TorusSubgroupModuli.evaluate j f =
        SubgroupFunctor.range (SubgroupFunctor.conjugateFamily e ρ.hom.hom) →
    ∀ (Y : Over (Spec R)) (p : G.X ⟶ Y),
      Flat p.left → Surjective p.left → LocallyOfFinitePresentation p.left →
      (∀ (U : Over (Spec R)) (g h : U ⟶ G.X),
        g ≫ p = h ≫ p ↔ g⁻¹ * h ∈ (torusNormalizer t).carrier U) →
      ∀ φ : Y ⟶ M, p ≫ φ = f → UniversallyClosed φ.left

end Langlands.GroupScheme
