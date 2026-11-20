import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli
import Langlands.GroupScheme.SubgroupFunctor.ConjugateFamily

/-! # Statement: the conjugacy class of the image torus embeds `G / N_G(T)` as a closed
subscheme of the moduli of subtori of `GL_m` -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Closed embedding of `G / N_G(T)` into the subtori of `GL_m`** (SGA 3,
Exposé XVI, Proposition 3.1(b), Lemma 3.2 and Theorem 3.3(c), with Exposé XV,
7.3(iv), and the proof of Exposé XVI, Theorem 4.1(d); adapted to a representation
whose kernel is central rather than equal to the centre).

Over an affine base `Spec R`, let `G` be smooth, separated and quasi-compact with
connected affine residue-field fibres, let `ρ : G ⟶ GL_m` have central kernel, and
let `t : T.toGrp ⟶ G` be a closed self-centralizing fibrewise-maximal torus. Let
`t ≫ ρ = π ≫ e` with `e : D.toGrp ⟶ GL_m` a closed torus and `π` flat, surjective
and locally of finite presentation (the image torus of `T`). Let `j` be a universal
family of closed subtori of `GL_m`, with parameter scheme `M`, and let
`f : G.X ⟶ M` classify the conjugate family `g ↦ ρ(g) D ρ(g)⁻¹`. Then for every
fppf quotient `p : G.X ⟶ Y` whose fibres are exactly the left cosets of the
normalizer of `T`, `f` factors as `p ≫ φ` with `φ.left` a closed immersion. -/
def SelfCentralizingConjugacyClosedEmbeddingStatement : Prop :=
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
      ∃ φ : Y ⟶ M, p ≫ φ = f ∧ IsClosedImmersion φ.left

end Langlands.GroupScheme
