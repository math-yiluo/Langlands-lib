import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli
import Langlands.GroupScheme.SubgroupFunctor.ConjugateFamily
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Statement: conjugates of the image torus extend over valuation rings -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Valuative lifting for the conjugacy map to the subtori of `GL_m`** (the
valuative form of SGA 3, Exposé XVI, Lemma 3.2 and Theorem 3.3(c), with Exposé XV,
7.3(iv), and Exposé XII, Theorem 7.1(b), in the setting of
`SelfCentralizingConjugacyUniversallyClosedStatement`).

The hypotheses on `G`, `ρ`, `T`, `D`, the universal family `j` and the conjugacy map
`f : G.X ⟶ M` are those of `SelfCentralizingConjugacyUniversallyClosedStatement`.
Let `A` be a valuation subring of an algebraically closed field `Ω`. Let
`g : Spec Ω ⟶ G` be a point of `G`, and let `b : Spec A ⟶ M` be a point of the scheme
of subtori whose restriction to `Spec Ω` is `f(g)`. Then `b = f(h)` for some point
`h : Spec A ⟶ G`. In terms of subtori: a closed subtorus of `GL_{m,A}` whose generic
fibre is the conjugate `ρ(g) D_Ω ρ(g)⁻¹` is the conjugate `ρ(h) D_A ρ(h)⁻¹` for some
`h ∈ G(A)`. -/
def SelfCentralizingConjugacyValuationLiftStatement : Prop :=
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
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)
      (g : Spec (CommRingCat.of Ω) ⟶ G.X.left) (b : Spec (CommRingCat.of A) ⟶ M.left),
      Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ b = g ≫ f.left →
      ∃ h : Spec (CommRingCat.of A) ⟶ G.X.left, h ≫ f.left = b

end Langlands.GroupScheme
