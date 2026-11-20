import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Global.AdelicIntertwiningOperator

/-! # Ambient character parameters for Eisenstein series -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Plancherel AdelicGroupPoints RealTorusSpace

/-- Restriction of a real parabolic parameter to the maximal split torus in its
standard Levi agrees with orthogonal lift from the Levi split component. -/
def EisensteinAmbientParameterLiftStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
    (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (t : r.data.T.toGrp ⟶ M),
    IsConnectedReductive G → t ≫ l ≫ p = r.data.i →
    ∀ x : RealCharacterParameter F P,
      realParameterRestriction (t ≫ l) x =
        weylCharacterRestrictionLift hA hT r.data.f r.data.i
          (realParameterRestriction (a ≫ l) x)

/-- For a representative normalizing the common split torus in two Levis,
the conjugation parameter map induces the relative Weyl action on the
restricted real parameter. -/
def EisensteinAmbientWeylParameterStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M Q M' : GroupScheme (Spec (CommRingCat.of F)))
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (p : P ⟶ G) [Mono p] (l : M ⟶ P) (q : Q ⟶ G) (l' : M' ⟶ Q)
    (t : T.toGrp ⟶ M) (t' : T.toGrp ⟶ M') (π' : Q ⟶ M')
    (n : normalizerPoints i) (c : M' ⟶ M),
    t ≫ l ≫ p = i → t' ≫ l' ≫ q = i → l' ≫ π' = 𝟙 M' →
    IsWeylConjugation p l q l' n.val c →
    ∀ lam : ComplexCharacterParameter F P,
      realParameterRestriction (t' ≫ l') (parameterRealPart F Q (weylParameter l c π' lam)) =
        relativeWeylRealCharacterAction i (QuotientGroup.mk n)
          (realParameterRestriction (t ≫ l) (parameterRealPart F P lam))

/-- The restriction and Weyl transport identities used in the leading
chamber comparison. -/
def EisensteinAmbientParametersStatement : Prop :=
  EisensteinAmbientParameterLiftStatement.{u} ∧ EisensteinAmbientWeylParameterStatement.{u}

end Langlands.Global
