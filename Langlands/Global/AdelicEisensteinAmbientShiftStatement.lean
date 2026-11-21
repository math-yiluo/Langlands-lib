import Langlands.Global.AdelicCharacterParameterPullback
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates

/-! # Shifts of the actual Eisenstein parameter in the ambient character direction

The defining sum transforms by the ambient adelic character. For an ambient shift of real part
zero, the same identity holds on the common holomorphy domain of a supplied continuation.
-/

noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Langlands.Analysis.Meromorphic

/-- Ambient-character shifts of the defining Eisenstein sum, with the Library's unconditional
`tsum` convention. Here `p*ν` is the pullback of the actual ambient parameter. -/
def EisensteinSeriesAmbientShiftStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
    (phi : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)
    (ν : ComplexCharacterParameter F G) (g : AdelicGroupPoints F G),
    hK.eisensteinSeries phi (lam + parameterRestrict p ν) g =
      parameterPower F G ν g * hK.eisensteinSeries phi lam g

/-- Ambient shifts of real part zero preserve the regularity region. A scalar meromorphic
continuation agreeing with the defining sum on the sufficiently regular part of its holomorphy
domain satisfies the same shift identity wherever both parameters are in that domain. -/
def EisensteinContinuationAmbientShiftStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp), IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
    (phi : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G)
    (E : ComplexCharacterParameter F P → ℂ) (D : Set (ComplexCharacterParameter F P)),
    IsMeromorphicInCoordinatesOn E D →
    (∃ R : ℝ, ∀ lam ∈ D, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries phi lam g) →
    ∀ (ν : ComplexCharacterParameter F G), parameterRealPart F G ν = 0 →
    ∀ lam ∈ D, lam + parameterRestrict p ν ∈ D →
      E (lam + parameterRestrict p ν) = parameterPower F G ν g * E lam

/-- The ambient shift identity for the defining sum and its common-domain continuation. -/
def EisensteinAmbientShiftStatement : Prop :=
  EisensteinSeriesAmbientShiftStatement.{u} ∧ EisensteinContinuationAmbientShiftStatement.{u}

end Langlands.Global
