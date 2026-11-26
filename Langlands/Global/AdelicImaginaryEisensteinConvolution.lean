import Langlands.Global.AdelicContinuedIntertwiningConvolution
import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.AdelicSpectralTransformInputs

/-! # Pointwise convolution of Eisenstein continuations on the imaginary axis -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- For an automorphic inducing form and a supplied Eisenstein continuation holomorphic on the
imaginary axis, the values are jointly continuous there. If a normalized convolution has an
entire finite expansion in automorphic inducing forms, its Eisenstein expansion using any
supplied continuations of those forms agrees on that axis with the convolution of the input
Eisenstein value. The matrix embedding has positive size. -/
def ImaginaryEisensteinConvolutionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      0 < N → IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    let Aut := IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho
    ∀ (v : AdelicGroupPoints F G → ℂ), Aut v →
    ∀ (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      Set.range (imaginaryParameter F P) ⊆ D →
      (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
      (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries v lam) →
    (∀ (n : ℕ) (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P),
      Continuous (Function.uncurry fun x => E (imaginaryParameter F P (e x)))) ∧
    ∀ (kernel : AdelicGroupPoints F G → ℂ), Continuous kernel → HasCompactSupport kernel →
    ∀ (m : ℕ) (u : Fin m → AdelicGroupPoints F G → ℂ)
      (b : Fin m → ComplexCharacterParameter F P → ℂ)
      (E' : Fin m → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D' : Set (ComplexCharacterParameter F P)),
      (∀ q, Aut (u q)) → IsFiniteNormalizedConvolutionExpansion hK kernel v u b →
      IsEisensteinContinuation hK r hA hT u E' D' →
    ∀ (x : RealCharacterParameter F P) (g : AdelicGroupPoints F G),
      let lam := imaginaryParameter F P x
      rightConvolution F G kernel (E lam) g = ∑ q, b q lam * E' q lam g

end Langlands.Global
