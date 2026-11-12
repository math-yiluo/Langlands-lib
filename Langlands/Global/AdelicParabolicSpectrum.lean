import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates
import Langlands.Representation.Unitary.DiscretePart
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # The spaces `L²_𝒫([G])` and `L²_disc([G])`

Getz–Hahn §9.1 (9.6) and §10.5 (10.21)–(10.24): the discrete spectrum of `L²([G])`,
`[G] = A_G G(F) \ G(𝔸)`, and the closed subspace `L²_𝒫([G])` spanned by the wave packets
`∫_{i(𝔞_M^G)^*} E(x, F_P(λ), λ) dλ` of compactly supported families attached to a parabolic `P`
of the association class `𝒫`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Analysis.Meromorphic

section Relative

variable {F : Type} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The space `(𝔞_M^G)^*` inside `𝔞_P^* = X^*(P) ⊗ ℝ`: the real parameters `μ` with
`⟨μ, H_P(x)⟩ = 0` for every `x ∈ P(𝔸)` whose image in `G(𝔸)` lies in the split component
`A_G` of `G(𝔸)`. -/
def relativeParameterSpace (p : P ⟶ G) : Submodule ℝ (RealCharacterParameter F P) :=
  ⨅ (x : AdelicGroupPoints F P) (_ : map F P G p x ∈ RestrictionSplitCentre.canonicalSubgroup F G),
    LinearMap.ker ((realParameterPairing F P).flip (characterLog F P x))

end Relative

section WavePackets

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

/-- `Θ` is a wave packet of Eisenstein series of `P` over the imaginary parameters
`i(𝔞_M^G)^*` (Getz–Hahn (10.24) for one parabolic):
`Θ(g) = ∫ ∑ j, c j x · E(v j, i e(x))(g) dx`, where `e` are coordinates on `(𝔞_M^G)^*`,
`v j ∈ A^2_P`, the `c j` are smooth and compactly supported, and `E j` is the meromorphic
continuation of the Eisenstein series `E(v j, λ)`, holomorphic near `i𝔞_P^*`. -/
def IsRelativeWavePacket (hK : IsIwasawaCompact p K) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (iU : U ⟶ P) (l : M ⟶ P)
    {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (Θ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∃ (n : ℕ) (e : (Fin n → ℝ) ≃ₗ[ℝ] relativeParameterSpace (F := F) p) (k : ℕ)
    (v : Fin k → AdelicGroupPoints F G → ℂ) (c : Fin k → (Fin n → ℝ) → ℂ)
    (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
    (D : Set (ComplexCharacterParameter F P)),
    (∀ j, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (v j)) ∧
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j) ∧ HasCompactSupport (c j)) ∧
    Set.range (imaginaryParameter F P) ⊆ D ∧
    (∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D) ∧
    (∀ j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
      E j lam = hK.eisensteinSeries (v j) lam) ∧
    Θ = fun g => ∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x : RealCharacterParameter F P)) g
      ∂(spectralMeasure n)

/-- The space `L²_𝒫([G])` of Getz–Hahn §10.5 for the association class `𝒫` of `P`: the closure
in `L²([G])` of the span of the classes of the wave packets of `P` over `i(𝔞_M^G)^*`. -/
def parabolicSpectrum (hK : IsIwasawaCompact p K) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (iU : U ⟶ P) (l : M ⟶ P)
    {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) :
    Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)) :=
  (Submodule.span ℂ {f : Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G) |
    ∃ Θ, IsRelativeWavePacket hK rho hsmooth hcalc iU l r hA hT Θ ∧
      f =ᵐ[RestrictionSplitCentre.canonicalMeasure F G] fun y => Θ y.out}).topologicalClosure

end WavePackets

section Discrete

variable (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The discrete spectrum `L²_disc([G])` (Getz–Hahn (9.6)): the discrete part of the right
regular representation of `G(𝔸)` on `L²([G])`. -/
def discreteSpectrum (hG : IsConnectedReductive G) :
    Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)) :=
  Langlands.Analysis.discretePart
    (RestrictionSplitCentre.canonicalL2RightAction F G centralSplitTorusCharacter.{0} hG)

end Discrete

end Langlands.Global.AdelicGroupPoints
