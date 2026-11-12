import Langlands.Global.AdelicSquareIntegrableInducedForms
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Holomorphy of Eisenstein series on the imaginary axis

Lapid 2011, Proposition 6 (p.329): for `φ ∈ A^2_P` the Eisenstein series `E_P(·, φ, λ)` is
holomorphic at every `λ ∈ i𝔞_P^*`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Holomorphy of Eisenstein series on the imaginary axis (Lapid 2011, Proposition 6). Let
`P = MU` be a parabolic with presentation `r`, `K` a maximal compact subgroup with
`P(𝔸)K = G(𝔸)`, and `φ ∈ A^2_P` (`IsSquareIntegrableInducedForm`). Let `E` be meromorphic in
`λ ∈ X^*(P) ⊗ ℂ` at each point `g`, with one domain of holomorphy `D`, and equal to the
Eisenstein series `E(φ, λ)` for `Re λ` sufficiently regular. Then there are `E'` and an open
dense `D'` containing the imaginary parameters `i(X^*(P) ⊗ ℝ)` such that `E'` is meromorphic at
each point `g` with domain of holomorphy `D'`, and `E' λ = E λ` for `λ ∈ D ∩ D'`. -/
def EisensteinImaginaryAxisHolomorphyStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ →
      ∀ (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
        (D : Set (ComplexCharacterParameter F P)),
        (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
          E lam = hK.eisensteinSeries φ lam) →
      ∃ (E' : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
        (D' : Set (ComplexCharacterParameter F P)),
        Set.range (imaginaryParameter F P) ⊆ D' ∧
        (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E' lam g) D') ∧
        ∀ lam ∈ D ∩ D', E' lam = E lam

end Langlands.Global
