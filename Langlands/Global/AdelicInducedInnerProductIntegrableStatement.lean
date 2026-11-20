import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Absolute convergence of the inner product `(·,·)_P` on `A^2_P`

Lapid 2011, §2 (p.311): for `φ, ψ ∈ A^2_P` the integral
`(φ, ψ)_P = ∫_{A_M U(𝔸) M(F) \ G(𝔸)} φ ψ̄` converges absolutely. In the Iwasawa form of
`inducedInnerProduct`, where the `A_M`-integration is replaced by a compactly supported weight
`β` on the coordinates of `H_P`, this is the integrability of
`(k, m) ↦ β(y(m)) δ_P(m)⁻¹ φ(m k) ψ̄(m k)` on `K × M(F) \ M(𝔸)`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Absolute convergence of the inner product `(φ, ψ)_P` on `A^2_P` (Lapid 2011, §2), in the
Iwasawa form of `inducedInnerProduct`. Let `P = MU` be a parabolic of a connected reductive `G`
over a number field with presentation `r` and Levi projection `π`, `K` a maximal compact
subgroup with `P(𝔸)K = G(𝔸)`, `μ_M` a compatible Haar measure on `M(𝔸)`, `e` coordinates on
`𝔞_P^*` and `β` a continuous compactly supported weight on `ℝⁿ`. Then for `φ, ψ ∈ A^2_P` the
integrand `(k, m) ↦ β(y(m)) δ_P(m)⁻¹ φ(m k) conj ψ(m k)` of `inducedInnerProduct` is integrable
on `K × M(F) \ M(𝔸)` for the product of the Haar probability measure on `K` and the quotient
of `μ_M` by counting measure on `M(F)`. -/
def InducedInnerProductIntegrableStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (_hA : IsSplitTorus A.toGrp) (_hT : IsSplitTorus r.data.T.toGrp) (π : P ⟶ M),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU → l ≫ π = 𝟙 M →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM →
    ∀ {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ),
      Continuous β → HasCompactSupport β →
    ∀ (φ ψ : AdelicGroupPoints F G → ℂ),
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ →
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l ψ →
      Integrable (fun z : K × RationalQuotient F M =>
          (β (parameterCoordinates F P e (characterLog F P (map F M P l z.2.out))) : ℂ) *
            parameterPower F P (-modulusParameter F P) (map F M P l z.2.out) *
            φ (map F P G p (map F M P l z.2.out) * (z.1 : AdelicGroupPoints F G)) *
            (starRingEnd ℂ)
              (ψ (map F P G p (map F M P l z.2.out) * (z.1 : AdelicGroupPoints F G))))
        ((compactHaarProbability F G K hK.isCompact).prod
          (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
            (isDiscrete_rationalSubgroup F M) μM))

end Langlands.Global
