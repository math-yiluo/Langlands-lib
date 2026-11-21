import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechet

/-! # A common growth space for regular Eisenstein series on bounded parameter sets

Bernstein–Lapid, §8.4 with §8.6 (number field case): on a bounded set of parameters, all
Eisenstein series `E(φ, λ)` at sufficiently regular `λ` lie in one space `𝔉^R_L` of right
`L`-invariant functions of uniform moderate growth with exponent `R`, for every large `R`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Regular Eisenstein series on a bounded parameter set lie in a common space `𝔉^R_L`
(Bernstein–Lapid §8.4 and §8.6, number field case). In the setting of
`EisensteinSystemDominationStatement` there is `R₀` such that for every linear coordinate
system `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` and every bounded set `W ⊆ ℂⁿ` there are a compact open subgroup
`L ≤ G(𝔸_f)` and a real `R₁` such that for every `R ≥ R₁` and every `s ∈ W` with `e s`
`R₀`-regular, the Eisenstein series `E(φ, e s)` is the underlying function of an element of
`𝔉^R_L` (`UniformGrowthFrechetSpace`). -/
def EisensteinCommonGrowthStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∃ R₀ : ℝ, ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
        (W : Set (Fin n → ℂ)), Bornology.IsBounded W →
          ∃ L : Subgroup (FiniteAdelicGroupPoints F G),
            IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
            IsCompact (L : Set (FiniteAdelicGroupPoints F G)) ∧
          ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R → ∀ s ∈ W, r.IsRegularParameter hA hT R₀ (e s) →
            ∃ v : UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L,
              UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v =
                hK.eisensteinSeries φ (e s)

end Langlands.Global
