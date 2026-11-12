import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechet
import Langlands.Analysis.Meromorphic.AnalyticSystems
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! # Meromorphic continuation of Eisenstein series in the Fréchet spaces of uniform
moderate growth

Bernstein–Lapid, Theorem 2.3 (1) in the number field case, in the Fréchet formulation of
their Corollary 8.6. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Meromorphic continuation of Eisenstein series (Bernstein–Lapid, Theorem 2.3 (1), number
field case, with the Fréchet formulation of Corollary 8.6). In the setting of
`EisensteinAbsoluteConvergenceStatement`, with `N > 0`, there is a function `E'` on
`X^*(P) ⊗ ℂ` with values in the functions on `G(𝔸)` such that

* `E'(λ)` is the Eisenstein series `E(·, φ, λ)` for `Re λ` sufficiently regular, and
* near every point, in every linear coordinate system, `E'` is a meromorphic function with
  values in one Fréchet space `𝔉^R_L` of right `L`-invariant functions of uniform moderate
  growth (`L` an open subgroup of `G(𝔸_f)`), and at every regular point its value is an
  automorphic form on `G(F) \ G(𝔸)`. -/
def EisensteinMeromorphicContinuationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
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
      ∃ E' : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ,
        (∃ R₀ : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R₀ lam →
          E' lam = hK.eisensteinSeries φ lam) ∧
        ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin n → ℂ),
          ∃ W : TopologicalSpace.Opens (Fin n → ℂ), s₀ ∈ W ∧
            ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G)),
              IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
              ∃ (f : W → UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L) (D : Set W),
                IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D ∧
                ∀ s ∈ D, UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (f s) =
                    E' (e s) ∧
                  IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
                    (K.comap (ofInfinite F G).toMonoidHom) rho (E' (e s))

end Langlands.Global
