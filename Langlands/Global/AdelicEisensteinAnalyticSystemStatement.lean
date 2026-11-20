import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechet
import Langlands.Analysis.Meromorphic.AnalyticSystems
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! # The analytic system of linear equations characterizing Eisenstein series

Bernstein–Lapid, Proposition of §8.4 (the system `Ξ_fnl(λ)`), with Lemma 8.1 (its solutions
are automorphic forms) and the Fréchet refinement of the Corollary at the end of §8.6, in the
number field case: on every bounded open set of parameters there is a holomorphic system of
linear equations on one Fréchet space `𝔉^R_L` of functions of uniform moderate growth which is
locally of finite type, whose solutions are automorphic forms, and whose unique solution at a
sufficiently regular parameter `λ` is the Eisenstein series `E(φ, λ)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- The Eisenstein series of `φ` is characterized by an analytic system of linear equations
(Bernstein–Lapid, Proposition of §8.4 with Lemma 8.1 and the Corollary of §8.6, number field
case). In the setting of `EisensteinMeromorphicContinuationStatement` there is `R₀` such that
for every linear coordinate system `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` and every bounded open set `W ⊆ ℂⁿ`
there are a real `R`, an open subgroup `L ≤ G(𝔸_f)` and a family `eqn i s v = c i s`, `i ∈ Idx`, of
scalar linear equations on `v ∈ 𝔉^R_L`, parametrized by `s ∈ W`, such that

* the system is analytic on `W` (`IsAnalyticSystem`) and its solution sets are locally of
  finite type (`IsLocallyFiniteType`);
* at every `s ∈ W` with `e s` `R₀`-regular, the system has exactly one solution, whose
  underlying function is the Eisenstein series `E(φ, e s)`;
* at every `s ∈ W`, every solution is an automorphic form on `G(F) \ G(𝔸)`. -/
def EisensteinAnalyticSystemStatement : Prop :=
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
      ∃ R₀ : ℝ, ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
        (W : TopologicalSpace.Opens (Fin n → ℂ)), Bornology.IsBounded (W : Set (Fin n → ℂ)) →
          ∃ (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G)),
            IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
            ∃ (Idx : Type u)
              (eqn : Idx → W → UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L →L[ℂ] ℂ)
              (c : Idx → W → ℂ),
              IsAnalyticSystem 𝓘(ℂ, Fin n → ℂ) eqn c ∧
              IsLocallyFiniteType 𝓘(ℂ, Fin n → ℂ) (systemSolutions eqn c) ∧
              (∀ s : W, r.IsRegularParameter hA hT R₀ (e s) →
                ∃ v : UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L,
                  UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v =
                      hK.eisensteinSeries φ (e s) ∧
                    systemSolutions eqn c s = {v}) ∧
              ∀ s : W, ∀ v ∈ systemSolutions eqn c s,
                IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
                  (K.comap (ofInfinite F G).toMonoidHom) rho
                  (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v)

end Langlands.Global
