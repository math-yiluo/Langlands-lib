import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.AdelicEisensteinConvergenceStatement

/-! # A characterizing system for Eisenstein series dominated by a system `Ξ_main`

Bernstein–Lapid, Proposition 8.4 with Lemma 8.1, number field case, in the Fréchet form of the
Corollary of §8.6. The system `Ξ_fnl(λ)` of §8.4 is analytic, has `E(φ, λ)` as its unique
solution for sufficiently regular `λ`, its solutions are automorphic forms (proof of
Proposition 8.4 via Lemma 8.1), and it "implies a system of the form considered in §7.2"
(last paragraph of the proof). This module states that combination: on a bounded open set of
parameters, for every large exponent `R`, there is an analytic system on `𝔉^R_L` whose solutions
are contained in the solutions of a system `Ξ_main` with data on all of `ℂⁿ`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Bernstein–Lapid, Proposition 8.4 with Lemma 8.1 (number field case), in Fréchet form, with
the domination of `Ξ_fnl(λ)` by a system `Ξ_main` of §7.2 made explicit. In the setting of
`EisensteinMeromorphicContinuationStatement` there is `R₀` such that for every linear coordinate
system `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` and every bounded open set `W ⊆ ℂⁿ` there are

* a maximal split torus `iT : T → G`, a generic cocharacter `ν` and group data `u`, `t`, `z` of
  `Ξ_main` (`IsLocalFinitenessGroupData`),
* admissible analytic data `X` of `Ξ_main` on all of `ℂⁿ`,
* a compact open subgroup `L ≤ G(𝔸_f)` and a real `R₁`,

such that for every `R ≥ R₁` there is a family `eqn i s v = c i s` (`i ∈ Idx`, `s ∈ W`) of scalar
linear equations on `v ∈ 𝔉^R_L` with

* the system analytic on `W` (`IsAnalyticSystem`);
* every solution at `s` a solution of `Ξ_main(s)` for the data `X` in `𝔉^R_L`;
* at every `s` with `e s` `R₀`-regular, exactly one solution, whose underlying function is the
  Eisenstein series `E(φ, e s)`;
* every solution an automorphic form on `G(F) \ G(𝔸)`. -/
def EisensteinSystemDominationStatement : Prop :=
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
        (W : TopologicalSpace.Opens (Fin n → ℂ)), Bornology.IsBounded (W : Set (Fin n → ℂ)) →
          ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G)
            (ν : cocharacterLattice T), IsMaximalSplitTorus iT ∧ IsGenericCocharacter iT ν ∧
          ∃ (Ua : simpleRelativeRoots iT ν → GroupScheme (Spec (CommRingCat.of F)))
            (_ : ∀ α, IsAffine (Ua α).X.left) (u : ∀ α, Ua α ⟶ G)
            (_ : ∀ α, IsClosedImmersion (u α).hom.hom.left)
            (t : simpleRelativeRoots iT ν → AdelicGroupPoints F T.toGrp) (nZ : ℕ)
            (z : Fin nZ → AdelicGroupPoints F T.toGrp),
            IsLocalFinitenessGroupData iT ν u t z ∧
          ∃ X : LocalFinitenessData F G (simpleRelativeRoots iT ν) nZ n ⊤, X.IsAdmissible ∧
          ∃ L : Subgroup (FiniteAdelicGroupPoints F G),
            IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
            IsCompact (L : Set (FiniteAdelicGroupPoints F G)) ∧
          ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R →
            ∃ (Idx : Type u)
              (eqn : Idx → W → UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L →L[ℂ] ℂ)
              (c : Idx → W → ℂ),
              IsAnalyticSystem 𝓘(ℂ, Fin n → ℂ) eqn c ∧
              (∀ s : W, systemSolutions eqn c s ⊆
                X.solutions u (fun α => map F T.toGrp G iT (t α))
                  (fun j => map F T.toGrp G iT (z j)) rho hN hrho hsmooth hcalc R L
                  ⟨s.1, trivial⟩) ∧
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
