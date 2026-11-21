import Langlands.Global.AdelicEisensteinSystemDominationStatement
import Langlands.Global.AdelicCuspidalAnnihilator

/-! # The cuspidal tests (8.2b) of the characterizing system of Eisenstein series

Bernstein–Lapid, §8.4, number field case: the non-homogeneous cuspidal equations (8.2b) of
the system `Ξ_fnl(λ)`, as scalar linear equations on `𝔉^R_L`, with the three properties used
in the proof of Proposition 8.4: every solution satisfies the difference equations (8.3) in the
cuspidal annihilators, the Eisenstein series is a solution at regular parameters ((6.21)), and
at regular parameters it is the only automorphic solution ((6.22)). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Bernstein–Lapid §8.4, the cuspidal equations (8.2b) and their consequences (8.3), (6.21)
and (6.22), number field case. In the setting of `EisensteinSystemDominationStatement` there
are `R₀`, a standard parabolic family `𝓕` (a minimal parabolic `P₀ = P_∅` with its standard
parabolics `P_J`) and a maximal compact subgroup `K'` with `P_J(𝔸) K' = G(𝔸)` for every `P_J`
(only maximality and this Iwasawa coverage are required; a `K'` in good position with respect
to `M₀` as in BL §2.1, which also meets the standard Levis in maximal compacts, is one possible
witness), such
that for all linear coordinates `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` there are polynomials `D J b Q s`
(`J`, `Q` standard, `b` a positive point of the split component `A_J`, `s ∈ ℂⁿ`), monic of a
degree independent of `s`, with nonzero constant coefficient and entire coefficients, with the
following property. For every compact open `L ≤ G(𝔸_f)` and every `R` there is a family
`eqn i s v = c i s` (`i ∈ Idx`, `s ∈ ℂⁿ`) of scalar linear equations on `v ∈ 𝔉^R_L` such that

* the system is analytic on `ℂⁿ`;
* for every solution `v` at `s`, every `J`, `b ∈ A_J` positive and `Q ≤ J`, the polynomial
  `D J b Q s` in the left translation by `b` (`f ↦ f(b ·)`) sends the constant term `C_Q v`
  into the cuspidal annihilator along `Q` (for `K'`); the action of the polynomial is written
  out as `∑_k coeff_k · C_Q v (b^k g)`;
* at every `s` with `e s` `R₀`-regular, every `v` whose function is `E(φ, e s)` is a solution;
* at every `s` with `e s` `R₀`-regular, every solution whose function is an automorphic form on
  `G(F) \ G(𝔸)` (for the archimedean part of `K`) has `E(φ, e s)` as its function. -/
def EisensteinCuspidalTestSystemStatement : Prop :=
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
      ∃ R₀ : ℝ, ∃ (𝓕 : StandardParabolicFamily F G) (K' : Subgroup (AdelicGroupPoints F G)),
        IsMaximalCompactSubgroup F G K' ∧
        (∀ Q : StandardIndex F G 𝓕.i 𝓕.ν, IsIwasawaCompact (𝓕.p Q) K') ∧
        ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P),
          ∃ (D : ∀ J : StandardIndex F G 𝓕.i 𝓕.ν, 𝓕.positiveSplitComponent J →
              StandardIndex F G 𝓕.i 𝓕.ν → (Fin n → ℂ) → Polynomial ℂ)
            (deg : ∀ J : StandardIndex F G 𝓕.i 𝓕.ν, 𝓕.positiveSplitComponent J →
              StandardIndex F G 𝓕.i 𝓕.ν → ℕ),
            (∀ J b Q s, (D J b Q s).Monic ∧ (D J b Q s).natDegree = deg J b Q ∧
              (D J b Q s).coeff 0 ≠ 0) ∧
            (∀ J b Q k, Differentiable ℂ fun s => (D J b Q s).coeff k) ∧
            ∀ L : Subgroup (FiniteAdelicGroupPoints F G),
              IsOpen (L : Set (FiniteAdelicGroupPoints F G)) →
              IsCompact (L : Set (FiniteAdelicGroupPoints F G)) → ∀ R : ℝ,
              ∃ (Idx : Type u)
                (eqn : Idx → (Fin n → ℂ) →
                  UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L →L[ℂ] ℂ)
                (c : Idx → (Fin n → ℂ) → ℂ),
                IsAnalyticSystem 𝓘(ℂ, Fin n → ℂ) eqn c ∧
                (∀ s, ∀ v ∈ systemSolutions eqn c s,
                  ∀ (J : StandardIndex F G 𝓕.i 𝓕.ν) (b : 𝓕.positiveSplitComponent J)
                    (Q : StandardIndex F G 𝓕.i 𝓕.ν), Q ≤ J →
                    (fun g => ∑ k ∈ Finset.range ((D J b Q s).natDegree + 1),
                        (D J b Q s).coeff k * 𝓕.constantTerm Q
                          (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v)
                          (map F (𝓕.P J) G (𝓕.p J) b ^ k * g)) ∈
                      𝓕.cuspidalAnnihilator (K'.comap (ofInfinite F G).toMonoidHom) rho Q) ∧
                (∀ s, r.IsRegularParameter hA hT R₀ (e s) →
                  ∀ v : UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L,
                    UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v =
                        hK.eisensteinSeries φ (e s) →
                      v ∈ systemSolutions eqn c s) ∧
                ∀ s, r.IsRegularParameter hA hT R₀ (e s) → ∀ v ∈ systemSolutions eqn c s,
                  IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
                      (K.comap (ofInfinite F G).toMonoidHom) rho
                      (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v) →
                    UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L v =
                      hK.eisensteinSeries φ (e s)

end Langlands.Global
