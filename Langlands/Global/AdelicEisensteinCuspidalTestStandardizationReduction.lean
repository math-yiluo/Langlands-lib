import Langlands.Global.AdelicEisensteinCuspidalTestIntertwiningReduction

/-! # Continued cuspidal-test expansions: reduction to standard parabolics

Bernstein–Lapid, §6.10, (6.18), with Theorem 2.3 (3) and §8.6, for an arbitrary parabolic `P`
presented by `r` and a maximal compact subgroup `K` in good position for a standard parabolic
family `𝓕`. A rational conjugate of `P` is a standard parabolic `P_I`; the norm-one Levi tests of
the constant terms of `E_P(φ, λ)` are finite combinations, with coefficients entire in `λ`, of the
tests of the constant terms of the series `E_{P_I}(φ'_j, ιλ)`, where `ι` identifies the parameter
spaces and transports regularity and root forms. With the continued expansion for standard
parabolics (`EisensteinCuspidalTestStandardExpansionStatement`) this gives
`EisensteinCuspidalTestContinuedExpansionStatement`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Set
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

attribute [local instance] StandardParabolicFamily.isClosedImmersion_p

/-- Passage of the cuspidal tests of Eisenstein series to a standard parabolic (derived from
Bernstein–Lapid §2.1–§2.2 and Mœglin–Waldspurger II.1.5, II.1.7). In the setting of
`EisensteinCuspidalTestContinuedExpansionStatement` there are a standard index `I`, a complex
linear isomorphism `iota : X^*(P) ⊗ ℂ ≃ X^*(P_I) ⊗ ℂ`, finitely many automorphic functions `φ' j`
on `U_I(𝔸) M_I(F) \ G(𝔸)` and coefficients `E j` entire on `X^*(P) ⊗ ℂ` in linear coordinates,
together with the instances required by the root forms and the regularity predicate of the
standard root presentation of `P_I`, such that:

* `iota` maps sufficiently regular parameters for `r` to regular parameters of the standard
  presentation of `P_I`;
* for every root `β'` of `A_I` in the unipotent radical of `P_I`, the pull-back along `iota` of the
  root form of `β'` is a nonzero multiple of the root form of a root `β` of `A` in the unipotent
  radical of `P`;
* for `λ` sufficiently regular, every standard `J`, every cusp form `ψ` on `M_J(F) \ M_J(𝔸)` and
  every `g`, the norm-one Levi test of `C_J E_P(φ, λ)` is
  `∑ j, E j λ · (C_J E_{P_I}(φ' j, iota λ)(· g), ψ)`. -/
def EisensteinCuspidalTestStandardizationStatement : Prop :=
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
    ∀ (𝓕 : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G))
      (hK : IsIwasawaCompact p K) (h₀ : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K),
      (∀ J : StandardIndex F G 𝓕.i 𝓕.ν, IsMaximalCompactSubgroup F (𝓕.M J)
        (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom)) →
      ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
        (hsmooth : SmoothOfRelativeDimension d G.X.hom)
        (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
        IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
        IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
          (K.comap (ofInfinite F G).toMonoidHom) rho φ →
        ∃ (I : StandardIndex F G 𝓕.i 𝓕.ν)
          (iota : ComplexCharacterParameter F P ≃ₗ[ℂ] ComplexCharacterParameter F (𝓕.P I))
          (m : ℕ) (E : Fin m → ComplexCharacterParameter F P → ℂ)
          (φ' : Fin m → AdelicGroupPoints F G → ℂ),
          (∀ j, 𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I (φ' j)) ∧
          (∀ j (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P),
            Differentiable ℂ (E j ∘ e)) ∧
          ∃ (_ : Fintype (relativeWeylGroup 𝓕.i))
            (_ : ∀ J, Mono (CommGroupScheme.groupHom (𝓕.f J)).hom.hom.left),
            (∀ R : ℝ, ∃ R' : ℝ, ∀ lam, r.IsRegularParameter hA hT R' lam →
              (𝓕.rootPresentation I).IsRegularParameter
                (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
                𝓕.maximalSplit.isSplitSubtorus.1 R (iota lam)) ∧
            (∀ β' ∈ (𝓕.rootPresentation I).unipotentRoots, ∃ β ∈ r.unipotentRoots,
              ∃ s : ℂ, s ≠ 0 ∧
                (𝓕.rootPresentation I).rootFunctional
                    (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
                    𝓕.maximalSplit.isSplitSubtorus.1 β' ∘ₗ iota.toLinearMap =
                  s • r.rootFunctional hA hT β) ∧
            ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
              ∀ (J : StandardIndex F G 𝓕.i 𝓕.ν) (ψ : AdelicGroupPoints F (𝓕.M J) → ℂ),
                𝓕.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J ψ → ∀ g,
                  𝓕.leviPairing J (𝓕.constantTerm J (hK.eisensteinSeries φ lam)) g ψ =
                    ∑ j, E j lam * 𝓕.leviPairing J (𝓕.constantTerm J
                      ((𝓕.isIwasawaCompact_of_minimal h₀ I).eisensteinSeries (φ' j)
                        (iota lam))) g ψ

/-- The reduction of the continued cuspidal-test expansion to the passage to standard
parabolics and the continued expansion for standard parabolics. -/
def EisensteinCuspidalTestContinuedExpansionStandardizationReductionStatement : Prop :=
  EisensteinCuspidalTestStandardizationStatement.{u} →
    EisensteinCuspidalTestStandardExpansionStatement.{u} →
      EisensteinCuspidalTestContinuedExpansionStatement.{u}

/-- The reduction of the continued cuspidal-test expansion to three premises: the passage to
standard parabolics, the tested constant-term formula (6.18) for standard parabolics, and the
restricted continuation of its tested intertwining terms. -/
def EisensteinCuspidalTestContinuedExpansionReductionStatement : Prop :=
  EisensteinCuspidalTestStandardizationStatement.{u} →
    EisensteinCuspidalTestIntertwiningExpansionStatement.{u} →
      IntertwiningRestrictedCuspidalTestContinuationStatement.{u} →
        EisensteinCuspidalTestContinuedExpansionStatement.{u}

/-- The passage to standard parabolics and the continued expansion for standard parabolics give
the continued cuspidal-test expansion for every presented parabolic. -/
theorem eisensteinCuspidalTestContinuedExpansionStandardizationReduction :
    EisensteinCuspidalTestContinuedExpansionStandardizationReductionStatement.{u} := by
  classical
  intro hstd hexp F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU 𝓕 K hK h₀ hLevi N d
    rho hsmooth hcalc φ hKmax hrho hφ J hKJ
  obtain ⟨I, iota, m, E, φ', hφ', hE, hW, hMono, hreg, hroot, R₀, hR₀⟩ :=
    hstd F G P M U A p iU l a r hA hT hG hU 𝓕 K hK h₀ hLevi rho hsmooth hcalc φ hKmax hrho hφ
  let hAI := (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
  let hTI := 𝓕.maximalSplit.isSplitSubtorus.1
  have hdata := fun j => hexp F G 𝓕 K h₀ hKmax hLevi rho hsmooth hrho I (φ' j) (hφ' j) J
  choose k Φ L c D hmer hpoles R hR using hdata
  choose R' hR' using fun j => hreg (R j)
  choose! σ hσ s hs hL using hroot
  -- the terms of all standard expansions, enumerated
  let κ := Σ j : Fin m, Fin (k j)
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  -- the common domain, pulled back along `iota`
  let Dc : Set (ComplexCharacterParameter F P) := ⋂ x : κ, iota ⁻¹' D x.1
  have hDc : IsOpenDenseInCoordinates Dc :=
    isOpenDenseInCoordinates_iInter_of_finite fun x n e₀ =>
      (hmer x.1 x.2).isOpenDenseInCoordinates n (e₀.trans iota)
  have hDcsub : ∀ x : κ, Dc ⊆ iota ⁻¹' D x.1 := fun x => iInter_subset_of_subset x subset_rfl
  obtain ⟨hR₀le, hRle⟩ := le_max_zero_add_sum_abs R₀ R'
  refine ⟨Fintype.card κ, fun i => Φ (e.symm i).1 (e.symm i).2,
    fun i => L (e.symm i).1 (e.symm i).2 ∘ₗ iota.toLinearMap,
    fun i lam => E (e.symm i).1 lam * c (e.symm i).1 (e.symm i).2 (iota lam), Dc,
    fun i => ?_, fun i => ?_, max R₀ 0 + ∑ j, |R' j|, fun lam hlam ψ hψ g => ?_⟩
  · -- meromorphy in linear coordinates
    have hc := (hmer (e.symm i).1 (e.symm i).2).comp_linearEquiv iota
    let : FiniteDimensional ℂ (ComplexCharacterParameter F P) := hc.1
    have hEm := isMeromorphicInCoordinatesOn_univ (hE (e.symm i).1)
    exact (hEm.mul hc).congr_mono hDc (fun x hx => ⟨mem_univ x, hDcsub (e.symm i) hx⟩)
      fun _ _ => rfl
  · -- poles along the root hyperplanes of `P`
    have hc := (hpoles (e.symm i).1 (e.symm i).2).comp_linearEquiv_of_proportional iota σ s hσ
      hs hL
    have hEp : HasRootHyperplanePoles (r.rootFunctional hA hT) r.unipotentRoots
        (E (e.symm i).1) (iota ⁻¹' D (e.symm i).1) :=
      hasRootHyperplanePoles_of_differentiable (hE (e.symm i).1)
    exact (hEp.mul hc).mono (hDcsub (e.symm i))
  · -- agreement in the convergence region
    rw [hR₀ lam (ParabolicRootPresentation.IsRegularParameter.mono r hA hT hR₀le hlam) J ψ hψ g]
    let Y : ∀ j, Fin (k j) → ℂ := fun j i => 𝓕.leviPairing J (𝓕.constantTerm J
      ((𝓕.isIwasawaCompact_of_minimal h₀ J).parameterTwist (Φ j i) (L j i (iota lam)))) g ψ
    have hstep : ∀ j, E j lam * 𝓕.leviPairing J (𝓕.constantTerm J
        ((𝓕.isIwasawaCompact_of_minimal h₀ I).eisensteinSeries (φ' j) (iota lam))) g ψ =
        ∑ i, E j lam * c j i (iota lam) * Y j i := by
      intro j
      rw [hR j (iota lam) (hR' j lam (ParabolicRootPresentation.IsRegularParameter.mono r hA hT (hRle j) hlam)) ψ hψ g,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
    calc _ = ∑ j, ∑ i, E j lam * c j i (iota lam) * Y j i := Finset.sum_congr rfl fun j _ =>
          hstep j
      _ = ∑ x : κ, E x.1 lam * c x.1 x.2 (iota lam) * Y x.1 x.2 :=
          (Fintype.sum_sigma (fun x : κ => E x.1 lam * c x.1 x.2 (iota lam) * Y x.1 x.2)).symm
      _ = ∑ i : Fin (Fintype.card κ), E (e.symm i).1 lam *
            c (e.symm i).1 (e.symm i).2 (iota lam) * Y (e.symm i).1 (e.symm i).2 :=
          (e.symm.sum_comp (fun x : κ => E x.1 lam * c x.1 x.2 (iota lam) * Y x.1 x.2)).symm
      _ = _ := rfl

/-- The passage to standard parabolics, the tested constant-term formula and the restricted
continuation of the tested intertwining terms give the continued cuspidal-test expansion. -/
theorem eisensteinCuspidalTestContinuedExpansionReduction :
    EisensteinCuspidalTestContinuedExpansionReductionStatement.{u} := fun hstd hexp hcont =>
  eisensteinCuspidalTestContinuedExpansionStandardizationReduction hstd
    (eisensteinCuspidalTestStandardExpansionReduction hexp hcont)

end Langlands.Global
