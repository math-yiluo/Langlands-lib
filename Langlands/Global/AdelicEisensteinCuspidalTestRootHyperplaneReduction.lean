import Langlands.Global.AdelicLeadingCuspidalInjectivityReduction
import Langlands.Global.AdelicEisensteinCuspidalTestRootHyperplaneStatement
import Langlands.Global.AdelicStandardConstantTermTwist
import Langlands.Analysis.Meromorphic.RootHyperplanePoles
import Langlands.Analysis.Meromorphic.ScalarIdentity

/-! # Root-hyperplane clearing of cuspidal tests from continued cuspidal expansions

Bernstein–Lapid, §6.10, (6.18), with the intertwining operators continued as in
Theorem 2.3 (3) and §8.6: the norm-one Levi tests of the standard constant terms of `E(φ, λ)`
are finite sums of tests of twists `[Φ_i]_{L_i λ}` of fixed functions with scalar
coefficients that have poles along root hyperplanes. Such an expansion gives
`EisensteinCuspidalTestRootHyperplaneStatement`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Set
open scoped CategoryTheory.MonObj TensorProduct Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

attribute [local instance] isClosedImmersion_p

omit [NumberField F] in
/-- The standard indices of a family form a finite type. -/
theorem finite_standardIndex_of_finite_simpleRoots : Finite (StandardIndex F G 𝓕.i 𝓕.ν) :=
  (𝓕.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots 𝓕.i 𝓕.ν).finite_subsets.to_subtype

end StandardParabolicFamily

attribute [local instance] StandardParabolicFamily.isClosedImmersion_p

/-- The cuspidal tests of `E(φ, λ)` expand through continued intertwining values
(Bernstein–Lapid, §6.10, (6.18), with Theorem 2.3 (3) and §8.6). In the setting of
`EisensteinCuspidalTestRootHyperplaneStatement`, for every standard `J` and with the Iwasawa
height of `P_J` for `K`, there are finitely many functions `Φ i` on `G(𝔸)`, complex linear maps
`L i : X^*(P) ⊗ ℂ → X^*(P_J) ⊗ ℂ` and scalar functions `c i` on `X^*(P) ⊗ ℂ`, meromorphic in
linear coordinates with one domain `D` and with poles along the hyperplanes of the root forms
`λ ↦ B(λ, β)`, `β` a root of `A` in the unipotent radical of `P`, such that for `λ` sufficiently
regular, every cusp form `ψ` on `M_J(F) \ M_J(𝔸)` and every `g`, the norm-one Levi test of
`C_J E(φ, λ)` is `∑ i, c i λ · (C_J [Φ i]_{L i λ}(· g), ψ)`. -/
def EisensteinCuspidalTestContinuedExpansionStatement : Prop :=
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
      (hK : IsIwasawaCompact p K),
      IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K →
      (∀ J : StandardIndex F G 𝓕.i 𝓕.ν, IsMaximalCompactSubgroup F (𝓕.M J)
        (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom)) →
      ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
        (hsmooth : SmoothOfRelativeDimension d G.X.hom)
        (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
        IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
        IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
          (K.comap (ofInfinite F G).toMonoidHom) rho φ →
        ∀ (J : StandardIndex F G 𝓕.i 𝓕.ν) (hKJ : IsIwasawaCompact (𝓕.p J) K),
          ∃ (k : ℕ) (Φ : Fin k → AdelicGroupPoints F G → ℂ)
            (L : Fin k → ComplexCharacterParameter F P →ₗ[ℂ]
              ComplexCharacterParameter F (𝓕.P J))
            (c : Fin k → ComplexCharacterParameter F P → ℂ)
            (D : Set (ComplexCharacterParameter F P)),
            (∀ i, IsMeromorphicInCoordinatesOn (c i) D) ∧
            (∀ i, HasRootHyperplanePoles (r.rootFunctional hA hT) r.unipotentRoots (c i) D) ∧
            ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
              ∀ ψ, 𝓕.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J ψ → ∀ g,
                𝓕.leviPairing J (𝓕.constantTerm J (hK.eisensteinSeries φ lam)) g ψ =
                  ∑ i, c i lam *
                    𝓕.leviPairing J (𝓕.constantTerm J (hKJ.parameterTwist (Φ i) (L i lam))) g ψ

/-- The reduction of `EisensteinCuspidalTestRootHyperplaneStatement` to continued cuspidal
expansions. -/
def EisensteinCuspidalTestRootHyperplaneReductionStatement : Prop :=
  EisensteinCuspidalTestContinuedExpansionStatement.{u} →
    EisensteinCuspidalTestRootHyperplaneStatement.{u}

section Lemmas

/-- An entire function on `ℂⁿ` is meromorphic with domain `ℂⁿ`. -/
private theorem isMeromorphicOn_univ_of_differentiable {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : Differentiable ℂ f) : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f univ :=
  ⟨isOpen_univ, dense_univ, isHolomorphicOn_of_differentiableOn hf.differentiableOn,
    fun s₀ => ⟨univ, isOpen_univ, isConnected_univ, mem_univ _, fun _ => 1, f,
      mdifferentiableOn_const, ⟨s₀, mem_univ _, one_ne_zero⟩,
      isHolomorphicOn_of_differentiableOn hf.differentiableOn, fun _ _ => one_smul ℂ _⟩⟩

/-- The height factor `λ ↦ exp ⟨b λ, H⟩` of a twist is entire along a linear map. -/
private theorem differentiable_exp_complexParameterPairing {F : Type u} [Field F] [NumberField F]
    {Q : GroupScheme (Spec (CommRingCat.of F))} {n : ℕ}
    (b : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F Q) (H : RealCharacterDual F Q) :
    Differentiable ℂ (fun s => Complex.exp (complexParameterPairing F Q (b s) H)) := by
  let ev : ComplexCharacterParameter F Q →ₗ[ℂ] ℂ :=
    { toFun := fun lam => complexParameterPairing F Q lam H
      map_add' := fun _ _ => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun _ _ => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  exact Complex.differentiable_exp.comp (ev.comp b).toContinuousLinearMap.differentiable

end Lemmas

/-- Continued cuspidal expansions give the root-hyperplane clearing of the cuspidal tests. -/
theorem eisensteinCuspidalTestRootHyperplaneReduction :
    EisensteinCuspidalTestRootHyperplaneReductionStatement.{u} := by
  classical
  intro hexp F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU 𝓕 K hK h₀ hLevi N d rho
    hsmooth hcalc φ hKmax hrho hφ
  have hfin := 𝓕.finite_standardIndex_of_finite_simpleRoots
  obtain ⟨m₀, ⟨e₀⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  have hfd : FiniteDimensional ℂ (ComplexCharacterParameter F P) :=
    FiniteDimensional.of_injective e₀.symm.toLinearMap e₀.symm.injective
  let hKJ : ∀ J : StandardIndex F G 𝓕.i 𝓕.ν, IsIwasawaCompact (𝓕.p J) K :=
    𝓕.isIwasawaCompact_of_minimal h₀
  have hdata := fun J => hexp F G P M U A p iU l a r hA hT hG hU 𝓕 K hK h₀ hLevi rho hsmooth
    hcalc φ hKmax hrho hφ J (hKJ J)
  choose k Φ L c D hmer hpoles R hR using hdata
  -- the common domain
  let Dc : Set (ComplexCharacterParameter F P) := ⋂ x : (Σ J, Fin (k J)), D x.1
  have hDc : IsOpenDenseInCoordinates Dc :=
    isOpenDenseInCoordinates_iInter_of_finite fun x =>
      (hmer x.1 x.2).isOpenDenseInCoordinates
  have hDcsub : ∀ J (i : Fin (k J)), Dc ⊆ D J := fun J i =>
    iInter_subset_of_subset ⟨J, i⟩ subset_rfl
  have hmerc : ∀ J i, IsMeromorphicInCoordinatesOn (c J i) Dc := fun J i =>
    (hmer J i).congr_mono hDc (hDcsub J i) fun _ _ => rfl
  have hpolesc : ∀ J i, HasRootHyperplanePoles (r.rootFunctional hA hT) r.unipotentRoots
      (c J i) Dc := fun J i => (hpoles J i).mono (hDcsub J i)
  -- the continued tests
  let τ : ∀ J : StandardIndex F G 𝓕.i 𝓕.ν, (AdelicGroupPoints F (𝓕.M J) → ℂ) →
      AdelicGroupPoints F G → Fin (k J) → ℂ :=
    fun J ψ g i => 𝓕.leviPairing J (𝓕.constantTerm J (Φ J i)) g ψ
  refine ⟨fun J ψ g lam => ∑ i, c J i lam * (τ J ψ g i * (hKJ J).heightPower (L J i lam) g),
    fun _ _ _ => Dc, fun J ψ hψ g => ⟨?_, ⟨R J, fun lam hlam => ?_⟩⟩, fun n e s₀ => ?_⟩
  · -- meromorphy in linear coordinates
    refine ⟨hfd, fun n e => ?_⟩
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (k J))),
        IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => c J i (e s) *
          (τ J ψ g i * (hKJ J).heightPower (L J i (e s)) g)) (e ⁻¹' Dc) := by
      intro i _
      have h1 := (hmerc J i).2 n e
      have h2 : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ)
          (fun s => τ J ψ g i * (hKJ J).heightPower (L J i (e s)) g) univ :=
        isMeromorphicOn_univ_of_differentiable ((differentiable_const _).mul
          (differentiable_exp_complexParameterPairing ((L J i).comp e.toLinearMap)
            ((hKJ J).height g)))
      have h3 := h1.mul h2
      rw [inter_univ] at h3
      exact h3
    have hsum := IsMeromorphicOn.sum Finset.univ (hDc n e).1 (hDc n e).2 hterm
    convert hsum using 1
    funext s
    simp only [Function.comp_apply, Finset.sum_apply]
  · -- agreement in the convergence region
    rw [hR J lam hlam ψ hψ g]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [𝓕.leviPairing_constantTerm_parameterTwist J J (hKJ J) le_rfl]
  · -- one root product for all tests
    obtain ⟨S, m, W, hSR, hW, hs₀, h, hh, hEq⟩ :=
      exists_rootPoleData_family (κ := Σ J : StandardIndex F G 𝓕.i 𝓕.ν, Fin (k J))
        (c := fun x => c x.1 x.2) (fun x => hpolesc x.1 x.2) n e s₀
    refine ⟨S, m, W, hSR, hW, hs₀, fun J ψ hψ g => ?_⟩
    refine ⟨fun s => ∑ i, h ⟨J, i⟩ s * (τ J ψ g i * (hKJ J).heightPower (L J i (e s)) g),
      ?_, fun s hs hsD => ?_⟩
    · refine DifferentiableOn.fun_sum fun i _ => (hh ⟨J, i⟩).mul ?_
      exact ((differentiable_const _).mul
        (differentiable_exp_complexParameterPairing ((L J i).comp e.toLinearMap)
          ((hKJ J).height g))).differentiableOn
    · simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hEq ⟨J, i⟩ s hs hsD]
      ring

end Langlands.Global
