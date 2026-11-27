import Langlands.Global.AdelicEisensteinCuspidalTestRootHyperplaneReduction
import Langlands.Global.AdelicIntertwiningElementaryChainStatement
import Langlands.Global.AdelicEisensteinConstantTermStatement
import Langlands.Global.AdelicRootHyperplaneReduction

/-! # Continued cuspidal-test expansions for standard parabolics from (6.18)

Bernstein–Lapid, §6.10, (6.18), with the intertwining operators continued as in Theorem 2.3 (3)
and §8.6, for a standard parabolic `P_I` and a maximal compact subgroup in good position. The
norm-one Levi tests of the constant term along `P_J` of `E(φ, λ)` are, in the range of
convergence, the sum of the tests of the intertwining terms `[M(w, λ) φ_w]_{wλ}` over the Weyl
elements `w` with target `P_J` that are positive on the simple roots of `M_I`; the tests of each
such term continue in `λ ∈ X^*(P_I) ⊗ ℂ` with poles along the root hyperplanes of `P_I`. Together
these give the continued expansion of the tests of `C_J E(φ, λ)` for standard `P_I`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Set
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic Langlands.Aubert.General.RationalPointFamily

attribute [local instance] StandardParabolicFamily.isClosedImmersion_p

/-- The continued cuspidal-test expansion for a standard parabolic (Bernstein–Lapid, §6.10,
(6.18), with Theorem 2.3 (3) and §8.6). Let `𝓕` be a standard parabolic family of a connected
reductive group `G` over a number field and `K` a maximal compact subgroup of `G(𝔸)` in good
position for `𝓕`. For every standard index `I`, every automorphic `φ` on `U_I(𝔸) M_I(F) \ G(𝔸)`
and every standard index `J` there are finitely many functions `Φ i` on `G(𝔸)`, complex linear
maps `L i : X^*(P_I) ⊗ ℂ → X^*(P_J) ⊗ ℂ` and scalar functions `c i` on `X^*(P_I) ⊗ ℂ`,
meromorphic in linear coordinates with one domain `D` and with poles along the hyperplanes of
the root forms of the roots of `A_I` in `U_I`, such that for `λ` sufficiently regular, every cusp
form `ψ` on `M_J(F) \ M_J(𝔸)` and every `g`, the norm-one Levi test of `C_J E(φ, λ)` is
`∑ i, c i λ · (C_J [Φ i]_{L i λ}(· g), ψ)`. -/
def EisensteinCuspidalTestStandardExpansionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (𝓕 : StandardParabolicFamily F G) [Fintype (relativeWeylGroup 𝓕.i)]
    [∀ J, Mono (CommGroupScheme.groupHom (𝓕.f J)).hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G))
    (h₀ : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K),
    IsMaximalCompactSubgroup F G K →
    (∀ J : StandardIndex F G 𝓕.i 𝓕.ν, IsMaximalCompactSubgroup F (𝓕.M J)
      (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom)) →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom), IsClosedSubgroup rho →
      ∀ (I : StandardIndex F G 𝓕.i 𝓕.ν) (φ : AdelicGroupPoints F G → ℂ),
        𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I φ →
        ∀ J : StandardIndex F G 𝓕.i 𝓕.ν,
          ∃ (k : ℕ) (Φ : Fin k → AdelicGroupPoints F G → ℂ)
            (L : Fin k → ComplexCharacterParameter F (𝓕.P I) →ₗ[ℂ]
              ComplexCharacterParameter F (𝓕.P J))
            (c : Fin k → ComplexCharacterParameter F (𝓕.P I) → ℂ)
            (D : Set (ComplexCharacterParameter F (𝓕.P I))),
            (∀ i, IsMeromorphicInCoordinatesOn (c i) D) ∧
            (∀ i, HasRootHyperplanePoles
              ((𝓕.rootPresentation I).rootFunctional
                (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
                𝓕.maximalSplit.isSplitSubtorus.1)
              (𝓕.rootPresentation I).unipotentRoots (c i) D) ∧
            ∃ R : ℝ, ∀ lam, (𝓕.rootPresentation I).IsRegularParameter
                (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
                𝓕.maximalSplit.isSplitSubtorus.1 R lam →
              ∀ ψ, 𝓕.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J ψ → ∀ g,
                𝓕.leviPairing J (𝓕.constantTerm J
                    ((𝓕.isIwasawaCompact_of_minimal h₀ I).eisensteinSeries φ lam)) g ψ =
                  ∑ i, c i lam * 𝓕.leviPairing J (𝓕.constantTerm J
                    ((𝓕.isIwasawaCompact_of_minimal h₀ J).parameterTwist (Φ i) (L i lam))) g ψ

/-- The tested constant-term formula (Bernstein–Lapid, §6.10, Lemma with (6.17) and (6.18),
tested by the pairings of (6.8)). In the setting of
`EisensteinCuspidalTestStandardExpansionStatement`, for every standard `I`, every automorphic
`φ` on `U_I(𝔸) M_I(F) \ G(𝔸)` and every standard `J` there are finitely many terms `t`, each
given by a standard index `I' t` with an inclusion `f t : P_{I' t} → P_I` over `G`, a rational
point `n t` normalizing the maximal split torus that presents an element `(n t, c t)` of
`W(P_{I' t}, P_J)` and maps the simple roots in `I` to positive roots, a retraction `π t` of the
Levi of `P_J`, and an automorphic function `φ' t` on `U_{I' t}(𝔸) M_{I' t}(F) \ G(𝔸)`, such that
for `λ` sufficiently regular, every cusp form `ψ` on `M_J(F) \ M_J(𝔸)` and every `g`, the
norm-one Levi test of `C_J E(φ, λ)` is the sum over `t` of the tests of the constant terms along
`P_J` of the intertwining integrals `[M(n t, λ) φ' t]_{(n t) λ}`, with `λ` restricted to
`P_{I' t}`. -/
def EisensteinCuspidalTestIntertwiningExpansionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (𝓕 : StandardParabolicFamily F G) [Fintype (relativeWeylGroup 𝓕.i)]
    [∀ J, Mono (CommGroupScheme.groupHom (𝓕.f J)).hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G))
    (h₀ : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K),
    IsMaximalCompactSubgroup F G K →
    (∀ J : StandardIndex F G 𝓕.i 𝓕.ν, IsMaximalCompactSubgroup F (𝓕.M J)
      (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom)) →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom), IsClosedSubgroup rho →
      ∀ (I : StandardIndex F G 𝓕.i 𝓕.ν) (φ : AdelicGroupPoints F G → ℂ),
        𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I φ →
        ∀ J : StandardIndex F G 𝓕.i 𝓕.ν,
          ∃ (k : ℕ) (I' : Fin k → StandardIndex F G 𝓕.i 𝓕.ν)
            (f : ∀ t, 𝓕.P (I' t) ⟶ 𝓕.P I) (n : Fin k → normalizerPoints 𝓕.i)
            (c : ∀ t, 𝓕.M J ⟶ 𝓕.M (I' t)) (π : Fin k → (𝓕.P J ⟶ 𝓕.M J))
            (φ' : Fin k → AdelicGroupPoints F G → ℂ),
            (∀ t, f t ≫ 𝓕.p I = 𝓕.p (I' t)) ∧
            (∀ t, IsWeylConjugation (𝓕.p (I' t)) (𝓕.l (I' t)) (𝓕.p J) (𝓕.l J) (n t).val
              (c t)) ∧
            (∀ t, 𝓕.l J ≫ π t = 𝟙 (𝓕.M J)) ∧
            (∀ t, ∀ α ∈ I.val, schemeWeylCharacterAction 𝓕.i (QuotientGroup.mk (n t)) α ∈
              positiveRelativeRoots 𝓕.i 𝓕.ν) ∧
            (∀ t, 𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho (I' t)
              (φ' t)) ∧
            ∃ R : ℝ, ∀ lam, (𝓕.rootPresentation I).IsRegularParameter
                (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
                𝓕.maximalSplit.isSplitSubtorus.1 R lam →
              ∀ ψ, 𝓕.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J ψ → ∀ g,
                𝓕.leviPairing J (𝓕.constantTerm J
                    ((𝓕.isIwasawaCompact_of_minimal h₀ I).eisensteinSeries φ lam)) g ψ =
                  ∑ t, 𝓕.leviPairing J (𝓕.constantTerm J
                    ((𝓕.isIwasawaCompact_of_minimal h₀ (I' t)).intertwiningIntegral
                      (𝓕.iU (I' t)) (𝓕.iU J ≫ 𝓕.p J) (n t).val (φ' t)
                      (parameterRestrict (f t) lam))) g ψ

/-- Continuation of the cuspidal tests of intertwining terms in parameters restricted from a
larger standard parabolic (derived from Bernstein–Lapid, Theorem 2.3 (3) and §8.6). In the
setting of `EisensteinCuspidalTestStandardExpansionStatement`, let `I' ≤ I` be standard indices
with the inclusion `f : P_{I'} → P_I` over `G`, let `(n, c)` be an element of `W(P_{I'}, P_J)`
given by a rational point `n` normalizing the maximal split torus whose Weyl element maps the
simple roots in `I` to positive roots, let `π` be a retraction of the Levi of `P_J`, and let `φ'`
be automorphic on `U_{I'}(𝔸) M_{I'}(F) \ G(𝔸)`. Then there are finitely many functions `Φ i` on
`G(𝔸)` and scalar functions `coeff i` on `X^*(P_I) ⊗ ℂ`, meromorphic in linear coordinates with
one domain `D` and with poles along the hyperplanes of the root forms of the roots of `A_I` in
`U_I`, such that for `λ ∈ X^*(P_I) ⊗ ℂ` sufficiently regular, every cusp form `ψ` on
`M_J(F) \ M_J(𝔸)` and every `g`, the norm-one Levi test of the constant term along `P_J` of
`[M(n, λ|) φ']_{nλ}` is `∑ i, coeff i λ · (C_J [Φ i]_{nλ}(· g), ψ)`, where `λ|` is the
restriction of `λ` to `P_{I'}` and `nλ` its Weyl transport to `P_J`. -/
def IntertwiningRestrictedCuspidalTestContinuationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (𝓕 : StandardParabolicFamily F G) [Fintype (relativeWeylGroup 𝓕.i)]
    [∀ J, Mono (CommGroupScheme.groupHom (𝓕.f J)).hom.hom.left]
    (K : Subgroup (AdelicGroupPoints F G))
    (h₀ : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K),
    IsMaximalCompactSubgroup F G K →
    (∀ J : StandardIndex F G 𝓕.i 𝓕.ν, IsMaximalCompactSubgroup F (𝓕.M J)
      (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom)) →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom), IsClosedSubgroup rho →
      ∀ (I I' J : StandardIndex F G 𝓕.i 𝓕.ν) (f : 𝓕.P I' ⟶ 𝓕.P I) (n : normalizerPoints 𝓕.i)
        (c : 𝓕.M J ⟶ 𝓕.M I') (π : 𝓕.P J ⟶ 𝓕.M J),
        f ≫ 𝓕.p I = 𝓕.p I' →
        IsWeylConjugation (𝓕.p I') (𝓕.l I') (𝓕.p J) (𝓕.l J) n.val c →
        𝓕.l J ≫ π = 𝟙 (𝓕.M J) →
        (∀ α ∈ I.val, schemeWeylCharacterAction 𝓕.i (QuotientGroup.mk n) α ∈
          positiveRelativeRoots 𝓕.i 𝓕.ν) →
        ∀ φ' : AdelicGroupPoints F G → ℂ,
          𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I' φ' →
          ∃ (k : ℕ) (Φ : Fin k → AdelicGroupPoints F G → ℂ)
            (coeff : Fin k → ComplexCharacterParameter F (𝓕.P I) → ℂ)
            (D : Set (ComplexCharacterParameter F (𝓕.P I))),
            (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) ∧
            (∀ i, HasRootHyperplanePoles
              ((𝓕.rootPresentation I).rootFunctional
                (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
                𝓕.maximalSplit.isSplitSubtorus.1)
              (𝓕.rootPresentation I).unipotentRoots (coeff i) D) ∧
            ∃ R : ℝ, ∀ lam, (𝓕.rootPresentation I).IsRegularParameter
                (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
                𝓕.maximalSplit.isSplitSubtorus.1 R lam →
              ∀ ψ, 𝓕.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J ψ → ∀ g,
                𝓕.leviPairing J (𝓕.constantTerm J
                    ((𝓕.isIwasawaCompact_of_minimal h₀ I').intertwiningIntegral
                      (𝓕.iU I') (𝓕.iU J ≫ 𝓕.p J) n.val φ' (parameterRestrict f lam))) g ψ =
                  ∑ i, coeff i lam * 𝓕.leviPairing J (𝓕.constantTerm J
                    ((𝓕.isIwasawaCompact_of_minimal h₀ J).parameterTwist (Φ i)
                      (weylParameter (𝓕.l I') c π (parameterRestrict f lam)))) g ψ

/-- The reduction of the standard continued cuspidal-test expansion to the tested
constant-term formula and the restricted continuation of the tested intertwining terms. -/
def EisensteinCuspidalTestStandardExpansionReductionStatement : Prop :=
  EisensteinCuspidalTestIntertwiningExpansionStatement.{u} →
    IntertwiningRestrictedCuspidalTestContinuationStatement.{u} →
      EisensteinCuspidalTestStandardExpansionStatement.{u}

section Lemmas

/-- A real number and the finitely many terms of a family are bounded by the sum of the
positive part of the first and the absolute values of the others. -/
theorem le_max_zero_add_sum_abs {k : ℕ} (R₀ : ℝ) (R : Fin k → ℝ) :
    R₀ ≤ max R₀ 0 + ∑ t, |R t| ∧ ∀ t, R t ≤ max R₀ 0 + ∑ t, |R t| := by
  have hsum : 0 ≤ ∑ t, |R t| := Finset.sum_nonneg fun t _ => abs_nonneg (R t)
  refine ⟨(le_max_left R₀ 0).trans (le_add_of_nonneg_right hsum), fun t => ?_⟩
  calc R t ≤ |R t| := le_abs_self (R t)
    _ ≤ ∑ t, |R t| := Finset.single_le_sum (fun i _ => abs_nonneg (R i)) (Finset.mem_univ t)
    _ ≤ max R₀ 0 + ∑ t, |R t| := le_add_of_nonneg_left (le_max_right R₀ 0)

end Lemmas

/-- The tested constant-term formula and the restricted continuation of the tested
intertwining terms give the continued cuspidal-test expansion for standard parabolics. -/
theorem eisensteinCuspidalTestStandardExpansionReduction :
    EisensteinCuspidalTestStandardExpansionReductionStatement.{u} := by
  classical
  intro hexp hcont F _ _ G _ _ _ 𝓕 _ _ K h₀ hKmax hLevi N d rho hsmooth hrho I φ hφ J
  obtain ⟨k, I', f, n, c, π, φ', hf, hW, hπ, hpos, hφ', R₀, hR₀⟩ :=
    hexp F G 𝓕 K h₀ hKmax hLevi rho hsmooth hrho I φ hφ J
  have hdata := fun t => hcont F G 𝓕 K h₀ hKmax hLevi rho hsmooth hrho I (I' t) J (f t) (n t)
    (c t) (π t) (hf t) (hW t) (hπ t) (hpos t) (φ' t) (hφ' t)
  choose m Φ coeff D hmer hpoles R hR using hdata
  -- the terms of all intertwining expansions, enumerated
  let κ := Σ t : Fin k, Fin (m t)
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  -- the common domain
  let Dc : Set (ComplexCharacterParameter F (𝓕.P I)) := ⋂ x : κ, D x.1
  have hDc : IsOpenDenseInCoordinates Dc :=
    isOpenDenseInCoordinates_iInter_of_finite fun x => (hmer x.1 x.2).isOpenDenseInCoordinates
  have hDcsub : ∀ x : κ, Dc ⊆ D x.1 := fun x => iInter_subset_of_subset x subset_rfl
  obtain ⟨hR₀le, hRle⟩ := le_max_zero_add_sum_abs R₀ R
  refine ⟨Fintype.card κ, fun i => Φ (e.symm i).1 (e.symm i).2,
    fun i => weylParameter (𝓕.l (I' (e.symm i).1)) (c (e.symm i).1) (π (e.symm i).1) ∘ₗ
      parameterRestrict (f (e.symm i).1),
    fun i => coeff (e.symm i).1 (e.symm i).2, Dc, fun i => ?_, fun i => ?_,
    max R₀ 0 + ∑ t, |R t|, fun lam hlam ψ hψ g => ?_⟩
  · exact (hmer _ _).congr_mono hDc (hDcsub (e.symm i)) fun _ _ => rfl
  · exact (hpoles _ _).mono (hDcsub (e.symm i))
  · let hA := (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
    let hT := 𝓕.maximalSplit.isSplitSubtorus.1
    rw [hR₀ lam (ParabolicRootPresentation.IsRegularParameter.mono (𝓕.rootPresentation I) hA hT hR₀le hlam) ψ hψ g]
    let X : ∀ t, Fin (m t) → ℂ := fun t i => 𝓕.leviPairing J (𝓕.constantTerm J
      ((𝓕.isIwasawaCompact_of_minimal h₀ J).parameterTwist (Φ t i)
        (weylParameter (𝓕.l (I' t)) (c t) (π t) (parameterRestrict (f t) lam)))) g ψ
    calc _ = ∑ t, ∑ i, coeff t i lam * X t i := Finset.sum_congr rfl fun t _ =>
          hR t lam (ParabolicRootPresentation.IsRegularParameter.mono (𝓕.rootPresentation I) hA hT (hRle t) hlam) ψ hψ g
      _ = ∑ x : κ, coeff x.1 x.2 lam * X x.1 x.2 := (Fintype.sum_sigma (fun x : κ => coeff x.1 x.2 lam * X x.1 x.2)).symm
      _ = ∑ i : Fin (Fintype.card κ), coeff (e.symm i).1 (e.symm i).2 lam *
            X (e.symm i).1 (e.symm i).2 :=
          (e.symm.sum_comp (fun x : κ => coeff x.1 x.2 lam * X x.1 x.2)).symm
      _ = _ := rfl

end Langlands.Global
