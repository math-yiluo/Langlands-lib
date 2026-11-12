import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedCoefficients
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedFourierTransform
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecay

/-! # The Fourier transform `f ↦ f̂(ω, P)` for actual standard parabolic subgroups (VII.1)

For a connected reductive group `G` over a nonarchimedean local field, a maximal split torus, a
generic cocharacter and an actual standard parabolic `P = P_I(F) = M_I(F) ⋉ U_I(F) ⊇ P₀(F)`, this
module instantiates the Library's `inducedFourierTransform` on actual rational points:
`rationalInducedFourierTransform` is Waldspurger's `f ↦ f̂(ω, P) = d(ω) π(f̌)` from the
Harish-Chandra Schwartz space `C(G)` (`RationalSchwartzSpace`) to `L(ω, P)`, for an irreducible
representation `ω` of `M_I(F)`, square integrable modulo a central subgroup and tempered. It
proves Lemma VII.1.1 (i)–(iii) on actual points, and the uniqueness of `f̂(ω, P)` given (ii).

The structural inputs are checked on actual points: compact open subgroups are cofinal in
`M_I(F)` (`compactOpenCofinal_standardLevi`), `Ξ(g⁻¹) = Ξ(g)` (Lemma II.1.4), `σ(g⁻¹) = σ(g)`,
the tempered growth of `I_P^G ω` (Lemma III.2.3) and the translation weights (Lemma II.1.2).
The conclusion of Lemma II.1.5 for the Haar measure is a hypothesis (`hsw`).
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

include hKc in
/-- Compact open subgroups are cofinal in `M_I(F)`: `K ∩ M_I(F)` is a compact open subgroup. -/
theorem compactOpenCofinal_standardLevi : CompactOpenCofinal 𝐌 := by
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν)
    (J := RationalPointFamily.rootSet i ν I) hKc
  have : Nonempty (CompactOpenSubgroup 𝐌) :=
    ⟨⟨K.comap (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)).subtype
      continuous_subtype_val, isCompact_iff_compactSpace.mpr this⟩⟩
  exact CompactOpenSubgroup.cofinal (G := 𝐌)

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (hρ : IsClosedSubgroup ρ)
  (hKρ : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) ρ)
  (hM : IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    ((K : Subgroup (rationalPoints G)).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))))
  (A : SmoothRep.{0, u, uV} ℂ 𝐌)
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (μM : Measure (𝐌 ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM)
  (hirr : A.representation.IsIrreducible)
  (hTA : IsRationalLeviTempered hKc ρ hM A)
  {mu : Measure (rationalPoints G)} [mu.IsMulLeftInvariant] [mu.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight mu (rationalXi hKc hPK) (rationalHeight (F := F) ρ))

/-- **Waldspurger's Fourier transform `f ↦ f̂(ω, P)` on actual rational points** (VII.1, printed
p. 313): for the actual standard parabolic `P = P_I(F) = M_I(F) ⋉ U_I(F)`, an irreducible
representation `ω = A` of `M_I(F)`, square integrable modulo a central subgroup `C`, tempered for
`Ξ^{M_I}` and `σ` (`hTA`), and `f ∈ C(G)` (`RationalSchwartzSpace`),
`f̂(ω, P) = d(ω) π(f̌) ∈ L(ω, P)`, `π = I_P^G ω`, `d(ω)` the formal degree. It is the Library's
`inducedFourierTransform` on the actual data of `P_I(F)`; `hsw` is the conclusion of Lemma II.1.5
for the Haar measure `mu`. -/
def rationalInducedFourierTransform :
    RationalSchwartzSpace hKc hPK ρ →ₗ[ℂ]
      productInducedCoefficientObject (G := rationalPoints G)
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  haveI : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  inducedFourierTransform (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    K hKc (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    A (compactOpenCofinal_standardLevi I hKc) C hC μM hsq hirr
    (rationalL2Weights K.isOpen hKc hPK ρ hsw)
    (rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hν
      (RationalPointFamily.rootSet_subset i ν I) I rfl K hKc hPK hM hρ hKρ A hsq.1 hTA)
    (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ)

/-- **Lemma VII.1.1 (i) on actual points**: `(ρ(g₁) λ(g₂) f)^(ω, P) = (π(g₁) ⊗ π̌(g₂)) f̂(ω, P)`
for the two-sided translation `Space.translate` of `C(G)` and the action of `G(F) × G(F)` on
`L(ω, P)`. -/
theorem rationalInducedFourierTransform_translate (g₁ g₂ : rationalPoints G)
    (f : RationalSchwartzSpace hKc hPK ρ) :
    rationalInducedFourierTransform hG hi hν I hKc hPK ρ hρ hKρ hM A C hC μM hsq hirr hTA hsw
        (Space.translate (rationalTranslationWeights K.isOpen hKc hPK ρ) g₁ g₂ f) =
      (productInducedCoefficientObject (G := rationalPoints G)
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A).representation
        (g₁, g₂) (rationalInducedFourierTransform hG hi hν I hKc hPK ρ hρ hKρ hM A C hC μM hsq
          hirr hTA hsw f) := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have h := inducedFourierTransform_translate (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    K hKc (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    A (compactOpenCofinal_standardLevi I hKc) C hC μM hsq hirr
    (rationalL2Weights K.isOpen hKc hPK ρ hsw)
    (rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hν
      (RationalPointFamily.rootSet_subset i ν I) I rfl K hKc hPK hM hρ hKρ A hsq.1 hTA)
    (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ)
    (rationalTranslationWeights K.isOpen hKc hPK ρ) g₁ g₂ f
  unfold rationalInducedFourierTransform
  with_reducible_and_instances exact h

/-- **Lemma VII.1.1 (iii) on actual points**: `(E_P^G f̂(ω, P))(g) = d(ω) θ_π(λ(g) f̌)`, where
`θ_π = schwartzCharacter` is the character of `π = I_P^G ω` on `C(G)`, `f̌(x) = f(x⁻¹)`
(`Space.check`) and `λ(g)` the left translation (`Space.translate … 1 g`). -/
theorem rationalInducedCoefficientMap_rationalInducedFourierTransform
    (f : RationalSchwartzSpace hKc hPK ρ) (g : rationalPoints G) :
    rationalInducedCoefficientMap hG hi hν I hKc hPK A hsq.1
        (rationalInducedFourierTransform hG hi hν I hKc hPK ρ hρ hKρ hM A C hC μM hsq hirr hTA hsw
          f) g =
      representationFormalDegree C hC μM (compactOpenCofinal_standardLevi I hKc) hsq hirr *
        (haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
        haveI : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
        schwartzCharacter (rationalL2Weights K.isOpen hKc hPK ρ hsw)
          (CompactInduction.induced_isAdmissible (G := rationalPoints G)
            (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
            (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) K hKc
            (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK) A
            (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
            hsq.1)
          (rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hν
            (RationalPointFamily.rootSet_subset i ν I) I rfl K hKc hPK hM hρ hKρ A hsq.1 hTA)
          (Space.translate (rationalTranslationWeights K.isOpen hKc hPK ρ) 1 g
            (Space.check (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ)
              f))) := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have h := coefficientMap_inducedFourierTransform (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    K hKc (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    A (compactOpenCofinal_standardLevi I hKc) C hC μM hsq hirr
    (rationalL2Weights K.isOpen hKc hPK ρ hsw)
    (rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hν
      (RationalPointFamily.rootSet_subset i ν I) I rfl K hKc hPK hM hρ hKρ A hsq.1 hTA)
    (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ)
    (rationalTranslationWeights K.isOpen hKc hPK ρ) f g
  unfold rationalInducedFourierTransform rationalInducedCoefficientMap
  with_reducible_and_instances exact h

/-- **Lemma VII.1.1 (ii) on actual points**: `(E_P^G ψ, f)_G = (ψ, f̂(ω, P))` for
`ψ ∈ L(ω, P)` and `f ∈ C(G)`, where `(φ₁, φ₂)_G = ∫_G conj(φ₁) φ₂ d(mu)` and `( , )` is the
product of V.2 on `L(ω, P)` (`CompactInduction.formalDegreeProductForm`). -/
theorem integral_conj_rationalInducedCoefficientMap_mul_eq_inner [mu.IsInvInvariant]
    (ψ : productInducedCoefficientObject (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A)
    (f : RationalSchwartzSpace hKc hPK ρ) :
    ∫ g, conj (rationalInducedCoefficientMap hG hi hν I hKc hPK A hsq.1 ψ g) * f g ∂mu =
      (haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
      CompactInduction.formalDegreeProductForm (G := rationalPoints G)
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
        (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
        (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
        (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
        (modularCharacter_standardParabolicPoints hG hi hν I rfl
          (RationalPointFamily.rootSet_subset i ν I))
        A (compactOpenCofinal_standardLevi I hKc) C hC μM hsq hirr).inner ψ
        (rationalInducedFourierTransform hG hi hν I hKc hPK ρ hρ hKρ hM A C hC μM hsq hirr hTA
          hsw f) := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have h := integral_conj_coefficientMap_mul_eq_inner (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    K hKc (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    A (compactOpenCofinal_standardLevi I hKc) C hC μM hsq hirr
    (rationalL2Weights K.isOpen hKc hPK ρ hsw)
    (rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hν
      (RationalPointFamily.rootSet_subset i ν I) I rfl K hKc hPK hM hρ hKρ A hsq.1 hTA)
    (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ) ψ f
  unfold rationalInducedFourierTransform rationalInducedCoefficientMap
  with_reducible_and_instances exact h

/-- **`f̂(ω, P)` is determined by Lemma VII.1.1 (ii)** on actual points: if
`(E_P^G ψ, f)_G = (ψ, φ)` for every `ψ ∈ L(ω, P)`, then `φ = f̂(ω, P)`. -/
theorem rationalInducedFourierTransform_eq_of_forall_integral [mu.IsInvInvariant]
    (f : RationalSchwartzSpace hKc hPK ρ)
    (φ : productInducedCoefficientObject (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A)
    (hφ : ∀ ψ, ∫ g, conj (rationalInducedCoefficientMap hG hi hν I hKc hPK A hsq.1 ψ g) * f g ∂mu =
      (haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
      CompactInduction.formalDegreeProductForm (G := rationalPoints G)
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
        (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
        (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
        (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
        (modularCharacter_standardParabolicPoints hG hi hν I rfl
          (RationalPointFamily.rootSet_subset i ν I))
        A (compactOpenCofinal_standardLevi I hKc) C hC μM hsq hirr).inner ψ φ) :
    rationalInducedFourierTransform hG hi hν I hKc hPK ρ hρ hKρ hM A C hC μM hsq hirr hTA hsw f =
      φ := by
  let B := (haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
    CompactInduction.formalDegreeProductForm (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
      (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
      (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
      (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
      (modularCharacter_standardParabolicPoints hG hi hν I rfl
        (RationalPointFamily.rootSet_subset i ν I))
      A (compactOpenCofinal_standardLevi I hKc) C hC μM hsq hirr)
  set Φ := rationalInducedFourierTransform hG hi hν I hKc hPK ρ hρ hKρ hM A C hC μM hsq hirr hTA
    hsw f with hΦ
  have hinner : ∀ ψ, B.inner ψ Φ = B.inner ψ φ := fun ψ =>
    (integral_conj_rationalInducedCoefficientMap_mul_eq_inner hG hi hν I hKc hPK ρ hρ hKρ hM A C
      hC μM hsq hirr hTA hsw ψ f).symm.trans (hφ ψ)
  let := B.toInnerProductCore
  have hzero : B.inner (Φ - φ) (Φ - φ) = 0 := by
    rw [InnerProductSpace.Core.inner_sub_right, hinner, sub_self]
  exact sub_eq_zero.mp (B.definite _ hzero)

end Langlands.HarishChandraSchwartz
