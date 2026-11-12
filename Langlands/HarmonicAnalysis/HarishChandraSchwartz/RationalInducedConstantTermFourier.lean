import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFourierOrbitSmoothness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientConvergence
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalWavePacketOrthogonality

/-! # Lemma VII.1.2 on actual points, and functions with vanishing constant term

For a connected reductive group `G` over a nonarchimedean local field and an actual standard
parabolic `P = P_I(F) = M_I(F) ⋉ U_I(F) ⊇ P₀(F)`, this module instantiates on actual rational
points the Library's `InducedConstantTermFourier`, `InducedCoefficientConvergence` and
`CuspidalWavePacketOrthogonality`:

* `integrable_rationalCoefficientPairingIntegrand`: the absolute convergence of
  `∫_G ∫_K conj⟨ψ(k g, k)⟩ f(g) dk dg` in the proof of Lemma VII.1.2, from Corollary III.1.2 for
  `M_I` (hypothesis `hcoeff`) and Lemma II.1.5 for `G` (`hsw`). This is the hypothesis `hint`
  of `RationalFourierOrbitSmoothness` and `RationalInducedOrbitWavePacketOrthogonality`;
* `rationalConstantTermInducedFourierTransform`: Waldspurger's `f̂^{(P),Ind}(ω) ∈ L(ω, P)`,
  `(g₁, g₂) ↦ [f^{(P),Ind}(g₁, g₂)]^(ω, M)`, built from the actual constant term
  `rationalConstantTerm`;
* `rationalInducedFourierTransform_eq_rationalConstantTermInducedFourierTransform`: Lemma VII.1.2,
  `f̂(ω, P) = f̂^{(P),Ind}(ω)`;
* `rationalInducedFourierTransform_eq_zero_of_rationalConstantTerm_eq_zero`,
  `rationalFourierOrbitSection_eq_zero_of_rationalConstantTerm_eq_zero` and
  `pairing_rationalInducedOrbitWavePacket_eq_zero_of_rationalConstantTerm_eq_zero`: if
  `(ρ(g₁) λ(g₂) f)^{(P)} = 0` for all `g₁, g₂`, then `f̂(ω, P) = 0`, `ψ_f[O, P] = 0` and
  `(f_ψ, f)_G = 0` for every wave packet `f_ψ` on `O` (first sentence of the proof of
  Lemma VIII.2.1 and the vanishing in the proof of Lemma VIII.2.3).
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

-- The root set `J` of `I`.
set_option hygiene false in
local notation "𝐉" => RationalPointFamily.rootSet i ν I

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (hM : IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν 𝐉))
    ((K : Subgroup (rationalPoints G)).subgroupOf (standardLeviPoints i ν 𝐉)))

section Convergence

/-- **Absolute convergence in the proof of Lemma VII.1.2, on actual points** (printed p. 315,
"Il résulte de la preuve du Lemme VI.2.2 et du Lemme II.1.5 que cette dernière intégrale est
absolument convergente"): for a smooth representation `A` of `M_I(F)` whose coefficients are
bounded by multiples of `Ξ^{M_I}` (Corollary III.1.2, hypothesis `hcoeff`), the conclusion of
Lemma II.1.5 for `G` (`hsw`), `ψ ∈ L(A, P)` and `f ∈ C(G)`, the function
`(g, k) ↦ conj⟨ψ(k g, k)⟩ f(g)` is integrable on `G(F) × K`. It is the Library's
`integrable_coefficientPairingIntegrand` with the actual `LeviData` of `P_I(F)`. -/
theorem integrable_rationalCoefficientPairingIntegrand (A : SmoothRep.{0, u, uV} ℂ 𝐌)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    {μG : Measure (rationalPoints G)} [SFinite μG]
    (hsw : SquareIntegrableWeight μG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (ψ : productInducedCoefficientObject (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν 𝐉) A)
    (f : RationalSchwartzSpace hKc hPK ρ) :
    Integrable
      (fun x : rationalPoints G × K => conj (CompactInduction.integrand
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν 𝐉) A K x.1 ψ x.2) * f x.1)
      (μG.prod (CompactInduction.measure K hKc)) := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := 𝐉) hKc
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have h := integrable_coefficientPairingIntegrand (G := rationalPoints G)
    (M := standardLeviPoints i ν 𝐉)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν 𝐉) A K hKc
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviData hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc) hPK hM
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp) hcoeff
    (rationalL2Weights K.isOpen hKc hPK ρ hsw) ψ f
  unfold coefficientPairingIntegrand at h
  with_reducible_and_instances exact h

include hG hi hν in
/-- Lemma II.1.5 for `M_I` in the form `L2Weights`: `Ξ^{M_I} > 0`, `σ ≥ 0`, and
`∫_{M_I} Ξ^{M_I}(m)² (1 + σ(m))^{-d} dm < ∞` for some `d`. -/
theorem rationalLeviL2Weights {μL : Measure 𝐌}
    (hswM : SquareIntegrableWeight μL (rationalLeviXi hKc hM)
      (fun m => rationalHeight (F := F) ρ m)) :
    L2Weights μL (rationalLeviXi hKc hM) (fun m => rationalHeight (F := F) ρ m) := by
  obtain ⟨d, hd⟩ := hswM
  exact ⟨rationalLeviXi_pos K.isOpen hKc hG hi hν (RationalPointFamily.rootSet_subset i ν I) hM,
    fun m => rationalHeight_nonneg ρ m, ⟨d, hd⟩⟩

end Convergence

section Representative

variable (hρ : IsClosedSubgroup ρ)
  (hKρ : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) ρ)
  (A : SmoothRep.{0, u, uV} ℂ 𝐌)
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (μM : Measure (𝐌 ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM)
  (hirr : A.representation.IsIrreducible)
  (hTA : IsRationalLeviTempered hKc ρ hM A)
  {μL : Measure 𝐌} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant]
  (hswM : SquareIntegrableWeight μL (rationalLeviXi hKc hM)
    (fun m => rationalHeight (F := F) ρ m))
  (νU : Measure (standardUnipotentPoints i ν 𝐉)) [νU.IsHaarMeasure] [νU.IsMulRightInvariant]
  (hE : ConstantTermEstimate νU (standardUnipotentModulus i ν (RationalPointFamily.rootSet i ν I))
    (rationalXi hKc hPK) (rationalHeight (F := F) ρ) (rationalLeviXi hKc hM)
    (fun m => rationalHeight (F := F) ρ m))

/-- **Waldspurger's `f̂^{(P),Ind}(ω)` on actual rational points** (VII.1, printed p. 315, before
Lemma VII.1.2): for the actual standard parabolic `P = P_I(F)`, an irreducible representation
`ω = A` of `M_I(F)`, square integrable modulo a central subgroup `C` and tempered (`hTA`), and
`f ∈ C(G)`, the element of `L(ω, P)` given by `(g₁, g₂) ↦ [f^{(P),Ind}(g₁, g₂)]^(ω, M)`, where
`f^{(P),Ind}(g₁, g₂) = (ρ(g₁) λ(g₂) f)^{(P)} ∈ C(M_I)` is the actual constant term
(`rationalConstantTerm`, which needs the conclusion `hE` of Proposition II.4.5) and
`φ ↦ φ^(ω, M) = d(ω) ω(φ̌)` is the Fourier transform of `C(M_I)`, with `d(ω)` the formal degree.
It is the Library's `constantTermInducedFourierTransform` on the actual data of `P_I(F)`;
`hswM` is the conclusion of Lemma II.1.5 for `M_I` and the Haar measure `μL`. -/
def rationalConstantTermInducedFourierTransform (f : RationalSchwartzSpace hKc hPK ρ) :
    productInducedCoefficientObject (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν 𝐉) A :=
  haveI : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  haveI : Nonempty (CompactOpenSubgroup 𝐌) :=
    haveI := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := 𝐉) hKc
    ⟨⟨K.comap (standardLeviPoints i ν 𝐉).subtype continuous_subtype_val,
      isCompact_iff_compactSpace.mpr this⟩⟩
  constantTermInducedFourierTransform (G := rationalPoints G) (M := standardLeviPoints i ν 𝐉)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν 𝐉)
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl) A
    (rationalLeviL2Weights hG hi hν I hKc ρ hM hswM) hsq.1 hTA
    (rationalLeviXi_inv hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc hM)
    (fun m => rationalHeight_inv ρ m)
    (representationFormalDegree C hC μM (compactOpenCofinal_standardLevi I hKc) hsq hirr)
    (rationalConstantTermData νU) (rationalIsConjModulus νU) hE
    (rationalTranslationWeights K.isOpen hKc hPK ρ)
    (rationalLeviTranslationWeights hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen
      hKc hM ρ) f

/-- The value of `f̂^{(P),Ind}(ω)` at `(g₁, g₂)` is the Fourier transform at `ω` of the actual
constant term `(ρ(g₁) λ(g₂) f)^{(P)}`. -/
theorem eval_rationalConstantTermInducedFourierTransform (f : RationalSchwartzSpace hKc hPK ρ)
    (g₁ g₂ : rationalPoints G) :
    Induction.eval
        ((standardParabolicPoints i ν 𝐉).prod (standardParabolicPoints i ν 𝐉))
        (inducingRepresentation
          ((isSemidirectDecomposition_standard hG hi hν
            (RationalPointFamily.rootSet_subset i ν I)).prod
            (isSemidirectDecomposition_standard hG hi hν
              (RationalPointFamily.rootSet_subset i ν I)))
          ((isClosed_standardUnipotentPoints i ν 𝐉).prod (isClosed_standardUnipotentPoints i ν 𝐉))
          (productLeviObject A A.contragredient))
        (rationalConstantTermInducedFourierTransform hG hi hν I hKc hPK ρ hM A C hC μM hsq hirr
          hTA hswM νU hE f) (g₁, g₂) =
      (haveI : Nonempty (CompactOpenSubgroup 𝐌) :=
        haveI := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := 𝐉) hKc
        ⟨⟨K.comap (standardLeviPoints i ν 𝐉).subtype continuous_subtype_val,
          isCompact_iff_compactSpace.mpr this⟩⟩
      coefficientFourierTransform A (rationalLeviL2Weights hG hi hν I hKc ρ hM hswM) hsq.1 hTA
        (rationalLeviXi_inv hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc hM)
        (fun m => rationalHeight_inv ρ m)
        (representationFormalDegree C hC μM (compactOpenCofinal_standardLevi I hKc) hsq hirr)
        (rationalConstantTerm K.isOpen hKc hPK hM ρ νU hG hi hν
          (RationalPointFamily.rootSet_subset i ν I) hE
          (Space.translate (rationalTranslationWeights K.isOpen hKc hPK ρ) g₁ g₂ f))) :=
  rfl

variable {μG : Measure (rationalPoints G)} [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight μG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
  [μG.IsInvInvariant] [SigmaFinite μG]
  (hμK : μG (K : Set (rationalPoints G)) = 1)
  [MeasurableInv 𝐌] [μL.IsInvInvariant] [SFinite μL] [SFinite νU]
  (hPKiw : ∀ (m : standardLeviPoints i ν 𝐉) (n : standardUnipotentPoints i ν 𝐉),
    (m : rationalPoints G) * n ∈ K ↔ (m : rationalPoints G) ∈ K ∧ (n : rationalPoints G) ∈ K)
  (hMK : μL {m : 𝐌 | (m : rationalPoints G) ∈ K} = 1)
  (hUK : νU {n : standardUnipotentPoints i ν 𝐉 | (n : rationalPoints G) ∈ K} = 1)

include hμK hPKiw hMK hUK in
/-- **Waldspurger, Lemma VII.1.2 on actual rational points** (printed p. 315):
`f̂(ω, P) = f̂^{(P),Ind}(ω)` for `f ∈ C(G)`, the actual standard parabolic `P = P_I(F)` and `ω = A`
as in `rationalInducedFourierTransform`, given Corollary III.1.2 for `ω` (`hcoeff`), the
conclusions of Lemma II.1.5 for `G` and `M_I` (`hsw`, `hswM`) and of Proposition II.4.5 (`hE`),
the normalizations `mes(K) = mes(M_I ∩ K) = mes(U_I ∩ K) = 1` (`hμK`, `hMK`, `hUK`) and
`P ∩ K = (M_I ∩ K)(U_I ∩ K)` (`hPKiw`). The absolute convergence used in the proof is
`integrable_rationalCoefficientPairingIntegrand`. -/
theorem rationalInducedFourierTransform_eq_rationalConstantTermInducedFourierTransform
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (f : RationalSchwartzSpace hKc hPK ρ) :
    rationalInducedFourierTransform hG hi hν I hKc hPK ρ hρ hKρ hM A C hC μM hsq hirr hTA hsw f =
      rationalConstantTermInducedFourierTransform hG hi hν I hKc hPK ρ hM A C hC μM hsq hirr hTA
        hswM νU hE f := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := 𝐉) hKc
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have : Nonempty (CompactOpenSubgroup 𝐌) :=
    ⟨⟨K.comap (standardLeviPoints i ν 𝐉).subtype continuous_subtype_val,
      isCompact_iff_compactSpace.mpr ‹_›⟩⟩
  have h := inducedFourierTransform_eq_constantTermInducedFourierTransform
    (G := rationalPoints G) (M := standardLeviPoints i ν 𝐉)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν 𝐉)
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
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviL2Weights hG hi hν I hKc ρ hM hswM) hTA
    (rationalLeviXi_inv hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc hM)
    (fun m => rationalHeight_inv ρ m)
    (rationalConstantTermData νU) (rationalIsConjModulus νU) hE
    (rationalTranslationWeights K.isOpen hKc hPK ρ)
    (rationalLeviTranslationWeights hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen
      hKc hM ρ)
    hμK hPKiw hMK hUK f
    (fun ψ => integrable_rationalCoefficientPairingIntegrand hG hi hν I hKc hPK ρ hM A hcoeff hsw
      ψ f)
  unfold rationalInducedFourierTransform rationalConstantTermInducedFourierTransform
  with_reducible_and_instances exact h

include hswM hμK hPKiw hMK hUK in
/-- **`f̂(ω, P) = 0` when the constant terms of the translates of `f` vanish** (Lemma VII.1.2 and
the first sentence of the proof of Lemma VIII.2.1, printed p. 321, for one `P`): under the
hypotheses of `rationalInducedFourierTransform_eq_rationalConstantTermInducedFourierTransform`,
if `(ρ(g₁) λ(g₂) f)^{(P)} = 0` for all `g₁, g₂ ∈ G(F)` (`h0`, with the actual constant term
`rationalConstantTerm`), then `f̂(ω, P) = 0`. -/
theorem rationalInducedFourierTransform_eq_zero_of_rationalConstantTerm_eq_zero
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (f : RationalSchwartzSpace hKc hPK ρ)
    (h0 : ∀ g₁ g₂ : rationalPoints G,
      rationalConstantTerm K.isOpen hKc hPK hM ρ νU hG hi hν
        (RationalPointFamily.rootSet_subset i ν I) hE
        (Space.translate (rationalTranslationWeights K.isOpen hKc hPK ρ) g₁ g₂ f) = 0) :
    rationalInducedFourierTransform hG hi hν I hKc hPK ρ hρ hKρ hM A C hC μM hsq hirr hTA hsw f =
      0 := by
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have : Nonempty (CompactOpenSubgroup 𝐌) :=
    haveI := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := 𝐉) hKc
    ⟨⟨K.comap (standardLeviPoints i ν 𝐉).subtype continuous_subtype_val,
      isCompact_iff_compactSpace.mpr this⟩⟩
  have h := constantTermInducedFourierTransform_eq_zero (G := rationalPoints G)
    (M := standardLeviPoints i ν 𝐉)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν 𝐉)
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl) A
    (rationalLeviL2Weights hG hi hν I hKc ρ hM hswM) hsq.1 hTA
    (rationalLeviXi_inv hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc hM)
    (fun m => rationalHeight_inv ρ m)
    (representationFormalDegree C hC μM (compactOpenCofinal_standardLevi I hKc) hsq hirr)
    (rationalConstantTermData νU) (rationalIsConjModulus νU) hE
    (rationalTranslationWeights K.isOpen hKc hPK ρ)
    (rationalLeviTranslationWeights hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen
      hKc hM ρ) f (fun x => h0 x.1 x.2)
  refine (rationalInducedFourierTransform_eq_rationalConstantTermInducedFourierTransform hG hi hν I
    hKc hPK ρ hM hρ hKρ A C hC μM hsq hirr hTA hswM νU hE hsw hμK hPKiw hMK hUK hcoeff f).trans ?_
  unfold rationalConstantTermInducedFourierTransform
  with_reducible_and_instances exact h

end Representative

section Orbit

variable (hρ : IsClosedSubgroup ρ)
  (hKρ : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) ρ)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (μM : Measure (𝐌 ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μM)
  (hTA : ∀ A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π,
    IsRationalLeviTempered hKc ρ hM A.val.obj)
  {μL : Measure 𝐌} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant]
  (hswM : SquareIntegrableWeight μL (rationalLeviXi hKc hM)
    (fun m => rationalHeight (F := F) ρ m))
  (νU : Measure (standardUnipotentPoints i ν 𝐉)) [νU.IsHaarMeasure] [νU.IsMulRightInvariant]
  (hE : ConstantTermEstimate νU (standardUnipotentModulus i ν (RationalPointFamily.rootSet i ν I))
    (rationalXi hKc hPK) (rationalHeight (F := F) ρ) (rationalLeviXi hKc hM)
    (fun m => rationalHeight (F := F) ρ m))
  {μG : Measure (rationalPoints G)} [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight μG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
  [μG.IsInvInvariant] [SigmaFinite μG]
  (hμK : μG (K : Set (rationalPoints G)) = 1)
  [MeasurableInv 𝐌] [μL.IsInvInvariant] [SFinite μL] [SFinite νU]
  (hPKiw : ∀ (m : standardLeviPoints i ν 𝐉) (n : standardUnipotentPoints i ν 𝐉),
    (m : rationalPoints G) * n ∈ K ↔ (m : rationalPoints G) ∈ K ∧ (n : rationalPoints G) ∈ K)
  (hMK : μL {m : 𝐌 | (m : rationalPoints G) ∈ K} = 1)
  (hUK : νU {n : standardUnipotentPoints i ν 𝐉 | (n : rationalPoints G) ∈ K} = 1)
  (hcoeffA : ∀ A : UnitaryOrbitRepresentative
      (RationalPointFamily.leviRationalNormCharacters i ν I) π,
    ∀ (v : A.val.obj) (ℓ : SmoothDual A.val.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (A.val.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)

include hswM hμK hPKiw hMK hUK hcoeffA in
/-- **`ψ_f[O, P] = 0` when the constant terms of the translates of `f` vanish**: under the
hypotheses of Lemma VII.1.2
(`rationalInducedFourierTransform_eq_rationalConstantTermInducedFourierTransform`) at every
representative `A` of the unitary unramified orbit `O` of `π` (Corollary III.1.2 for each `A` is
`hcoeffA`), if `(ρ(g₁) λ(g₂) f)^{(P)} = 0` for all `g₁, g₂ ∈ G(F)`, then the section
`ψ_f[O, P] : ω ↦ f̂(ω, P)` (`rationalFourierOrbitSection`) vanishes. -/
theorem rationalFourierOrbitSection_eq_zero_of_rationalConstantTerm_eq_zero
    (f : RationalSchwartzSpace hKc hPK ρ)
    (h0 : ∀ g₁ g₂ : rationalPoints G,
      rationalConstantTerm K.isOpen hKc hPK hM ρ νU hG hi hν
        (RationalPointFamily.rootSet_subset i ν I) hE
        (Space.translate (rationalTranslationWeights K.isOpen hKc hPK ρ) g₁ g₂ f) = 0) :
    rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw f = 0 := by
  funext A
  rw [rationalFourierOrbitSection_apply]
  exact rationalInducedFourierTransform_eq_zero_of_rationalConstantTerm_eq_zero hG hi hν I hKc hPK
    ρ hM hρ hKρ A.val.obj C hC μM (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq A)
    A.val.property.1 (hTA A) hswM νU hE hsw hμK hPKiw hMK hUK (hcoeffA A) f h0

variable [Finite (discreteSeriesStabilizer C hC μM
    (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC μM π hsq))]
  (ρX : Measure (unitaryUnramifiedCharacters
    (RationalPointFamily.leviRationalNormCharacters i ν I)))
  (w : discreteSeriesOrbit C hC μM (RationalPointFamily.leviRationalNormCharacters i ν I)
      (discreteSeriesClass C hC μM π hsq) → ℂ)

include hρ hKρ hTA hsw hswM hμK hPKiw hMK hUK hcoeffA in
/-- **Wave packets are orthogonal to `f` when the constant terms of the translates of `f`
vanish** (Waldspurger, proof of Lemma VIII.2.3, printed p. 322, for one orbit `O` and the actual
standard parabolic `P = P_I(F)`): under the hypotheses of Lemma VII.1.2 at every representative of
`O` and of formula (1) of the proof of Proposition VII.2.2
(`pairing_rationalInducedOrbitWavePacket_eq_integral_productPairing`), if
`(ρ(g₁) λ(g₂) f)^{(P)} = 0` for all `g₁, g₂ ∈ G(F)`, then `(f_ψ, f)_G = 0` for the actual wave
packet `f_ψ` (`rationalInducedOrbitWavePacket`) of every `ψ ∈ C^∞(O, P)`. -/
theorem pairing_rationalInducedOrbitWavePacket_eq_zero_of_rationalConstantTerm_eq_zero
    [IsFiniteMeasure ρX]
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure (RationalPointFamily.leviRationalNormCharacters i ν I) C hC μM
        (discreteSeriesClass C hC μM π hsq) ρX))
    {b : ℝ} (hwb : ∀ ω, ‖w ω‖ ≤ b)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (f : RationalSchwartzSpace hKc hPK ρ)
    (h0 : ∀ g₁ g₂ : rationalPoints G,
      rationalConstantTerm K.isOpen hKc hPK hM ρ νU hG hi hν
        (RationalPointFamily.rootSet_subset i ν I) hE
        (Space.translate (rationalTranslationWeights K.isOpen hKc hPK ρ) g₁ g₂ f) = 0) :
    pairing μG (rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC μM hsq ρX w q) f = 0 := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := 𝐉) hKc
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have : Nonempty (CompactOpenSubgroup 𝐌) :=
    ⟨⟨K.comap (standardLeviPoints i ν 𝐉).subtype continuous_subtype_val,
      isCompact_iff_compactSpace.mpr ‹_›⟩⟩
  have h := pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero
    (G := rationalPoints G) (M := standardLeviPoints i ν 𝐉)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν 𝐉)
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
    (compactOpenCofinal_standardLevi I hKc) C hC μM hsq ρX w hPK
    (rationalL2Weights K.isOpen hKc hPK ρ hsw)
    (fun A => rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hν
      (RationalPointFamily.rootSet_subset i ν I) I rfl K hKc hPK hM hρ hKρ A.val.obj
      (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq A).1 (hTA A))
    (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ)
    (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    (leviRationalUnitaryCoordinates hG hi hν I).continuous hwm hwb
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviData hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc) hM
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp) hcoeff q
    (rationalLeviL2Weights hG hi hν I hKc ρ hM hswM) hTA
    (rationalLeviXi_inv hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc hM)
    (fun m => rationalHeight_inv ρ m)
    (rationalConstantTermData νU) (rationalIsConjModulus νU) hE
    (rationalTranslationWeights K.isOpen hKc hPK ρ)
    (rationalLeviTranslationWeights hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen
      hKc hM ρ)
    hμK hPKiw hMK hUK f
    (fun A ψ => integrable_rationalCoefficientPairingIntegrand hG hi hν I hKc hPK ρ hM A.val.obj
      (hcoeffA A) hsw ψ f)
    (fun x => h0 x.1 x.2)
  unfold rationalInducedOrbitWavePacket
  with_reducible_and_instances exact h

end Orbit

end Langlands.HarishChandraSchwartz
