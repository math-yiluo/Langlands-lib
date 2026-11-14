import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacketOrthogonality
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketOrthogonalityDense

/-! # Wave packets detect `ψ_f[O, P]` on actual points, for a weight positive on a dense set

For a connected reductive group `G` over a nonarchimedean local field and an actual standard
parabolic `P = P_I(F) = M_I(F) ⋉ U_I(F) ⊇ P₀(F)`, this module instantiates
`InducedOrbitWavePacketOrthogonalityDense` on actual rational points. The weight `u` on the orbit
is bounded, continuous and nonnegative, and positive on a dense subset of the orbit. This is the
situation of the Plancherel weight `µ` of Waldspurger V.2: it is `≥ 0` on `O` (Lemma V.2.1) but
may vanish where `j` has a unitary pole.

* `rationalUnitaryOrbitWeightedProductCore_of_dense`: the positive definite hermitian product
  `(q, r) ↦ ∫_O u(ω) (q_ω, r_ω) dω` on `C^∞(O, P)` (the summand of the product of VII.2,
  printed p. 319, for one pair `(O, P)`);
* `rationalFourierOrbitSection_eq_zero_iff_forall_pairing_rationalInducedOrbitWavePacket_eq_zero_of_dense`:
  `ψ_f[O, P] = 0` if and only if `(f_ψ, f)_G = 0` for every wave packet `f_ψ`, `ψ ∈ C^∞(O, P)`,
  of weight `u` (the deduction in the proof of Corollary VII.2.3). The smoothness of
  `ψ_f[O, P]` (Proposition VII.1.3) is supplied by `rationalFourierOrbitSmoothSectionLinear`;
* `rationalInducedFourierTransform_eq_zero_of_forall_pairing_rationalInducedOrbitWavePacket_eq_zero_of_dense`:
  the same conclusion at each representative, `f̂(A, P) = 0`.

The proofs are those of `RationalInducedOrbitWavePacketOrthogonality` with the generic results of
`InducedOrbitWavePacketOrthogonalityDense` in place of their everywhere-positive versions.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

section Orthogonality

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

local instance instRationalInducedOrbitWavePacketOrthogonalityDense1
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (RationalPointFamily.rootSet i ν I)
local instance instRationalInducedOrbitWavePacketOrthogonalityDense2
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsAffine (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left
local instance instRationalInducedOrbitWavePacketOrthogonalityDense3
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    TopologicalSpace
      (rationalPoints (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
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

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (μM : Measure (𝐌 ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μM)
  [Finite (discreteSeriesStabilizer C hC μM
    (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC μM π hsq))]
  [Finite (𝐌 ⧸ (commonNormKernel (RationalPointFamily.leviRationalNormCharacters i ν I) ⊔ C))]
  (ρX : Measure (unitaryUnramifiedCharacters
    (RationalPointFamily.leviRationalNormCharacters i ν I)))
  (u : discreteSeriesOrbit C hC μM (RationalPointFamily.leviRationalNormCharacters i ν I)
      (discreteSeriesClass C hC μM π hsq) → ℝ)

/-- **The weighted product on `C^∞(O, P)` for an actual standard parabolic and a weight positive
on a dense set** (Waldspurger, VII.2, printed p. 319, for a single pair `(O, P)`): for a finite
measure `ρX` on `Im X(M_I)` positive on nonempty open sets and a bounded continuous weight
`u ≥ 0` on the orbit with `{ω | 0 < u ω}` dense, `(q, r) ↦ ∫_O u(ω) (q_ω, r_ω) dω` is a positive
definite hermitian product on `C^∞(O, P) = rationalInducedSmoothOrbitSections`,
conjugate-linear in its first argument. It is `unitaryOrbitWeightedProductCore_of_dense` on the
actual data of `P_I(F)`. -/
@[instance_reducible]
def rationalUnitaryOrbitWeightedProductCore_of_dense [IsFiniteMeasure ρX] [ρX.IsOpenPosMeasure]
    (hu : Continuous u) (hu0 : ∀ ω, 0 ≤ u ω) (hud : Dense {ω | 0 < u ω}) {b : ℝ}
    (hub : ∀ ω, u ω ≤ b) :
    InnerProductSpace.Core ℂ (rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  unitaryOrbitWeightedProductCore_of_dense (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
    (compactOpenCofinal_standardLevi I hKc) C hC μM hsq ρX u
    (leviRationalUnitaryCoordinates hG hi hν I).continuous hu hu0 hud hub

/-- The inner product of `rationalUnitaryOrbitWeightedProductCore_of_dense` is
`∫_O u(ω) (q_ω, r_ω) dω`. -/
theorem rationalUnitaryOrbitWeightedProductCore_of_dense_inner [IsFiniteMeasure ρX]
    [ρX.IsOpenPosMeasure]
    (hu : Continuous u) (hu0 : ∀ ω, 0 ≤ u ω) (hud : Dense {ω | 0 < u ω}) {b : ℝ}
    (hub : ∀ ω, u ω ≤ b)
    (q r : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) :
    (rationalUnitaryOrbitWeightedProductCore_of_dense hG hi hν I hKc hPK π C hC μM hsq ρX u hu hu0
        hud hub).inner q r =
      ∫ ω, (u ω : ℂ) *
        (haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
        unitaryOrbitProductPairing (G := rationalPoints G)
          (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
          (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
          (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
          (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
          (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
          (fun g =>
            RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
          (modularCharacter_standardParabolicPoints hG hi hν I rfl
            (RationalPointFamily.rootSet_subset i ν I))
          π (compactOpenCofinal_standardLevi I hKc) C hC μM hsq
          (RationalPointFamily.leviRationalNormCharacters i ν I)
          (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
          (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
          (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv q r ω)
        ∂discreteSeriesOrbitMeasure (RationalPointFamily.leviRationalNormCharacters i ν I) C hC μM
          (discreteSeriesClass C hC μM π hsq) ρX :=
  rfl

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (hρ : IsClosedSubgroup ρ)
  (hKρ : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) ρ)
  (hM : IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν 𝐉))
    ((K : Subgroup (rationalPoints G)).subgroupOf (standardLeviPoints i ν 𝐉)))
  (hTA : ∀ A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π,
    IsRationalLeviTempered hKc ρ hM A.val.obj)
  {μG : Measure (rationalPoints G)} [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight μG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
  [μG.IsInvInvariant] [SigmaFinite μG]
  (hμK : μG (K : Set (rationalPoints G)) = 1)
  {μL : Measure 𝐌} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] [MeasurableInv 𝐌]
  [μL.IsInvInvariant] [SFinite μL]
  (hswM : SquareIntegrableWeight μL (rationalLeviXi hKc hM)
    (fun m => rationalHeight (F := F) ρ m))
  (hTπ : IsRationalLeviTempered hKc ρ hM π.obj)
  {νU : Measure (standardUnipotentPoints i ν 𝐉)} [νU.IsHaarMeasure]
  [νU.IsMulRightInvariant] [SFinite νU]
  (hE : ConstantTermEstimate νU (standardUnipotentModulus i ν (RationalPointFamily.rootSet i ν I))
    (rationalXi hKc hPK) (rationalHeight (F := F) ρ) (rationalLeviXi hKc hM)
    (fun m => rationalHeight (F := F) ρ m))
  (hPKiw : ∀ (m : standardLeviPoints i ν 𝐉) (n : standardUnipotentPoints i ν 𝐉),
    (m : rationalPoints G) * n ∈ K ↔ (m : rationalPoints G) ∈ K ∧ (n : rationalPoints G) ∈ K)
  (hMK : μL {m : 𝐌 | (m : rationalPoints G) ∈ K} = 1)
  (hUK : νU {n : standardUnipotentPoints i ν 𝐉 | (n : rationalPoints G) ∈ K} = 1)
  {Cn : ℝ}
  (hnσ : ∀ m : standardLeviPoints i ν (RationalPointFamily.rootSet i ν I),
    ‖rationalValuationCoordinates (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))
      (isConnectedReductive_leviScheme_rootSet hG hi hν I)
      ((RationalPointFamily.leviRationalPointHomeomorph i ν I).symm m)‖ ≤
      Cn * (1 + rationalHeight (F := F) ρ m))
  (hint : ∀ (f : RationalSchwartzSpace hKc hPK ρ)
    (A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π)
    (ψ : productInducedCoefficientObject (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A.val.obj),
    Integrable
      (fun x : rationalPoints G × K => conj (CompactInduction.integrand
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν 𝐉) A.val.obj K x.1 ψ x.2) * f x.1)
      (μG.prod (CompactInduction.measure K hKc)))

include hμK hswM hTπ hE hPKiw hMK hUK hnσ hint in
/-- **Wave packets detect `ψ_f[O, P]` on actual points, for a weight positive on a dense set**
(the deduction in the proof of Corollary VII.2.3, printed p. 319, with Proposition VII.1.3 from
`rationalFourierOrbitSmoothSectionLinear`): for a bounded continuous weight `u ≥ 0` with
`{ω | 0 < u ω}` dense and `f ∈ C(G)`, `ψ_f[O, P] = 0` if and only if `(f_ψ, f)_G = 0` for the
actual wave packet `f_ψ` of weight `u` of every `ψ ∈ C^∞(O, P)`. -/
theorem rationalFourierOrbitSection_eq_zero_iff_forall_pairing_rationalInducedOrbitWavePacket_eq_zero_of_dense
    [IsFiniteMeasure ρX] [ρX.IsOpenPosMeasure]
    (hu : Continuous u) (hu0 : ∀ ω, 0 ≤ u ω) (hud : Dense {ω | 0 < u ω}) {b : ℝ}
    (hub : ∀ ω, u ω ≤ b)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (f : RationalSchwartzSpace hKc hPK ρ) :
    rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw f = 0 ↔
      ∀ q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π,
        pairing μG (rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC μM hsq ρX
          (fun ω => (u ω : ℂ)) q) f = 0 := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν)
    (J := RationalPointFamily.rootSet i ν I) hKc
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have hsm := (rationalFourierOrbitSmoothSectionLinear hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM
    hsq hTA hsw hμK hswM hTπ hE hPKiw hMK hUK hnσ hint f).property
  rw [rationalFourierOrbitSmoothSectionLinear_val] at hsm
  have h := fourierOrbitSection_eq_zero_iff_forall_pairing_inducedOrbitWavePacket_eq_zero_of_dense
    (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
    (compactOpenCofinal_standardLevi I hKc) C hC μM hsq ρX u hPK
    (rationalL2Weights K.isOpen hKc hPK ρ hsw)
    (fun A => rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hν
      (RationalPointFamily.rootSet_subset i ν I) I rfl K hKc hPK hM hρ hKρ A.val.obj
      (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq A).1 (hTA A))
    (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ)
    (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    (leviRationalUnitaryCoordinates hG hi hν I).continuous hu hu0 hud hub
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviData hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc) hM
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp) hcoeff f
    (by unfold rationalFourierOrbitSection at hsm; exact hsm)
  unfold rationalFourierOrbitSection rationalInducedOrbitWavePacket
  delta rationalXi
  with_reducible_and_instances exact h

include hμK hswM hTπ hE hPKiw hMK hUK hnσ hint in
/-- **The conclusion of Corollary VII.2.3 at each representative, on actual points, for a weight
positive on a dense set**: for a bounded continuous weight `u ≥ 0` with `{ω | 0 < u ω}` dense, if
`(f_ψ, f)_G = 0` for the actual wave packet `f_ψ` of weight `u` of every `ψ ∈ C^∞(O, P)`, then
`f̂(A, P) = 0` (`rationalInducedFourierTransform`) for every representative `A` of the orbit. -/
theorem rationalInducedFourierTransform_eq_zero_of_forall_pairing_rationalInducedOrbitWavePacket_eq_zero_of_dense
    [IsFiniteMeasure ρX] [ρX.IsOpenPosMeasure]
    (hu : Continuous u) (hu0 : ∀ ω, 0 ≤ u ω) (hud : Dense {ω | 0 < u ω}) {b : ℝ}
    (hub : ∀ ω, u ω ≤ b)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (f : RationalSchwartzSpace hKc hPK ρ)
    (h0 : ∀ q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π,
      pairing μG (rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC μM hsq ρX
        (fun ω => (u ω : ℂ)) q) f = 0)
    (A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π) :
    rationalInducedFourierTransform hG hi hν I hKc hPK ρ hρ hKρ hM A.val.obj C hC μM
      (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq A) A.val.property.1 (hTA A)
      hsw f = 0 := by
  rw [← rationalFourierOrbitSection_apply hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw f
      A,
    (rationalFourierOrbitSection_eq_zero_iff_forall_pairing_rationalInducedOrbitWavePacket_eq_zero_of_dense
      hG hi hν I hKc hPK π C hC μM hsq ρX u ρ hρ hKρ hM hTA hsw hμK hswM hTπ hE hPKiw hMK hUK hnσ
      hint hu hu0 hud hub hcoeff f).mpr h0]
  rfl

end Orthogonality

end Langlands.HarishChandraSchwartz
