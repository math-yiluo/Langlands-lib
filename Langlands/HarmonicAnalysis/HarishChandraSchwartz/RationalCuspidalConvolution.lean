import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedConstantTermFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalConvolution
import Langlands.Group.GL.LeviCentralQuotientMeasure

/-! # Cuspidal functions and wave packets on actual points (Waldspurger, proof of Lemma VIII.2.3)

For a connected reductive group `G` over a nonarchimedean local field and an actual standard
parabolic `P = P_I(F) = M_I(F) ⋉ U_I(F) ⊇ P₀(F)`, this module instantiates on actual rational
points the Library's `CuspidalConvolution`:

* `rationalUnipotentHaar_isInvInvariant`: a right-invariant Haar measure on `U_J(F)` is
  invariant under inversion;
* `RationalConstantTermIndVanishes`: the condition `f^{(P),Ind} = 0` of Lemma VIII.2.1, that is
  `(ρ(g₁) λ(g₂) f)^{(P)} = 0` for all `g₁, g₂ ∈ G(F)`;
* `isUnipotentCuspidal_iff_rationalConstantTermIndVanishes`: `∫_{U_I(F)} f(x u y) du = 0` for all
  `x, y` if and only if `f^{(P),Ind} = 0`;
* `convolution_rationalInducedOrbitWavePacket_eq_zero` and
  `convolution_rationalInducedOrbitWavePacket_left_eq_zero`: if `f₁^{(P),Ind} = 0`, then
  `f₁ ∗ f_ψ = f_ψ ∗ f₁ = 0` for the actual wave packet `f_ψ` of every `ψ ∈ C^∞(O, P)` (the
  vanishing proved in the proof of Lemma VIII.2.3), with the absolute convergence of Lemma VII.1.2
  supplied by `integrable_rationalCoefficientPairingIntegrand`.
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

section Unipotent

/-- **Haar measures on `U_J(F)` are inversion invariant**: a right-invariant Haar measure `ν_U`
on the actual unipotent radical `U_J(F)` satisfies `ν_U(A⁻¹) = ν_U(A)`. It is the Library's
`isInvInvariant_of_isMulRightInvariant`, with the regularity of `ν_U` from the second
countability and local compactness of the closed subgroup `U_J(F)`. -/
theorem rationalUnipotentHaar_isInvInvariant {J : Set (characterLattice S)}
    (νU : Measure (standardUnipotentPoints i ν J)) [νU.IsHaarMeasure] [νU.IsMulRightInvariant] :
    νU.IsInvInvariant := by
  have hU := isClosed_standardUnipotentPoints i ν J
  have : LocallyCompactSpace (standardUnipotentPoints i ν J) := hU.locallyCompactSpace
  have : SecondCountableTopology (standardUnipotentPoints i ν J) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : TopologicalSpace.MetrizableSpace (standardUnipotentPoints i ν J) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  have : νU.Regular :=
    MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure νU
  exact isInvInvariant_of_isMulRightInvariant νU

end Unipotent

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

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (hM : IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν 𝐉))
    ((K : Subgroup (rationalPoints G)).subgroupOf (standardLeviPoints i ν 𝐉)))

section Cuspidal

variable (νU : Measure (standardUnipotentPoints i ν 𝐉)) [νU.IsHaarMeasure]
  (hE : ConstantTermEstimate νU (standardUnipotentModulus i ν (RationalPointFamily.rootSet i ν I))
    (rationalXi hKc hPK) (rationalHeight (F := F) ρ) (rationalLeviXi hKc hM)
    (fun m => rationalHeight (F := F) ρ m))

/-- **The condition `f^{(P),Ind} = 0` on actual points** (Waldspurger, III.6 and Lemma VIII.2.1,
for the actual standard parabolic `P = P_I(F)`): for `f ∈ C(G)`, the actual constant term
`f^{(P),Ind}(g₁, g₂) = (ρ(g₁) λ(g₂) f)^{(P)}` (`rationalConstantTerm`, which needs the conclusion
`hE` of Proposition II.4.5) vanishes for all `g₁, g₂ ∈ G(F)`. -/
def RationalConstantTermIndVanishes (f : RationalSchwartzSpace hKc hPK ρ) : Prop :=
  ∀ g₁ g₂ : rationalPoints G,
    rationalConstantTerm K.isOpen hKc hPK hM ρ νU hG hi hν
      (RationalPointFamily.rootSet_subset i ν I) hE
      (Space.translate (rationalTranslationWeights K.isOpen hKc hPK ρ) g₁ g₂ f) = 0

/-- **Cuspidality along `U_I(F)` is the vanishing of `f^{(P),Ind}`**: for `f ∈ C(G)`,
`∫_{U_I(F)} f(x u y) dν_U(u) = 0` for all `x, y ∈ G(F)` (`IsUnipotentCuspidal`) if and only if
the actual constant term `(ρ(g₁) λ(g₂) f)^{(P)}` vanishes for all `g₁, g₂ ∈ G(F)`. -/
theorem isUnipotentCuspidal_iff_rationalConstantTermIndVanishes
    (f : RationalSchwartzSpace hKc hPK ρ) :
    IsUnipotentCuspidal (G := rationalPoints G) νU (f : rationalPoints G → ℂ) ↔
      RationalConstantTermIndVanishes hG hi hν I hKc hPK ρ hM νU hE f := by
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  unfold RationalConstantTermIndVanishes
  constructor
  · intro hf g₁ g₂
    have h := constantTermIndVanishes_of_isUnipotentCuspidal (G := rationalPoints G)
      (rationalConstantTermData νU) hE (rationalTranslationWeights K.isOpen hKc hPK ρ)
      (rationalLeviTranslationWeights hG hi hν (RationalPointFamily.rootSet_subset i ν I)
        K.isOpen hKc hM ρ) hf (g₁, g₂)
    unfold Space.constantTermInd at h
    unfold rationalConstantTerm
    with_reducible_and_instances exact h
  · intro h0
    exact isUnipotentCuspidal_of_constantTermIndVanishes (G := rationalPoints G)
      (rationalConstantTermData νU) hE (rationalTranslationWeights K.isOpen hKc hPK ρ)
      (rationalLeviTranslationWeights hG hi hν (RationalPointFamily.rootSet_subset i ν I)
        K.isOpen hKc hM ρ) (fun x => h0 x.1 x.2)

end Cuspidal

section Convolution

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
  [Finite (discreteSeriesStabilizer C hC μM
    (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC μM π hsq))]
  (ρX : Measure (unitaryUnramifiedCharacters
    (RationalPointFamily.leviRationalNormCharacters i ν I)))
  (w : discreteSeriesOrbit C hC μM (RationalPointFamily.leviRationalNormCharacters i ν I)
      (discreteSeriesClass C hC μM π hsq) → ℂ)

include hρ hKρ hTA hsw hswM hμK hPKiw hMK hUK hcoeffA in
/-- **Waldspurger, proof of Lemma VIII.2.3, `f₁ ∗ f_ψ = 0`, on actual points** (printed p. 322,
for one orbit `O` and the actual standard parabolic `P = P_I(F)`): under the hypotheses of
Lemma VII.1.2 at every representative of `O`
(`rationalInducedFourierTransform_eq_rationalConstantTermInducedFourierTransform`) and of the
actual wave packet, if `f₁^{(P),Ind} = 0`, that is `(ρ(g₁) λ(g₂) f₁)^{(P)} = 0` for all
`g₁, g₂ ∈ G(F)` (`h0`), then
`(f₁ ∗ f_ψ)(g) = ∫ f₁(h) f_ψ(h⁻¹ g) dμG(h) = 0` for every `g` and the actual wave packet `f_ψ`
(`rationalInducedOrbitWavePacket`) of every `ψ ∈ C^∞(O, P)`. -/
theorem convolution_rationalInducedOrbitWavePacket_eq_zero
    [IsFiniteMeasure ρX]
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure (RationalPointFamily.leviRationalNormCharacters i ν I) C hC μM
        (discreteSeriesClass C hC μM π hsq) ρX))
    {b : ℝ} (hwb : ∀ ω, ‖w ω‖ ≤ b)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (f₁ : RationalSchwartzSpace hKc hPK ρ)
    (h0 : RationalConstantTermIndVanishes hG hi hν I hKc hPK ρ hM νU hE f₁)
    (g : rationalPoints G) :
    convolution μG f₁
      (rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC μM hsq ρX w q) g = 0 := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := 𝐉) hKc
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have : Nonempty (CompactOpenSubgroup 𝐌) :=
    ⟨⟨K.comap (standardLeviPoints i ν 𝐉).subtype continuous_subtype_val,
      isCompact_iff_compactSpace.mpr ‹_›⟩⟩
  have := rationalUnipotentHaar_isInvInvariant νU
  have hcusp := (isUnipotentCuspidal_iff_rationalConstantTermIndVanishes hG hi hν I hKc hPK ρ hM
    νU hE f₁).mpr h0
  have h := convolution_inducedOrbitWavePacket_eq_zero
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
    hμK hPKiw hMK hUK f₁ hcusp g
    (fun A ψ => integrable_rationalCoefficientPairingIntegrand hG hi hν I hKc hPK ρ hM A.val.obj
      (hcoeffA A) hsw ψ
      (Space.complexConj (Space.translate (rationalTranslationWeights K.isOpen hKc hPK ρ) g⁻¹ 1
        (Space.check (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ) f₁))))
  unfold rationalInducedOrbitWavePacket
  with_reducible_and_instances exact h

include hρ hKρ hTA hsw hswM hμK hPKiw hMK hUK hcoeffA in
/-- **Waldspurger, proof of Lemma VIII.2.3, `f_ψ ∗ f₁ = 0`, on actual points** ("Idem
`f_ψ ∗ f_1 = 0`", printed p. 322): under the hypotheses of
`convolution_rationalInducedOrbitWavePacket_eq_zero`,
`(f_ψ ∗ f₁)(g) = ∫ f_ψ(h) f₁(h⁻¹ g) dμG(h) = 0` for every `g`. -/
theorem convolution_rationalInducedOrbitWavePacket_left_eq_zero
    [IsFiniteMeasure ρX]
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure (RationalPointFamily.leviRationalNormCharacters i ν I) C hC μM
        (discreteSeriesClass C hC μM π hsq) ρX))
    {b : ℝ} (hwb : ∀ ω, ‖w ω‖ ≤ b)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (f₁ : RationalSchwartzSpace hKc hPK ρ)
    (h0 : RationalConstantTermIndVanishes hG hi hν I hKc hPK ρ hM νU hE f₁)
    (g : rationalPoints G) :
    convolution μG
      (rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC μM hsq ρX w q) f₁ g = 0 := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := 𝐉) hKc
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have : Nonempty (CompactOpenSubgroup 𝐌) :=
    ⟨⟨K.comap (standardLeviPoints i ν 𝐉).subtype continuous_subtype_val,
      isCompact_iff_compactSpace.mpr ‹_›⟩⟩
  have := rationalUnipotentHaar_isInvInvariant νU
  have hcusp := (isUnipotentCuspidal_iff_rationalConstantTermIndVanishes hG hi hν I hKc hPK ρ hM
    νU hE f₁).mpr h0
  have h := convolution_inducedOrbitWavePacket_left_eq_zero
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
    hμK hPKiw hMK hUK f₁ hcusp g
    (fun A ψ => integrable_rationalCoefficientPairingIntegrand hG hi hν I hKc hPK ρ hM A.val.obj
      (hcoeffA A) hsw ψ
      (Space.complexConj (Space.translate (rationalTranslationWeights K.isOpen hKc hPK ρ) 1 g
        (Space.check (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ) f₁))))
  unfold rationalInducedOrbitWavePacket
  with_reducible_and_instances exact h

end Convolution

end Langlands.HarishChandraSchwartz
