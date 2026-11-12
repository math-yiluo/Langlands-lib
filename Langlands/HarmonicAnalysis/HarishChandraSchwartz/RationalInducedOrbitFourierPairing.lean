import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacket
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedFourierTransform
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketPairing

/-! # `ψ_f[O, P]` and the pairing of wave packets with `C(G)` on actual points (VII.1, VII.2)

For a connected reductive group `G` over a nonarchimedean local field and an actual standard
parabolic `P = P_I(F) = M_I(F) ⋉ U_I(F) ⊇ P₀(F)`, this module joins the actual wave packets of
`RationalInducedOrbitWavePacket` and the actual Fourier transform of
`RationalInducedFourierTransform`:

* `rationalFourierOrbitSection`: Waldspurger's `ψ_f[O, P] : ω ↦ f̂(ω, P)` over the unitary
  unramified orbit `O` of a discrete series `π` of `M_I(F)` (VII.1, printed p. 316), with its
  values (`rationalFourierOrbitSection_apply`) and coherence
  (`rationalFourierOrbitSection_mem_coherent`);
* formula (1) of the proof of Proposition VII.2.2 (printed p. 319) for an arbitrary `f ∈ C(G)`:
  if `ψ_f[O, P]` is a smooth section `r`, then `(f_ψ, f)_G = ∫_O conj(w(ω)) (ψ_ω, f̂(ω, P)) dω`
  (`pairing_rationalInducedOrbitWavePacket_eq_integral_productPairing`).
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

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (hρ : IsClosedSubgroup ρ)
  (hKρ : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) ρ)
  (hM : IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    ((K : Subgroup (rationalPoints G)).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (μM : Measure (𝐌 ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μM)
  (hTA : ∀ A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π,
    IsRationalLeviTempered hKc ρ hM A.val.obj)
  {μG : Measure (rationalPoints G)} [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight μG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))

/-- **Waldspurger's `ψ_f[O, P]` on actual rational points** (VII.1, printed p. 316): for
`f ∈ C(G)`, the section `ω ↦ f̂(ω, P)` over the unitary unramified orbit `O` of `π`, with value
`rationalInducedFourierTransform … A … f` at every representative `A`
(`rationalFourierOrbitSection_apply`). It is the Library's `fourierOrbitSection` on the actual
data of `P_I(F)`. -/
def rationalFourierOrbitSection (f : RationalSchwartzSpace hKc hPK ρ) :
    ProductInducedOrbitSections (RationalPointFamily.leviRationalNormCharacters i ν I) π
      (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  haveI : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  fourierOrbitSection (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    K hKc (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (compactOpenCofinal_standardLevi I hKc) C hC μM
    (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq)
    (rationalL2Weights K.isOpen hKc hPK ρ hsw)
    (fun A => rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hν
      (RationalPointFamily.rootSet_subset i ν I) I rfl K hKc hPK hM hρ hKρ A.val.obj
      (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq A).1 (hTA A))
    (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ) f

/-- At a representative `A`, `ψ_f[O, P]_A = f̂(A, P)` (`rationalInducedFourierTransform`). -/
theorem rationalFourierOrbitSection_apply (f : RationalSchwartzSpace hKc hPK ρ)
    (A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π) :
    rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw f A =
      rationalInducedFourierTransform hG hi hν I hKc hPK ρ hρ hKρ hM A.val.obj C hC μM
        (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq A) A.val.property.1 (hTA A)
        hsw f := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have h := fourierOrbitSection_apply (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    K hKc (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (compactOpenCofinal_standardLevi I hKc) C hC μM
    (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq)
    (rationalL2Weights K.isOpen hKc hPK ρ hsw)
    (fun A => rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hν
      (RationalPointFamily.rootSet_subset i ν I) I rfl K hKc hPK hM hρ hKρ A.val.obj
      (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq A).1 (hTA A))
    (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ) f A
  unfold rationalFourierOrbitSection rationalInducedFourierTransform
  with_reducible_and_instances exact h

/-- `ψ_f[O, P]` is coherent: its values at two representatives of the same class correspond
under every equivalence between them. -/
theorem rationalFourierOrbitSection_mem_coherent [μG.IsInvInvariant]
    (f : RationalSchwartzSpace hKc hPK ρ) :
    rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw f ∈
      coherentProductInducedOrbitSections (RationalPointFamily.leviRationalNormCharacters i ν I) π
        (G := rationalPoints G)
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have h := fourierOrbitSection_mem_coherent (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    K hKc (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (compactOpenCofinal_standardLevi I hKc) C hC μM
    (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq)
    (rationalL2Weights K.isOpen hKc hPK ρ hsw)
    (fun A => rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hν
      (RationalPointFamily.rootSet_subset i ν I) I rfl K hKc hPK hM hρ hKρ A.val.obj
      (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq A).1 (hTA A))
    (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ) f
  unfold rationalFourierOrbitSection
  with_reducible_and_instances exact h

variable [Finite (discreteSeriesStabilizer C hC μM
    (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC μM π hsq))]
  (ρX : Measure (unitaryUnramifiedCharacters
    (RationalPointFamily.leviRationalNormCharacters i ν I)))
  (w : discreteSeriesOrbit C hC μM (RationalPointFamily.leviRationalNormCharacters i ν I)
      (discreteSeriesClass C hC μM π hsq) → ℂ)

/-- **Formula (1) of the proof of Proposition VII.2.2 on actual rational points** (printed
p. 319): if `ψ_f[O, P]` is given by a smooth section `r ∈ C^∞(O, P)` (`hrf`), then for the actual
wave packet `f_ψ` of `q ∈ C^∞(O, P)` (`rationalInducedOrbitWavePacket`),
`(f_ψ, f)_G = ∫_O conj(w(ω)) (ψ_ω, f̂(ω, P)) dω`, where `(ψ_ω, ·)` is the product of V.2 on
`L(ω, P)` (`unitaryOrbitProductPairing`). -/
theorem pairing_rationalInducedOrbitWavePacket_eq_integral_productPairing
    [μG.IsInvInvariant] [SFinite μG] [IsFiniteMeasure ρX]
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure (RationalPointFamily.leviRationalNormCharacters i ν I) C hC μM
        (discreteSeriesClass C hC μM π hsq) ρX))
    {b : ℝ} (hwb : ∀ ω, ‖w ω‖ ≤ b)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (q r : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π)
    (f : RationalSchwartzSpace hKc hPK ρ)
    (hrf : r.val =
      rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw f) :
    pairing μG (rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC μM hsq ρX w q) f =
      ∫ ω, conj (w ω) *
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
          (discreteSeriesClass C hC μM π hsq) ρX := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν)
    (J := RationalPointFamily.rootSet i ν I) hKc
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have h := pairing_inducedOrbitWavePacket_eq_integral_productPairing (G := rationalPoints G)
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
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp) hcoeff q r f
    (by unfold rationalFourierOrbitSection at hrf; exact hrf)
  unfold unitaryOrbitWeightedProductPairing at h
  unfold rationalInducedOrbitWavePacket
  with_reducible_and_instances exact h

end Langlands.HarishChandraSchwartz
