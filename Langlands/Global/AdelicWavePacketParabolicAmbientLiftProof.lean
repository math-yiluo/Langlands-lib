import Langlands.Global.AdelicWavePacketParabolicAmbientLiftStatement
import Langlands.Global.AdelicRelativeAmbientParameterProduct
import Langlands.Global.AdelicEisensteinAmbientShiftProof
import Langlands.Global.AdelicEisensteinImaginaryContinuation
import Langlands.Global.AdelicSpectralCoordinateProduct
import Mathlib.Tactic.Ring

/-! # Lifting relative wave packets by an ambient spectral coefficient

Multiplying a wave packet of `P` over `i(𝔞_M^G)^*` by the profile
`g ↦ ∫ b(z) g^{i eG(z)} dz` of a smooth compactly supported ambient coefficient `b` gives a wave
packet of the same presented parabolic over all of `i𝔞_P^*`: concatenate the relative chart
with the ambient chart through `relativeAmbientParameterEquiv`, multiply the coefficients, keep
the inducing forms and continuations, and move the ambient character out of each continuation
with the ambient shift of Eisenstein series.

* `wavePacketParabolicAmbientLift_of_regularParameter`: `WavePacketParabolicAmbientLiftStatement`
  from `EisensteinRegularParameterStatement`;
* `isWavePacket_of_isParabolicWavePacket`: a wave packet of one presented parabolic is a wave
  packet in the sense of `IsWavePacket`;
* `wavePacketAmbientLift_of_regularParameter`: `WavePacketAmbientLiftStatement` from
  `EisensteinRegularParameterStatement`. -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Analysis.Meromorphic

/-- The ambient product formula with the original inducing forms and the original
number of summands retained. -/
theorem relativeWavePacketAmbientLiftPresentation
    (hR : EisensteinRegularParameterStatement.{0})
    {F : Type} [Field F] [NumberField F]
    {G P M : GroupScheme (Spec (CommRingCat.of F))}
    {A : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
    [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
    {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
    {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (hG : IsConnectedReductive G) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact p K) {n m k : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] relativeParameterSpace (F := F) p)
    (eG : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G)
    (b : (Fin m → ℝ) → ℂ) (c : Fin k → (Fin n → ℝ) → ℂ)
    (v : Fin k → AdelicGroupPoints F G → ℂ)
    (E : Fin k → ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
    (D : Set (ComplexCharacterParameter F P))
    (hD : Set.range (imaginaryParameter F P) ⊆ D)
    (hE : ∀ j g, IsMeromorphicInCoordinatesOn (fun lam => E j lam g) D)
    (hreg : ∀ j, ∃ R, ∀ lam, r.IsRegularParameter hA hT R lam → E j lam = hK.eisensteinSeries (v j) lam) :
    let e' := (spectralCoordinateProduct n m).symm.trans
      ((e.prodCongr eG).trans (relativeAmbientParameterEquiv r hG))
    let c' := fun j => spectralProductCoefficient (c j) b
    (fun g => ∫ z, ∑ j, c' j z * E j (imaginaryParameter F P (e' z)) g ∂(spectralMeasure (n + m))) =
    fun g => ambientWavePacketProfile eG b g *
      (∫ x, ∑ j, c j x * E j (imaginaryParameter F P (e x).val) g ∂(spectralMeasure n)) := by
  intro e' c'
  funext g
  let f : (Fin n → ℝ) → ℂ := fun x =>
    ∑ j, c j x * E j (imaginaryParameter F P (e x).val) g
  let B : (Fin m → ℝ) → ℂ := fun z => b z * parameterPower F G (imaginaryParameter F G (eG z)) g
  have he (x : (Fin n → ℝ) × (Fin m → ℝ)) :
      e' (spectralCoordinateProduct n m x) =
        relativeAmbientParameterEquiv r hG (e x.1, eG x.2) := by
    simp only [e', LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  have hshift (j : Fin k) (x : (Fin n → ℝ) × (Fin m → ℝ)) :
      E j (imaginaryParameter F P (e' (spectralCoordinateProduct n m x))) g =
        parameterPower F G (imaginaryParameter F G (eG x.2)) g *
          E j (imaginaryParameter F P (e x.1).val) g := by
    rw [he, imaginaryParameter_relativeAmbientParameterEquiv]
    refine eisensteinContinuationAmbientShift_of_regularParameter hR F G P M A p l a r hA hT hG
      K hK (v j) g (fun lam => E j lam g) D (hE j g) ?_ _
      (parameterRealPart_imaginaryParameter _) _ (hD (Set.mem_range_self _)) ?_
    · obtain ⟨R, hR⟩ := hreg j
      exact ⟨R, fun lam _ h => congrFun (hR lam h) g⟩
    · rw [← imaginaryParameter_relativeAmbientParameterEquiv r hG]
      exact hD (Set.mem_range_self _)
  have hf : (fun z => ∑ j, c' j z * E j (imaginaryParameter F P (e' z)) g) =
      spectralProductCoefficient f B := by
    funext z
    obtain ⟨x, rfl⟩ := (spectralCoordinateProduct n m).surjective z
    simp only [c', spectralProductCoefficient_apply_product, hshift, f, B, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hf, integral_spectralProductCoefficient, mul_comm]
  rfl

/-- **Ambient lift of a relative wave packet, retaining the parabolic.** If every regular
parameter region is nonempty, the product of the ambient profile of a smooth compactly supported
coefficient with a wave packet of `P` over `i(𝔞_M^G)^*` is a wave packet of `P` over `i𝔞_P^*`,
with the concatenated coordinates `ℝ^{n+m} ≃ (𝔞_M^G)^* × 𝔞_G^* ≃ 𝔞_P^*`, the product
coefficients, and the original inducing forms, continuations and holomorphy domain. -/
theorem wavePacketParabolicAmbientLift_of_regularParameter
    (hR : EisensteinRegularParameterStatement.{0}) :
    WavePacketParabolicAmbientLiftStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ _ p hp iU l a r _ _ _ hA hT hG hiU K hK N d rho hsmooth
    hcalc m eG b hb hb' Θ hΘ
  obtain ⟨n, e, k, v, c, E, D, hv, hc, hD, hE, hreg, hΘ⟩ := hΘ
  let e' := (spectralCoordinateProduct n m).symm.trans
    ((e.prodCongr eG).trans (relativeAmbientParameterEquiv r hG))
  let c' := fun j => spectralProductCoefficient (c j) b
  refine ⟨n + m, e', k, v, c', E, D, hv, fun j => ⟨(hc j).1.spectralProductCoefficient hb,
    (hc j).2.spectralProductCoefficient hb'⟩, hD, hE, hreg, ?_⟩
  rw [hΘ]
  let : LocallyOfFiniteType P.X.hom := IsClosedSubgroup.locallyOfFiniteType (j := p) hp
  exact (relativeWavePacketAmbientLiftPresentation hR r hA hT hG hK e eG b c v E D hD hE hreg).symm

/-- A wave packet of one presented parabolic `P` with geometric unipotent radical and
`P(𝔸)K = G(𝔸)` is a wave packet in the sense of `IsWavePacket`, with the same data. -/
theorem isWavePacket_of_isParabolicWavePacket {F : Type} [Field F] [NumberField F]
    {G P M U : GroupScheme (Spec (CommRingCat.of F))}
    {A : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    {p : P ⟶ G} [hp : IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
    {a : A.toGrp ⟶ M} {r : ParabolicRootPresentation p l a}
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    {hA : IsSplitTorus A.toGrp} {hT : IsSplitTorus r.data.T.toGrp}
    (hiU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {K : Subgroup (AdelicGroupPoints F G)} {N d : ℕ}
    {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth} {Θ : AdelicGroupPoints F G → ℂ} :
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    ∀ (hK : IsIwasawaCompact p K),
      IsParabolicWavePacket hK rho hsmooth hcalc iU l r hA hT Θ →
        IsWavePacket F G K rho hsmooth hcalc Θ := by
  intro hK hΘ
  have hiUp : IsClosedImmersion (iU ≫ p).hom.hom.left :=
    hiU.isGeometricUnipotentRadical.1.comp hp
  obtain ⟨n, e, k, v, c, E, D, hv, hc, hD, hE, hreg, hΘ⟩ := hΘ
  exact ⟨P, M, U, A, inferInstance, inferInstance, inferInstance, inferInstance, p, hp, iU, l,
    hiUp, a, r, inferInstance, inferInstance, inferInstance, hA, hT, hiU,
    hK, n, e, k, v, c, E, D, hv, hc, hD, hE, hreg, hΘ⟩

/-- **Ambient lift of a relative wave packet.** If every regular parameter region is nonempty,
the product of the ambient profile with a relative wave packet is a wave packet in the sense of
`IsWavePacket`. -/
theorem wavePacketAmbientLift_of_regularParameter
    (hR : EisensteinRegularParameterStatement.{0}) : WavePacketAmbientLiftStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ _ p hp iU l a r _ _ _ hA hT hG hiU K hK N d rho hsmooth
    hcalc m eG b hb hb' Θ hΘ
  exact isWavePacket_of_isParabolicWavePacket hiU hK
    (wavePacketParabolicAmbientLift_of_regularParameter hR F G P M U A p iU l a r hA hT hG hiU
      K hK rho hsmooth hcalc eG b hb hb' Θ hΘ)

end Langlands.Global
