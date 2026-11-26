import Langlands.Global.AdelicSpectralTransformInputs
import Langlands.Global.AdelicLeftFiniteConvolutionApproximation
import Langlands.Global.AdelicInducedInnerProductIntegrable

/-! # From symmetric convolution stability to wave-packet translation -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The sum of spectral integrals on the adelic group itself, whose evaluation at quotient
representatives is `wavePacketSum`. -/
def wavePacketSumOnGroup {F : Type} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} {I : Type} [Fintype I]
    {P : I → GroupScheme (Spec (CommRingCat.of F))} {n : I → ℕ}
    (e : ∀ i, (Fin (n i) → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P i)) (nP : I → ℕ)
    {k : I → ℕ} (c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ)
    (E : ∀ i, Fin (k i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) : ℂ :=
  ∑ i, ((nP i : ℂ))⁻¹ * ∫ x, ∑ j, c i j x * E i j (imaginaryParameter F (P i) (e i x)) g
    ∂(spectralMeasure (n i))

set_option synthInstance.maxHeartbeats 400000 in
/-- Pointwise symmetric wave packets are continuous, left invariant under the rational points,
and closed under convolution by the specified left-finite test functions. -/
def SymmetricWavePacketConvolutionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (I : Type) [Fintype I]
    (P M U : I → GroupScheme (Spec (CommRingCat.of F)))
    (A : I → CommGroupScheme (Spec (CommRingCat.of F)))
    [∀ i, IsAffine (P i).X.left] [∀ i, IsAffine (M i).X.left]
    [∀ i, LocallyOfFiniteType (M i).X.hom] [∀ i, IsAffine (U i).X.left]
    (p : ∀ i, P i ⟶ G) [∀ i, IsClosedImmersion (p i).hom.hom.left] (iU : ∀ i, U i ⟶ P i)
    (l : ∀ i, M i ⟶ P i) [∀ i, IsClosedImmersion (iU i ≫ p i).hom.hom.left]
    (a : ∀ i, (A i).toGrp ⟶ M i) (r : ∀ i, ParabolicRootPresentation (p i) (l i) (a i))
    [∀ i, Mono (r i).data.i.hom.hom.left] [∀ i, Fintype (relativeWeylGroup (r i).data.i)]
    [∀ i, Mono (CommGroupScheme.groupHom (r i).data.f).hom.hom.left]
    (hA : ∀ i, IsSplitTorus (A i).toGrp) (hT : ∀ i, IsSplitTorus (r i).data.T.toGrp)
    (π : ∀ i, P i ⟶ M i),
    haveI : ∀ i, LocallyOfFiniteType (P i).X.hom := fun i =>
      IsClosedSubgroup.locallyOfFiniteType (j := p i)
        (inferInstance : IsClosedImmersion (p i).hom.hom.left)
    IsConnectedReductive G → (∀ i, LeviSubgroup.IsGeometricUnipotentRadical (iU i)) →
    (∀ i, IsIso (subgroupMultiplication (l i) (iU i))) → (∀ i, l i ≫ π i = 𝟙 (M i)) →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : ∀ i, IsIwasawaCompact (p i) K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM : ∀ i, Measure (AdelicGroupPoints F (M i))) [∀ i, (μM i).IsHaarMeasure],
      (∀ i, IsIwasawaCompatibleMeasure K (hK i).isCompact (p i) (iU i) (l i) (μM i)) →
    ∀ (n : I → ℕ) (e : ∀ i, (Fin (n i) → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P i))
      (β : ∀ i, (Fin (n i) → ℝ) → ℝ),
      (∀ i, Continuous (β i) ∧ HasCompactSupport (β i) ∧ (∀ y, 0 ≤ β i y) ∧
        ∫ y, β i y = 1) →
    ∀ (T : I → I → Type) [∀ i i', Fintype (T i i')]
      (w : ∀ i i', T i i' → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
      (cw : ∀ i i', T i i' → (M i' ⟶ M i)),
      (∀ i i' t, IsWeylConjugation (p i) (l i) (p i') (l i') (w i i' t) (cw i i' t)) →
      (∀ i i', Function.Injective (fun t => weylParameter (l i) (cw i i' t) (π i'))) →
      (∀ i i', ∀ s ∈ weylParameterSet (p i) (l i) (p i') (l i') (π i'),
        ∃ t, weylParameter (l i) (cw i i' t) (π i') = s) →
    ∀ (hw : ∀ i i' t, MeasurePreserving
        (fun x => (e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x)))
        volume volume),
    let nP : I → ℕ := fun i => ∑ i', Fintype.card (T i i')
    ∀ (Mop : ∀ i i', T i i' → (Fin (n i) → ℝ) →
        inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) (μM i)
            (e i) (β i) →L[ℂ]
          inducedHilbertSpace K (hK i').isCompact rho hsmooth hcalc (p i') (iU i') (l i')
            (μM i') (e i') (β i')),
      (∀ i i' t, IsImaginaryIntertwiningOperator (hK i) (hK i') rho hsmooth hcalc (iU i) (l i)
        (a i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t) (μM i) (μM i')
        (e i) (e i') (β i) (β i') (Mop i i' t)) →
    ∀ (Φ : symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop)
      (k : I → ℕ) (v : ∀ i, Fin (k i) → AdelicGroupPoints F G → ℂ)
      (c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ)
      (E : ∀ i, Fin (k i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ)
      (D : ∀ i, Set (ComplexCharacterParameter F (P i))),
      IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k v c Φ.1 →
      (∀ i, IsEisensteinContinuation (hK i) (r i) (hA i) (hT i) (v i) (E i) (D i)) →
    let Θ := wavePacketSumOnGroup e nP c E
    Continuous Θ ∧ IsLeftInvariantUnder F G (rationalSubgroup F G) Θ ∧
    ∀ (kernel : AdelicGroupPoints F G → ℂ),
      IsLeftFiniteTestFunction F G (K.comap (ofInfinite F G).toMonoidHom) kernel →
    ∃ (Φ' : symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop)
      (k' : I → ℕ) (v' : ∀ i, Fin (k' i) → AdelicGroupPoints F G → ℂ)
      (c' : ∀ i, Fin (k' i) → (Fin (n i) → ℝ) → ℂ)
      (E' : ∀ i, Fin (k' i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ)
      (D' : ∀ i, Set (ComplexCharacterParameter F (P i))),
      IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k' v' c' Φ'.1 ∧
      (∀ i, IsEisensteinContinuation (hK i) (r i) (hA i) (hT i) (v' i) (E' i) (D' i)) ∧
      rightConvolution F G kernel Θ = wavePacketSumOnGroup e nP c' E'

/-- Symmetric wave-packet convolution stability, square integrability of the packets, and
right-translation separation imply the published approximation statement. -/
def WavePacketTranslationOfConvolutionStatement : Prop :=
  RightTranslationTestFunctionSeparationStatement → SymmetricFamilyGramStatement →
    SymmetricWavePacketConvolutionStatement → WavePacketTranslationStatement

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem wavePacketTranslation_of_convolution : WavePacketTranslationOfConvolutionStatement := by
  intro hSep hGram hConv F _ _ G _ _ _ I _ P M U A _ _ _ _ p _ iU l _ a r _ _ _ hA hT π
    hG hUR hMul hπ K hK N d rho hsmooth hcalc hKm hrho μM _ hμM n e β hβ T _ w cw hW hinj hsurj
    hw nP μG Mop hMop Φ k v c E D hΦ hE y ε hε
  let : ∀ i, LocallyOfFiniteType (P i).X.hom := fun i =>
    IsClosedSubgroup.locallyOfFiniteType (j := p i) (inferInstance : IsClosedImmersion (p i).hom.hom.left)
  let Θ := wavePacketSumOnGroup e nP c E
  have hData := hConv F G I P M U A p iU l a r hA hT π hG hUR hMul hπ
    K hK rho hsmooth hcalc hKm hrho μM hμM n e β hβ T w cw hW hinj hsurj hw Mop hMop
    Φ k v c E D hΦ hE
  obtain ⟨hΘc, hΘinv, hΘconv⟩ := hData
  have hL (Ψ : symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop)
      (k' : I → ℕ) (v' : ∀ i, Fin (k' i) → AdelicGroupPoints F G → ℂ)
      (c' : ∀ i, Fin (k' i) → (Fin (n i) → ℝ) → ℂ)
      (E' : ∀ i, Fin (k' i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ)
      (D' : ∀ i, Set (ComplexCharacterParameter F (P i)))
      (hΨ : IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k' v' c' Ψ.1)
      (hE' : ∀ i, IsEisensteinContinuation (hK i) (r i) (hA i) (hT i) (v' i) (E' i) (D' i)) :
      MemLp (wavePacketSum e nP c' E') 2 μG :=
    (hGram F G I P M U A p iU l a r hA hT π hG hUR hMul hπ K hK rho hsmooth hcalc hKm hrho μM hμM
      n e β hβ T w cw hW hinj hsurj hw Mop hMop Ψ Ψ k' v' c' E' D' k' v' c' E' D' hΨ hE' hΨ hE').1
  have hΘL : MemLp (fun z : RationalQuotient F G => Θ z.out) 2 μG := hL Φ k v c E D hΦ hE
  have hCL (kernel : AdelicGroupPoints F G → ℂ)
      (hker : IsLeftFiniteTestFunction F G (K.comap (ofInfinite F G).toMonoidHom) kernel) :
      MemLp (fun z : RationalQuotient F G => rightConvolution F G kernel Θ z.out) 2 μG := by
    obtain ⟨Ψ, k', v', c', E', D', hΨ, hE', hEq⟩ := hΘconv kernel hker
    change MemLp (fun z : RationalQuotient F G => rightConvolution F G kernel
      (wavePacketSumOnGroup e nP c E) z.out) 2 μG
    rw [hEq]
    exact hL Ψ k' v' c' E' D' hΨ hE'
  have happ := leftFiniteConvolutionApproximation hSep F G hG K hKm Θ hΘc hΘinv
    hΘL hCL y ε hε
  obtain ⟨kernel, hker, herr⟩ := happ
  have hNew := hΘconv kernel hker
  obtain ⟨Ψ, k', v', c', E', D', hΨ, hE', hEq⟩ := hNew
  refine ⟨Ψ, k', v', c', E', D', hΨ, hE', ?_⟩
  have hfun : (fun z : RationalQuotient F G => wavePacketSum e nP c E
      (LeftCosetSpace.mk (rationalSubgroup F G) (z.out * y)) - wavePacketSum e nP c' E' z) =
        fun z => Θ (z.out * y) - rightConvolution F G kernel Θ z.out := by
    funext z
    change Θ (LeftCosetSpace.mk (rationalSubgroup F G) (z.out * y)).out -
      wavePacketSumOnGroup e nP c' E' z.out = Θ (z.out * y) - rightConvolution F G kernel Θ z.out
    rw [LeftCosetSpace.out_mk_of_invariant _ Θ hΘinv]
    exact congrArg (fun q : ℂ => Θ (z.out * y) - q) (congrFun hEq z.out).symm
  rw [hfun]
  exact herr

end Langlands.Global
