import Langlands.Global.LocalWavePacketMainTermLimitStatement
import Langlands.Global.AdelicWavePacketCorootDenominators
import Langlands.Global.BoundedWavePacketReduction

/-! # Measurability of the main term and the exceptional sets in its denominator -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 250000

open CategoryTheory AlgebraicGeometry Filter MeasureTheory Set Module
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Global.ArthurTruncation

open GroupScheme RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces
  Langlands.Analysis Langlands.Analysis.Meromorphic

variable {F : Type} [fieldF : Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [affineG : IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [monoI : Mono i.hom.hom.left]
  {ν : cocharacterLattice T} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)

local notation "I" => @StandardIndex F fieldF G affineG T i monoI hG hi ν
local notation "P[" S "]" => Standard.parabolicScheme i ν (StandardIndex.roots (hG := hG) (hi := hi) (ν := ν) S)
local notation "L[" S "]" => Standard.leviScheme i ν (StandardIndex.roots (hG := hG) (hi := hi) (ν := ν) S)
local notation "p[" S "]" => Standard.parabolicHom i ν (StandardIndex.roots (hG := hG) (hi := hi) (ν := ν) S)
local notation "l[" S "]" => Standard.leviToParabolic i ν (StandardIndex.roots (hG := hG) (hi := hi) (ν := ν) S)
local notation "Z[" n "]" => (Fin n → ℝ)
local notation "ζ[" n "]" => (volume : Measure Z[n])

variable {J J' : StandardIndex hG hi ν} {Ω Ω' : StandardIndex hG hi ν → Type}
  [∀ S, Fintype (Ω S)] [∀ S, Fintype (Ω' S)]
  (π : ∀ S : StandardIndex hG hi ν,
    Standard.parabolicScheme i ν S.roots ⟶ Standard.leviScheme i ν S.roots)
  (cw : ∀ S : StandardIndex hG hi ν, Ω S →
    (Standard.leviScheme i ν S.roots ⟶ Standard.leviScheme i ν J.roots))
  (cw' : ∀ S : StandardIndex hG hi ν, Ω' S →
    (Standard.leviScheme i ν S.roots ⟶ Standard.leviScheme i ν J'.roots))

/-- The sum of the two transformed exponents with conjugation on the second exponent. -/
def wavePacketPairExponent (S : I) (t : Ω S) (t' : Ω' S)
    (lam : ComplexCharacterParameter F P[J]) (lam' : ComplexCharacterParameter F P[J']) :
    ComplexCharacterParameter F P[S] :=
  weylParameter l[J] (cw S t) (π S) lam +
    weylParameter l[J'] (cw' S t') (π S) (parameterConj F _ lam')

/-- The product of the simple-coroot evaluations outside the target Levi. -/
def wavePacketPairDenominator (S : I) (t : Ω S) (t' : Ω' S)
    (lam : ComplexCharacterParameter F P[J]) (lam' : ComplexCharacterParameter F P[J']) : ℂ :=
  ∏ α ∈ simpleFinset ν hG hi \ S.1,
    complexParameterPairing F P[S] (wavePacketPairExponent hG hi π cw cw' S t t' lam lam')
      (toCharacterDual F i ν S.roots (corootVector D α))

include hν in
/-- Outside the finitely many coroot hyperplanes all the denominators of the main term
are nonzero in the equal-frequency coordinates. -/
theorem ae_wavePacketPairDenominator_ne_zero
    (hπ : ∀ S : I, l[S] ≫ π S = 𝟙 L[S])
    (A₀ : I → CommGroupScheme (Spec (CommRingCat.of F)))
    (a₀ : ∀ S : I, (A₀ S).toGrp ⟶ L[S])
    (r : ∀ S : I, ParabolicRootPresentation p[S] l[S] (a₀ S))
    (w : ∀ S : I, Ω S → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
    (hw : ∀ S t, IsWeylConjugation p[J] l[J] p[S] l[S] (w S t) (cw S t))
    {m n n' u v : ℕ} (b : Basis (Fin m) ℝ (relativeCentralDirections i))
    (f : RestrictionSplitCentre.canonicalTorus F G ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ i = RestrictionSplitCentre.canonicalComponent F G)
    (e : Z[n] ≃ₗ[ℝ] RealCharacterParameter F P[J])
    (e' : Z[n'] ≃ₗ[ℝ] RealCharacterParameter F P[J'])
    (B : (Z[u] × Z[m]) ≃ₗ[ℝ] Z[n]) (B' : (Z[v] × Z[m]) ≃ₗ[ℝ] Z[n'])
    (hB : ∀ u z j, pair T (restrictToTorus F i ν J.roots (e (B (u, z)))) (b j : V T) = z j)
    (ν₁ : Measure Z[u]) (ν₂ : Measure Z[v]) [ν₁.IsAddHaarMeasure] [ν₂.IsAddHaarMeasure] :
    ∀ᵐ p : Z[m] × (Z[u] × Z[v]) ∂(ζ[m].prod (ν₁.prod ν₂)), ∀ S t t',
      wavePacketPairDenominator hG hi D π cw cw' S t t'
        (imaginaryParameter F _ (e (B (p.2.1, p.1))))
        (imaginaryParameter F _ (e' (B' (p.2.2, p.1)))) ≠ 0 := by
  classical
  refine eventually_all.mpr fun S => eventually_all.mpr fun t => eventually_all.mpr fun t' => ?_
  let roots := simpleFinset ν hG hi \ S.1
  have hS : S.roots ⊆ simpleRelativeRoots i ν := fun _ hα =>
    (mem_simpleFinset hG hi).mp ((Finset.mem_powerset.mp S.2) hα)
  have hfactor (α : characterLattice T) (hα : α ∈ roots) :
      ∀ᵐ p : Z[m] × (Z[u] × Z[v]) ∂(ζ[m].prod (ν₁.prod ν₂)),
        complexParameterPairing F P[S]
          (wavePacketPairExponent hG hi π cw cw' S t t'
            (imaginaryParameter F _ (e (B (p.2.1, p.1))))
            (imaginaryParameter F _ (e' (B' (p.2.2, p.1)))))
          (toCharacterDual F i ν S.roots (corootVector D α)) ≠ 0 := by
    have hα' := Finset.mem_sdiff.mp hα
    exact ae_wavePacketCorootFactor_ne_zero hG hi hν D b f hf hS (r J) (r S) (π S) (hπ S)
      (cw S t) (hw S t) (cw' S t') e e' B B' hB ν₁ ν₂
      ((mem_simpleFinset hG hi).mp hα'.1) hα'.2
  exact (eventually_all_finset roots).mpr hfactor |>.mono fun p hp => Finset.prod_ne_zero_iff.mpr hp

variable {n n' : ℕ}
  (e : Z[n] ≃ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν J.roots))
  (e' : Z[n'] ≃ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν J'.roots))

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [(S : StandardIndex hG hi ν) → Fintype (Ω S)] [(S : StandardIndex hG hi ν) → Fintype (Ω' S)] in
private theorem continuous_wavePacketPairEvaluation (S : I) (t : Ω S) (t' : Ω' S)
    (H : RealCharacterDual F P[S]) :
    Continuous (fun p : Z[n] × Z[n'] =>
      complexParameterPairing F P[S]
        (wavePacketPairExponent hG hi π cw cw' S t t'
          (imaginaryParameter F _ (e p.1)) (imaginaryParameter F _ (e' p.2))) H) := by
  let W : Z[n] × Z[n'] →ₗ[ℝ] ComplexCharacterParameter F P[S] :=
    ((weylParameter l[J] (cw S t) (π S)).restrictScalars ℝ ∘ₗ
      imaginaryParameter F P[J] ∘ₗ e.toLinearMap ∘ₗ LinearMap.fst ℝ Z[n] Z[n']) +
    ((weylParameter l[J'] (cw' S t') (π S)).restrictScalars ℝ ∘ₗ
      parameterConj F P[J'] ∘ₗ imaginaryParameter F P[J'] ∘ₗ e'.toLinearMap ∘ₗ
      LinearMap.snd ℝ Z[n] Z[n'])
  exact ((((complexParameterPairing F P[S]).flip H).restrictScalars ℝ).comp W).continuous_of_finiteDimensional

omit [NumberField F] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [(S : StandardIndex hG hi ν) → Fintype (Ω S)] [(S : StandardIndex hG hi ν) → Fintype (Ω' S)] in
/-- Each complete denominator is continuous in the two imaginary parameter charts. -/
theorem continuous_wavePacketPairDenominator (S : I) (t : Ω S) (t' : Ω' S) :
    Continuous (fun p : Z[n] × Z[n'] =>
      wavePacketPairDenominator hG hi D π cw cw' S t t'
        (imaginaryParameter F _ (e p.1)) (imaginaryParameter F _ (e' p.2))) := by
  classical
  exact continuous_finsetProd _ fun α _ => continuous_wavePacketPairEvaluation hG hi π cw cw' e e'
    S t t' (toCharacterDual F i ν S.roots (corootVector D α))

section MainTerm

variable {K : Subgroup (AdelicGroupPoints F G)}
  (hK : ∀ S : StandardIndex hG hi ν, IsIwasawaCompact (Standard.parabolicHom i ν S.roots) K)
  (μM : ∀ S : StandardIndex hG hi ν, Measure (AdelicGroupPoints F (Standard.leviScheme i ν S.roots)))
  {nS : StandardIndex hG hi ν → ℕ}
  (eS : ∀ S : StandardIndex hG hi ν,
    Z[nS S] ≃ₗ[ℝ] RealCharacterParameter F (Standard.parabolicScheme i ν S.roots))
  (βS : ∀ S : StandardIndex hG hi ν, Z[nS S] → ℝ)
  {m k k' a a' : ℕ} (cd : Fin m → V T)
  (ψ : ∀ S : StandardIndex hG hi ν, Ω S → Fin k → Fin a → AdelicGroupPoints F G → ℂ)
  (ψ' : ∀ S : StandardIndex hG hi ν, Ω' S → Fin k' → Fin a' → AdelicGroupPoints F G → ℂ)
  (coeff : ∀ S : StandardIndex hG hi ν, Ω S → Fin k → Fin a →
      ComplexCharacterParameter F (Standard.parabolicScheme i ν J.roots) → ℂ)
  (coeff' : ∀ S : StandardIndex hG hi ν, Ω' S → Fin k' → Fin a' →
      ComplexCharacterParameter F (Standard.parabolicScheme i ν J'.roots) → ℂ)

/-- The individual main term of the compact-uniform asymptotic formula. -/
def wavePacketPairMainTerm (j : Fin k) (j' : Fin k') (Tp : V T)
    (lam : ComplexCharacterParameter F P[J]) (lam' : ComplexCharacterParameter F P[J']) : ℂ :=
  ∑ S : I, ∑ t : Ω S, ∑ t' : Ω' S,
    (corootCovolume hG hi ν D S (eS S) cd : ℂ) *
      Complex.exp (complexParameterPairing F P[S] (wavePacketPairExponent hG hi π cw cw' S t t' lam lam')
        (toCharacterDual F i ν S.roots Tp)) *
      (∑ i₁, ∑ i₂, coeff S t j i₁ lam * (starRingEnd ℂ) (coeff' S t' j' i₂ lam') *
        inducedInnerProduct K (hK S).isCompact p[S] l[S] (μM S) (eS S) (βS S)
          (ψ S t j i₁) (ψ' S t' j' i₂)) /
      wavePacketPairDenominator hG hi D π cw cw' S t t' lam lam'

/-- The main term is almost everywhere strongly measurable on the ambient set mapped
into the spectral supports in the holomorphy domains of the two coefficient families. -/
def WavePacketPairMainTermMeasurabilityStatement : Prop :=
  ∀ {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (mu : Measure X) {S : Set X}, MeasurableSet S →
    ∀ (f : X → Z[n] × Z[n']), Continuous f →
    ∀ {C : Set Z[n]} {C' : Set Z[n']}, MapsTo f S (C ×ˢ C') →
    ∀ {DM : Set (ComplexCharacterParameter F P[J])} {DM' : Set (ComplexCharacterParameter F P[J'])},
    (∀ x ∈ C, imaginaryParameter F _ (e x) ∈ DM) →
    (∀ x ∈ C', imaginaryParameter F _ (e' x) ∈ DM') →
    (∀ S t j a, IsMeromorphicInCoordinatesOn (coeff S t j a) DM) →
    (∀ S t j a, IsMeromorphicInCoordinatesOn (coeff' S t j a) DM') →
    ∀ (j : Fin k) (j' : Fin k') (Tp : V T),
    AEStronglyMeasurable (fun z => wavePacketPairMainTerm hG hi D π cw cw' hK μM eS βS cd ψ ψ'
      coeff coeff' j j' Tp (imaginaryParameter F _ (e (f z).1))
        (imaginaryParameter F _ (e' (f z).2))) (mu.restrict S)

/-- Use continuity of the coefficients on the supports and measurability of the totalized
division by the coroot denominator. -/
theorem aestronglyMeasurable_wavePacketPairMainTerm :
    WavePacketPairMainTermMeasurabilityStatement hG hi D π cw cw' e e' hK μM eS βS cd ψ ψ'
      coeff coeff' := by
  classical
  intro X _ _ _ mu S hS f hf C C' hmap DM DM' hC hC' hc hc' j j' Tp
  have hcoeff (Q : I) (t : Ω Q) (a₁ : Fin a) :
      ContinuousOn (fun z => coeff Q t j a₁ (imaginaryParameter F _ (e (f z).1))) S := by
    have hc₁ := (BoundedWavePacket.isOpen_and_continuousOn_of_isMeromorphicInCoordinatesOn
      ((imaginaryParameter F P[J]).comp e.toLinearMap) (hc Q t j a₁)).2
    exact hc₁.comp hf.fst.continuousOn fun z hz => hC _ (hmap hz).1
  have hcoeff' (Q : I) (t' : Ω' Q) (a₂ : Fin a') :
      ContinuousOn (fun z => coeff' Q t' j' a₂ (imaginaryParameter F _ (e' (f z).2))) S := by
    have hc₂ := (BoundedWavePacket.isOpen_and_continuousOn_of_isMeromorphicInCoordinatesOn
      ((imaginaryParameter F P[J']).comp e'.toLinearMap) (hc' Q t' j' a₂)).2
    exact hc₂.comp hf.snd.continuousOn fun z hz => hC' _ (hmap hz).2
  apply AEMeasurable.aestronglyMeasurable
  unfold wavePacketPairMainTerm
  refine Finset.aemeasurable_fun_sum _ fun Q _ =>
    Finset.aemeasurable_fun_sum _ fun t _ => Finset.aemeasurable_fun_sum _ fun t' _ => ?_
  have hexp := Complex.continuous_exp.comp
    ((continuous_wavePacketPairEvaluation hG hi π cw cw' e e' Q t t'
      (toCharacterDual F i ν Q.roots Tp)).comp hf)
  have hsum : ContinuousOn (fun z => ∑ a₁, ∑ a₂,
      coeff Q t j a₁ (imaginaryParameter F _ (e (f z).1)) *
        (starRingEnd ℂ) (coeff' Q t' j' a₂ (imaginaryParameter F _ (e' (f z).2))) *
        inducedInnerProduct K (hK Q).isCompact p[Q] l[Q] (μM Q) (eS Q) (βS Q)
          (ψ Q t j a₁) (ψ' Q t' j' a₂)) S :=
    continuousOn_finsetSum _ fun a₁ _ => continuousOn_finsetSum _ fun a₂ _ =>
      ((hcoeff Q t a₁).mul (Complex.continuous_conj.comp_continuousOn (hcoeff' Q t' a₂))).mul
        continuousOn_const
  have hden := (continuous_wavePacketPairDenominator hG hi D π cw cw' e e' Q t t').comp hf
  exact ((continuousOn_const.mul hexp.continuousOn).mul hsum).aemeasurable hS |>.div
    hden.measurable.aemeasurable

end MainTerm

end Langlands.Global.ArthurTruncation
