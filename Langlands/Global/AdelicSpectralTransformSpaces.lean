import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Analysis.Meromorphic.LinearCoordinates

/-! # The Hilbert spaces of the spectral transform

Arthur 2005, §7 (pp.32–35), and Getz–Hahn (10.22)–(10.23): the Hilbert space `H_P` of the
induced representation `Ind_{P(𝔸)}^{G(𝔸)}(L²_disc)`, realized in Iwasawa coordinates on
`K × M(F) \ M(𝔸)`; the operators `M(w, λ) : H_P → H_{P'}` for imaginary `λ`, characterized by
their values on Lapid's `A^2_P`; the Hilbert space of families `(F_P)_P` of square-integrable
`H_P`-valued functions on `i𝔞_P^*` with the weighted norm `∑_P n_P⁻¹ ∫ ‖F_P(λ)‖² dλ`; its
subspace `L̂` of families with `F_{P'}(wλ) = M(w, λ) F_P(λ)`; and its smooth compactly supported
families. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct ENNReal

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Analysis.Meromorphic

section InducedHilbert

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]

/-- The measure `β(H_M(m)) δ_P(m)⁻¹ dk dm` on `K × M(F) \ M(𝔸)`, where `dk` is the Haar
probability measure on `K`, `dm` the quotient of `μ_M` by counting measure on `M(F)`, and `β` is
read in the coordinates `e`. For `φ ∈ A^2_P` and `β ≥ 0` with integral `1`, the squared norm of
`(k, m) ↦ φ(mk)` for this measure is `(φ, φ)_P` (`inducedInnerProduct`). -/
def inducedL2Measure (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) (l : M ⟶ P)
    (μM : Measure (AdelicGroupPoints F M)) {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ) :
    Measure (K × RationalQuotient F M) :=
  ((compactHaarProbability F G K hKc).prod
      (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
        (isDiscrete_rationalSubgroup F M) μM)).withDensity fun x =>
    ENNReal.ofReal
      (β (parameterCoordinates F P e (characterLog F P (map F M P l x.2.out))) *
        ‖parameterPower F P (-modulusParameter F P) (map F M P l x.2.out)‖)

/-- The restriction `(k, m) ↦ φ(mk)` of a function on `G(𝔸)` to Iwasawa coordinates
`K × M(F) \ M(𝔸)`, using the chosen representative `m` of a coset. -/
def inducedRestriction (K : Subgroup (AdelicGroupPoints F G)) (p : P ⟶ G) (l : M ⟶ P)
    (φ : AdelicGroupPoints F G → ℂ) : K × RationalQuotient F M → ℂ :=
  fun x => φ (map F P G p (map F M P l x.2.out) * (x.1 : AdelicGroupPoints F G))

variable [IsAffineHom G.X.hom] [IsAffine U.X.left]

/-- The Hilbert space `H_P` of Arthur §7 (`Ind_{P(𝔸)}^{G(𝔸)}(L²_disc)`, Getz–Hahn (10.22)): the
closure in `L²(K × M(F) \ M(𝔸), β δ_P⁻¹ dk dm)` of the span of the restrictions of the elements
of Lapid's `A^2_P`. -/
def inducedHilbertSpace (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (p : P ⟶ G) (iU : U ⟶ P) (l : M ⟶ P)
    (μM : Measure (AdelicGroupPoints F M)) {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ) :
    Submodule ℂ (Lp ℂ 2 (inducedL2Measure K hKc l μM e β)) :=
  (Submodule.span ℂ {f : Lp ℂ 2 (inducedL2Measure K hKc l μM e β) |
    ∃ φ, IsSquareIntegrableInducedForm K hKc rho hsmooth hcalc p iU l φ ∧
      f =ᵐ[inducedL2Measure K hKc l μM e β] inducedRestriction K p l φ}).topologicalClosure

end InducedHilbert

section ImaginaryIntertwining

variable {F : Type} [Field F] [NumberField F]
  {G P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  [IsAffine P'.X.left] [LocallyOfFiniteType P'.X.hom]
  [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom] [IsAffine U'.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {p' : P' ⟶ G}
  [IsClosedImmersion p'.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

/-- `Mop` is the family of operators `M(w, λ) : H_P → H_{P'}` at the imaginary parameters
`λ = i e(x)` (Arthur 2005, §7; Mœglin–Waldspurger IV.1.11 (b), VI.2.1 (i)): whenever
`v ∈ A^2_P` satisfies `M(w, λ) v = ∑ q, coeff q λ • ψ q` for `Re λ` sufficiently regular, with
`ψ q ∈ A^2_{P'}` and coefficients meromorphic with a domain of holomorphy `DM` containing
`i(X^*(P) ⊗ ℝ)`, then for every `x` the operator `Mop x` sends the class of the restriction of
`v` to `H_P` to the class of the restriction of `∑ q, coeff q (i e(x)) • ψ q`. -/
def IsImaginaryIntertwiningOperator (hK : IsIwasawaCompact p K)
    (hK' : IsIwasawaCompact p' K) {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left] (a : A.toGrp ⟶ M)
    (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (iU' : U' ⟶ P')
    (l' : M' ⟶ P') [IsClosedImmersion (iU' ≫ p').hom.hom.left] (π' : P' ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (cw : M' ⟶ M)
    (μM : Measure (AdelicGroupPoints F M)) (μM' : Measure (AdelicGroupPoints F M'))
    {n n' : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (e' : (Fin n' → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P') (β : (Fin n → ℝ) → ℝ)
    (β' : (Fin n' → ℝ) → ℝ)
    (Mop : (Fin n → ℝ) →
      inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β →L[ℂ]
        inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc p' iU' l' μM' e' β') : Prop :=
  ∀ v : AdelicGroupPoints F G → ℂ,
    IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l v →
  ∀ (m : ℕ) (ψ : Fin m → AdelicGroupPoints F G → ℂ)
    (coeff : Fin m → ComplexCharacterParameter F P → ℂ) (DM : Set (ComplexCharacterParameter F P)),
    (∀ q, IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (ψ q)) →
    Set.range (imaginaryParameter F P) ⊆ DM →
    (∀ q, IsMeromorphicInCoordinatesOn (coeff q) DM) →
    (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
      hK.intertwiningOperator hK' iU l iU' cw π' w v lam g = ∑ q, coeff q lam * ψ q g) →
  ∀ h : inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β,
    ⇑(h : Lp ℂ 2 (inducedL2Measure K hK.isCompact l μM e β)) =ᵐ[inducedL2Measure K hK.isCompact l μM e β]
      inducedRestriction K p l v →
  ∀ x : Fin n → ℝ,
    ⇑(Mop x h : Lp ℂ 2 (inducedL2Measure K hK'.isCompact l' μM' e' β')) =ᵐ[inducedL2Measure K hK'.isCompact l' μM' e' β']
      inducedRestriction K p' l' fun g => ∑ q, coeff q (imaginaryParameter F P (e x)) * ψ q g

end ImaginaryIntertwining

/-- `spectralMeasure n` has the null sets of Lebesgue measure. -/
theorem ae_spectralMeasure_eq (n : ℕ) :
    ae (spectralMeasure n) = ae (volume : Measure (Fin n → ℝ)) :=
  Measure.ae_ennreal_smul_measure_eq
    (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)) _

/-- A nonzero multiple of `spectralMeasure n` has the null sets of Lebesgue measure. -/
theorem ae_smul_spectralMeasure_eq (n : ℕ) {c : ℝ≥0∞} (hc : c ≠ 0) :
    ae (c • spectralMeasure n) = ae (volume : Measure (Fin n → ℝ)) := by
  rw [Measure.ae_ennreal_smul_measure_eq hc, ae_spectralMeasure_eq]

section Intertwined

variable {α β E E' : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {ma ma1 : Measure α} {nb : Measure β} {τ : α → β} {A : α → E →L[ℂ] E'} {q : ℝ≥0∞}

/-- The relation `f'(τ x) = A x (f x)` for almost every `x` holds for `f = 0`, `f' = 0`. -/
theorem ae_intertwined_zero (hτ : Filter.Tendsto τ (ae ma) (ae nb)) (h₁ : ae ma ≤ ae ma1) :
    ∀ᵐ x ∂ma, (0 : Lp E' q nb) (τ x) = A x ((0 : Lp E q ma1) x) := by
  filter_upwards [hτ.eventually (Lp.coeFn_zero E' q nb), h₁ (Lp.coeFn_zero E q ma1)]
    with x h h'
  rw [h, h', Pi.zero_apply, Pi.zero_apply, map_zero]

/-- The relation `f'(τ x) = A x (f x)` for almost every `x` is preserved by sums. -/
theorem ae_intertwined_add (hτ : Filter.Tendsto τ (ae ma) (ae nb)) (h₁ : ae ma ≤ ae ma1)
    (f g : Lp E q ma1) (f' g' : Lp E' q nb) (hf : ∀ᵐ x ∂ma, f' (τ x) = A x (f x))
    (hg : ∀ᵐ x ∂ma, g' (τ x) = A x (g x)) :
    ∀ᵐ x ∂ma, (f' + g') (τ x) = A x ((f + g) x) := by
  filter_upwards [hf, hg, hτ.eventually (Lp.coeFn_add f' g'), h₁ (Lp.coeFn_add f g)]
    with x h1 h2 h3 h4
  rw [h3, h4, Pi.add_apply, Pi.add_apply, map_add, h1, h2]

/-- The relation `f'(τ x) = A x (f x)` for almost every `x` is preserved by scalars. -/
theorem ae_intertwined_smul (hτ : Filter.Tendsto τ (ae ma) (ae nb)) (h₁ : ae ma ≤ ae ma1)
    (a : ℂ) (f : Lp E q ma1) (f' : Lp E' q nb) (hf : ∀ᵐ x ∂ma, f' (τ x) = A x (f x)) :
    ∀ᵐ x ∂ma, (a • f') (τ x) = A x ((a • f) x) := by
  filter_upwards [hf, hτ.eventually (Lp.coeFn_smul a f'), h₁ (Lp.coeFn_smul a f)]
    with x h1 h2 h3
  rw [h2, h3, Pi.smul_apply, Pi.smul_apply, map_smul, h1]

end Intertwined

section Families

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {I : Type} [Fintype I] {P M U : I → GroupScheme (Spec (CommRingCat.of F))}
  [∀ i, IsAffine (P i).X.left] [∀ i, LocallyOfFiniteType (P i).X.hom]
  [∀ i, IsAffine (M i).X.left] [∀ i, LocallyOfFiniteType (M i).X.hom]
  [∀ i, IsAffine (U i).X.left]
  {p : ∀ i, P i ⟶ G} [∀ i, IsClosedImmersion (p i).hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)}

/-- The Hilbert space of families `(F_i)_{i ∈ I}` of square-integrable functions
`F_i : i𝔞_{P i}^* → H_{P i}`, in the coordinates `e i` with the measure `dλ` of
`spectralMeasure`, with the norm `‖F‖² = ∑ i, (nP i)⁻¹ ∫ ‖F_i(λ)‖² dλ` (Arthur Theorem 7.2(b),
Getz–Hahn (10.22)). -/
abbrev spectralFamilySpace (hK : ∀ i, IsIwasawaCompact (p i) K) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (iU : ∀ i, U i ⟶ P i)
    (l : ∀ i, M i ⟶ P i) (μM : ∀ i, Measure (AdelicGroupPoints F (M i))) (n : I → ℕ)
    (e : ∀ i, (Fin (n i) → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P i))
    (β : ∀ i, (Fin (n i) → ℝ) → ℝ) (nP : I → ℕ) :=
  PiLp 2 fun i =>
    Lp (inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) (μM i)
      (e i) (β i)) 2 (((nP i : ℝ≥0∞))⁻¹ • spectralMeasure (n i))

variable (hK : ∀ i, IsIwasawaCompact (p i) K) {N d : ℕ}
  (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth) (iU : ∀ i, U i ⟶ P i)
  (l : ∀ i, M i ⟶ P i) (μM : ∀ i, Measure (AdelicGroupPoints F (M i))) (n : I → ℕ)
  (e : ∀ i, (Fin (n i) → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P i))
  (β : ∀ i, (Fin (n i) → ℝ) → ℝ) (nP : I → ℕ)

/-- `Φ` is a smooth compactly supported family with values in a finite-dimensional space of
`K`-finite vectors (Arthur Theorem 7.2(b)): for almost every `x`, `Φ_i(x)` is the class of the
restriction of `F_i(x) = ∑ j, c i j x • v i j`, with `v i j ∈ A^2_{P i}` and `c i j` smooth and
compactly supported. -/
def IsSmoothCompactFamily (k : I → ℕ) (v : ∀ i, Fin (k i) → AdelicGroupPoints F G → ℂ)
    (c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ)
    (Φ : spectralFamilySpace hK rho hsmooth hcalc iU l μM n e β nP) : Prop :=
  (∀ i j,
    IsSquareIntegrableInducedForm K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i)
      (v i j)) ∧
  (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (c i j) ∧ HasCompactSupport (c i j)) ∧
  ∀ i, ∀ᵐ x ∂(spectralMeasure (n i)),
    ⇑(Φ i x : Lp ℂ 2 (inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i)))
      =ᵐ[inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i)]
      inducedRestriction K (p i) (l i) (fun g => ∑ j, c i j x * v i j g)

set_option synthInstance.maxHeartbeats 400000 in
/-- Arthur's space `L̂` (Theorem 7.2(b), Getz–Hahn (10.22)): the families `Φ` in
`spectralFamilySpace` with `Φ_{i'}(w λ) = M(w, λ) Φ_i(λ)` for almost every `λ` and every
element `(w i i' t, cw i i' t)` of `Ω(P i, P i')`, where `M(w, λ)` is given by the operators
`Mop i i' t x` at `λ = i e_i(x)` and `w λ` by the coordinate change
`x ↦ (e i')⁻¹ (w (e i x))`, which is assumed to preserve Lebesgue measure. -/
def symmetricFamilySpace (T : I → I → Type) (cw : ∀ i i', T i i' → (M i' ⟶ M i))
    (π : ∀ i, P i ⟶ M i)
    (hw : ∀ i i' t, MeasurePreserving
      (fun x => (e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x)))
      volume volume)
    (Mop : ∀ i i', T i i' → (Fin (n i) → ℝ) →
      inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) (μM i) (e i)
          (β i) →L[ℂ]
        inducedHilbertSpace K (hK i').isCompact rho hsmooth hcalc (p i') (iU i') (l i')
          (μM i') (e i') (β i')) :
    Submodule ℂ (spectralFamilySpace hK rho hsmooth hcalc iU l μM n e β nP) where
  carrier := {Φ | ∀ i i' t, ∀ᵐ x ∂(spectralMeasure (n i)),
    Φ i' ((e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x))) =
      Mop i i' t x (Φ i x)}
  zero_mem' := by
    intro i i' t
    have hc : ∀ j, ((nP j : ℝ≥0∞))⁻¹ ≠ 0 := fun j =>
      ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
    have hτ : Filter.Tendsto (fun x => (e i').symm (realWeylParameter (l i) (cw i i' t) (π i')
        (e i x))) (ae (spectralMeasure (n i))) (ae (((nP i' : ℝ≥0∞))⁻¹ •
          spectralMeasure (n i'))) := by
      rw [ae_spectralMeasure_eq, ae_smul_spectralMeasure_eq _ (hc i')]
      exact (hw i i' t).quasiMeasurePreserving.tendsto_ae
    have h₁ : ae (spectralMeasure (n i)) ≤ ae (((nP i : ℝ≥0∞))⁻¹ • spectralMeasure (n i)) := by
      rw [ae_spectralMeasure_eq, ae_smul_spectralMeasure_eq _ (hc i)]
    exact ae_intertwined_zero (A := Mop i i' t) hτ h₁
  add_mem' := by
    intro Φ Ψ hΦ hΨ i i' t
    have hc : ∀ j, ((nP j : ℝ≥0∞))⁻¹ ≠ 0 := fun j =>
      ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
    have hτ : Filter.Tendsto (fun x => (e i').symm (realWeylParameter (l i) (cw i i' t) (π i')
        (e i x))) (ae (spectralMeasure (n i))) (ae (((nP i' : ℝ≥0∞))⁻¹ •
          spectralMeasure (n i'))) := by
      rw [ae_spectralMeasure_eq, ae_smul_spectralMeasure_eq _ (hc i')]
      exact (hw i i' t).quasiMeasurePreserving.tendsto_ae
    have h₁ : ae (spectralMeasure (n i)) ≤ ae (((nP i : ℝ≥0∞))⁻¹ • spectralMeasure (n i)) := by
      rw [ae_spectralMeasure_eq, ae_smul_spectralMeasure_eq _ (hc i)]
    exact ae_intertwined_add hτ h₁ (Φ i) (Ψ i) (Φ i') (Ψ i') (hΦ i i' t) (hΨ i i' t)
  smul_mem' := by
    intro a Φ hΦ i i' t
    have hc : ∀ j, ((nP j : ℝ≥0∞))⁻¹ ≠ 0 := fun j =>
      ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
    have hτ : Filter.Tendsto (fun x => (e i').symm (realWeylParameter (l i) (cw i i' t) (π i')
        (e i x))) (ae (spectralMeasure (n i))) (ae (((nP i' : ℝ≥0∞))⁻¹ •
          spectralMeasure (n i'))) := by
      rw [ae_spectralMeasure_eq, ae_smul_spectralMeasure_eq _ (hc i')]
      exact (hw i i' t).quasiMeasurePreserving.tendsto_ae
    have h₁ : ae (spectralMeasure (n i)) ≤ ae (((nP i : ℝ≥0∞))⁻¹ • spectralMeasure (n i)) := by
      rw [ae_spectralMeasure_eq, ae_smul_spectralMeasure_eq _ (hc i)]
    exact ae_intertwined_smul hτ h₁ a (Φ i) (Φ i') (hΦ i i' t)

end Families

end Langlands.Global.AdelicGroupPoints
