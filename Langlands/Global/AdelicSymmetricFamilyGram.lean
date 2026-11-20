import Langlands.Global.AdelicSpectralTransformInputs
import Langlands.Global.AdelicWavePacketInnerProductStatement
import Langlands.Global.AdelicIntertwiningSquareIntegrableExpansionStatement
import Langlands.Global.AdelicInducedRestrictionMemLpStatement
import Langlands.Global.AdelicInducedL2Inner
import Langlands.Global.AdelicWeylFamilyCounting
import Langlands.Analysis.Meromorphic.CoordinateGluing
import Langlands.Analysis.MeasurePreservingLinearCoordinates

/-! # The Gram identity for wave packets of `L̂` from Lapid's inner product formula

Lapid's formula for the inner products of wave packets (`WavePacketInnerProductStatement`;
Lapid 2011, Proposition 2), finite expansions of `M(w, λ)` on `A^2_P` in `A^2_Q` with
coefficients holomorphic near the imaginary axis (`IntertwiningSquareIntegrableExpansionStatement`;
Lapid 2011, §2, p.312) and the square integrability of restrictions of elements of `A^2_P`
(`InducedRestrictionMemLpStatement`) imply `SymmetricFamilyGramStatement`.

For two smooth compactly supported families `Φ`, `Φ'` of Arthur's space `L̂`, Lapid's formula for
the pair `(P_{i'}, P_i)` writes `(Θ'_{i'}, Θ_i)` as the integral over `i𝔞_{P_{i'}}^*` of
`∑_{t ∈ Ω(P_{i'}, P_i)} (M(w_t, λ)Φ'_{i'}(λ), Φ_i(w_t λ))_{P_i}`. The operators `M(w_t, λ)` of
`L̂` act on the classes of the restrictions through the same expansions, so the integrand is
`∑_t ⟨Φ_i(w_t λ), Φ'_i(w_t λ)⟩` by the symmetry of `Φ'`, and the change of variables `λ ↦ w_t λ`
gives `|Ω(P_{i'}, P_i)| ∫ ⟨Φ_i, Φ'_i⟩`. Arthur's normalization
`∑_{i'} |Ω(P_{i'}, P_i)| / n_P(i') = 1` (`sum_card_div_card_eq_one`) then yields
`(W, W') = ∑_i n_P(i)⁻¹ ∫ ⟨Φ_i, Φ'_i⟩ = ⟨Φ, Φ'⟩_{L̂}`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct InnerProductSpace

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Uniform

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- The whole space is open and dense in coordinates. -/
theorem isOpenDenseInCoordinates_univ : IsOpenDenseInCoordinates (Set.univ : Set X) :=
  fun n e => by
    rw [Set.preimage_univ]
    exact ⟨isOpen_univ, dense_univ⟩

/-- A finite intersection of sets open and dense in coordinates, over any finite index type. -/
theorem isOpenDenseInCoordinates_iInter_of_finite {κ : Type*} [Finite κ] {U : κ → Set X}
    (hU : ∀ j, IsOpenDenseInCoordinates (U j)) : IsOpenDenseInCoordinates (⋂ j, U j) :=
  fun n e => by
    rw [Set.preimage_iInter]
    exact ⟨isOpen_iInter_of_finite fun j => (hU j n e).1,
      dense_iInter_of_isOpen (fun j => (hU j n e).1) fun j => (hU j n e).2⟩

/-- The zero function is meromorphic in coordinates on every domain of holomorphy in coordinates
of some function. -/
theorem isMeromorphicInCoordinatesOn_const_zero {g : X → ℂ} {V : Set X}
    (hg : IsMeromorphicInCoordinatesOn g V) :
    IsMeromorphicInCoordinatesOn (fun _ => (0 : ℂ)) V := by
  refine ⟨hg.1, fun n e => ⟨(hg.2 n e).1, (hg.2 n e).2.1, fun mu => ?_, fun s₀ => ?_⟩⟩
  · simp only [Function.comp_def, map_zero]
    exact mdifferentiableOn_const
  · refine ⟨Set.univ, isOpen_univ, isConnected_univ, Set.mem_univ _, fun _ => 1, fun _ => 0,
      mdifferentiableOn_const, ⟨s₀, Set.mem_univ _, one_ne_zero⟩, fun mu => ?_, fun s _ => ?_⟩
    · simp only [map_zero]
      exact mdifferentiableOn_const
    · simp

/-- A finite family meromorphic in coordinates with domain `D` is meromorphic in coordinates with
a domain `D' ⊇ D` that is open and dense in coordinates (`D' = D` for a nonempty family, the
whole space for an empty one). -/
theorem exists_openDense_domain {m : ℕ} {coeff : Fin m → X → ℂ} {D : Set X}
    (h : ∀ q, IsMeromorphicInCoordinatesOn (coeff q) D) :
    ∃ D' : Set X, D ⊆ D' ∧ IsOpenDenseInCoordinates D' ∧
      ∀ q, IsMeromorphicInCoordinatesOn (coeff q) D' := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨Set.univ, Set.subset_univ _, isOpenDenseInCoordinates_univ, fun q => q.elim0⟩
  · exact ⟨D, subset_rfl, (h ⟨0, hm⟩).isOpenDenseInCoordinates, h⟩

/-- Padding a sum over `Fin k` by zeros to a sum over `Fin m`, `k ≤ m`. -/
theorem sum_fin_pad {k m : ℕ} (hkm : k ≤ m) (f : Fin k → ℂ) :
    ∑ q : Fin m, (if h : (q : ℕ) < k then f ⟨q, h⟩ else 0) = ∑ q, f q := by
  let g : ℕ → ℂ := fun q => if h : q < k then f ⟨q, h⟩ else 0
  have h1 : ∑ q : Fin m, (if h : (q : ℕ) < k then f ⟨q, h⟩ else 0) = ∑ q : Fin m, g q := rfl
  have h2 : ∑ q : Fin k, f q = ∑ q : Fin k, g q :=
    Finset.sum_congr rfl fun q _ => by simp [g, q.2]
  rw [h1, h2, Fin.sum_univ_eq_sum_range g m, Fin.sum_univ_eq_sum_range g k]
  refine (Finset.sum_subset (Finset.range_subset_range.2 hkm) fun q _ hq => ?_).symm
  have hq' : ¬ q < k := fun h => hq (Finset.mem_range.2 h)
  simp [g, hq']

/-- Uniform expansions: finitely many expansions `Mv s λ = ∑ q, coeff s q λ • ψ s q` (for
regular `λ`), each with its own length and domain of holomorphy containing `Z`, can be
replaced by expansions of one common length `m` with one common domain of holomorphy
containing `Z`, padding with zero coefficients. -/
theorem exists_uniform_expansions {Y : Type*} {S : Type*} [Fintype S]
    (Z : Set X) (Pr : (Y → ℂ) → Prop) (Mv : S → X → Y → ℂ) (reg : ℝ → X → Prop)
    (h : ∀ s, ∃ (k : ℕ) (ψ : Fin k → Y → ℂ) (coeff : Fin k → X → ℂ) (D : Set X),
      (∀ q, Pr (ψ q)) ∧ Z ⊆ D ∧ (∀ q, IsMeromorphicInCoordinatesOn (coeff q) D) ∧
        ∃ R : ℝ, ∀ lam, reg R lam → ∀ g, Mv s lam g = ∑ q, coeff q lam * ψ q g) :
    ∃ (m : ℕ) (ψ : S → Fin m → Y → ℂ) (coeff : S → Fin m → X → ℂ) (D : Set X),
      (∀ s q, Pr (ψ s q)) ∧ Z ⊆ D ∧ (∀ s q, IsMeromorphicInCoordinatesOn (coeff s q) D) ∧
        ∀ s, ∃ R : ℝ, ∀ lam, reg R lam → ∀ g, Mv s lam g = ∑ q, coeff s q lam * ψ s q g := by
  choose k ψ coeff D hPr hZ hmero hagree using h
  choose D' hDD' hD'o hD'm using fun s => exists_openDense_domain (hmero s)
  set m := Finset.univ.sup k with hm
  have hkm : ∀ s, k s ≤ m := fun s => Finset.le_sup (Finset.mem_univ s)
  have hex : ∀ q : Fin m, ∃ s, (q : ℕ) < k s := fun q => by
    obtain ⟨s, -, hs⟩ := Finset.lt_sup_iff.1 q.2
    exact ⟨s, hs⟩
  choose s₀ hs₀ using hex
  have hDMo : IsOpenDenseInCoordinates (⋂ s, D' s) :=
    isOpenDenseInCoordinates_iInter_of_finite hD'o
  have hmero' : ∀ s (q : Fin (k s)), IsMeromorphicInCoordinatesOn (coeff s q) (⋂ s, D' s) :=
    fun s q => (hD'm s q).congr_mono hDMo (Set.iInter_subset _ s) fun _ _ => rfl
  refine ⟨m, fun s q => if h : (q : ℕ) < k s then ψ s ⟨q, h⟩ else ψ (s₀ q) ⟨q, hs₀ q⟩,
    fun s q lam => if h : (q : ℕ) < k s then coeff s ⟨q, h⟩ lam else 0, ⋂ s, D' s,
    fun s q => ?_, fun z hz => Set.mem_iInter.2 fun s => hDD' s (hZ s hz), fun s q => ?_,
    fun s => ?_⟩
  · by_cases h : (q : ℕ) < k s
    · simp only [h, ↓reduceDIte]
      exact hPr s _
    · simp only [h, ↓reduceDIte]
      exact hPr _ _
  · by_cases h : (q : ℕ) < k s
    · simp only [h, ↓reduceDIte]
      exact hmero' s _
    · simp only [h, ↓reduceDIte]
      exact isMeromorphicInCoordinatesOn_const_zero (hmero' _ ⟨q, hs₀ q⟩)
  · obtain ⟨R, hR⟩ := hagree s
    refine ⟨R, fun lam hlam g => ?_⟩
    rw [hR lam hlam g, ← sum_fin_pad (hkm s)]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : (q : ℕ) < k s
    · simp only [h, ↓reduceDIte]
    · simp only [h, ↓reduceDIte, zero_mul]

/-- The inner product of a finite expansion `φ = ∑ j', c j' • B j'` with the image under a
linear map `op` of a finite expansion `∑ j, c' j • A' j`, when `op (A' j) = ∑ q, a j q • Ψ j q`. -/
theorem inner_sum_smul_map_sum_smul {H H' : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [AddCommGroup H'] [Module ℂ H'] {k k' m : ℕ}
    (op : H' →ₗ[ℂ] H) (A' : Fin k' → H') (B : Fin k → H) (Ψ : Fin k' → Fin m → H)
    (a : Fin k' → Fin m → ℂ) (c' : Fin k' → ℂ) (c : Fin k → ℂ)
    (hop : ∀ j, op (A' j) = ∑ q, a j q • Ψ j q) {φ φ'' : H}
    (hφ : φ = ∑ j', c j' • B j') (hφ'' : φ'' = op (∑ j, c' j • A' j)) :
    ⟪φ, φ''⟫_ℂ = ∑ j, ∑ q, ∑ j', c' j * a j q * (starRingEnd ℂ) (c j') * ⟪B j', Ψ j q⟫_ℂ := by
  subst hφ hφ''
  simp only [map_sum, map_smul, hop, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Finset.mul_sum, mul_assoc]

/-- Change of variables along a measure-preserving map for an integrable function. -/
theorem integral_comp_of_measurePreserving {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {ma : Measure α} {mb : Measure β} {τ : α → β}
    (h : MeasurePreserving τ ma mb) {g : β → ℂ} (hg : Integrable g mb) :
    Integrable (fun x => g (τ x)) ma ∧ ∫ x, g (τ x) ∂ma = ∫ y, g y ∂mb := by
  refine ⟨h.integrable_comp_of_integrable hg, ?_⟩
  have hm : AEStronglyMeasurable g (Measure.map τ ma) := by
    rw [h.map_eq]
    exact hg.aestronglyMeasurable
  rw [← integral_map h.measurable.aemeasurable hm, h.map_eq]

/-- The inner product of two weighted sums `W = ∑ i, n(i)⁻¹ Θ i`, `W' = ∑ i, n(i)⁻¹ Θ' i` of
square integrable functions, when `∫ Θ' i' · conj(Θ i) = C(i', i) J(i)` and
`∑ i', C(i', i) / n(i') = 1` for every `i`: `∫ conj(W) W' = ∑ i, n(i)⁻¹ J(i)`. -/
theorem integral_conj_mul_eq_of_pairs {X : Type*} [MeasurableSpace X] {mX : Measure X}
    {κ : Type*} [Fintype κ] {Θ Θ' : κ → X → ℂ} (hΘ : ∀ i, MemLp (Θ i) 2 mX)
    (hΘ' : ∀ i, MemLp (Θ' i) 2 mX) (nP : κ → ℕ) (C : κ → κ → ℕ) (J : κ → ℂ)
    (hC : ∀ i' i, ∫ y, Θ' i' y * (starRingEnd ℂ) (Θ i y) ∂mX = (C i' i : ℂ) * J i)
    (hone : ∀ i, ∑ i', (C i' i : ℂ) / (nP i' : ℂ) = 1) {W W' : X → ℂ}
    (hW : W = fun y => ∑ i, ((nP i : ℂ))⁻¹ * Θ i y)
    (hW' : W' = fun y => ∑ i, ((nP i : ℂ))⁻¹ * Θ' i y) :
    ∫ y, (starRingEnd ℂ) (W y) * W' y ∂mX = ∑ i, ((nP i : ℂ))⁻¹ * J i := by
  subst hW hW'
  have hint : ∀ i i', Integrable (fun y => (starRingEnd ℂ) ((nP i : ℂ))⁻¹ * ((nP i' : ℂ))⁻¹ *
      (Θ' i' y * (starRingEnd ℂ) (Θ i y))) mX := fun i i' =>
    ((hΘ' i').integrable_mul (hΘ i).star).const_mul _
  have hpt : ∀ y, (starRingEnd ℂ) (∑ i, ((nP i : ℂ))⁻¹ * Θ i y) *
      ∑ i', ((nP i' : ℂ))⁻¹ * Θ' i' y = ∑ i, ∑ i', (starRingEnd ℂ) ((nP i : ℂ))⁻¹ *
        ((nP i' : ℂ))⁻¹ * (Θ' i' y * (starRingEnd ℂ) (Θ i y)) := by
    intro y
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [map_mul]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun i' _ => hint i i']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun i' _ => hint i i']
  simp only [integral_const_mul, hC]
  calc ∑ i', (starRingEnd ℂ) ((nP i : ℂ))⁻¹ * ((nP i' : ℂ))⁻¹ * ((C i' i : ℂ) * J i)
      = ((nP i : ℂ))⁻¹ * J i * ∑ i', (C i' i : ℂ) / (nP i' : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [map_inv₀, Complex.conj_natCast]
        ring
    _ = ((nP i : ℂ))⁻¹ * J i := by rw [hone i, mul_one]

/-- A finite sum of functions each a.e. equal to `g ∘ τ t` for measure-preserving maps `τ t`
integrates to `|κ| ∫ g`. -/
theorem integral_sum_eq_card_mul {α β κ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype κ] {ma : Measure α} {mb : Measure β} {τ : κ → α → β}
    (hτ : ∀ t, MeasurePreserving (τ t) ma mb) {g : β → ℂ} (hg : Integrable g mb)
    {L : κ → α → ℂ} (hL : ∀ t, ∀ᵐ x ∂ma, L t x = g (τ t x)) :
    ∫ x, ∑ t, L t x ∂ma = (Fintype.card κ : ℂ) * ∫ y, g y ∂mb := by
  have hcv := fun t => integral_comp_of_measurePreserving (hτ t) hg
  calc ∫ x, ∑ t, L t x ∂ma = ∫ x, ∑ t, g (τ t x) ∂ma :=
        integral_congr_ae ((ae_all_iff.2 hL).mono fun x hx => Finset.sum_congr rfl fun t _ => hx t)
    _ = ∑ t, ∫ x, g (τ t x) ∂ma := integral_finsetSum _ fun t _ => (hcv t).1
    _ = ∑ _t : κ, ∫ y, g y ∂mb := Finset.sum_congr rfl fun t _ => (hcv t).2
    _ = (Fintype.card κ : ℂ) * ∫ y, g y ∂mb := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The inner product of a finite `ℓ²`-sum of spaces `L²(c(i)⁻¹ ν_i; H_i)`. -/
theorem piLp_L2_inner_eq {κ : Type*} [Fintype κ] {α : κ → Type*} [∀ i, MeasurableSpace (α i)]
    {H : κ → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    (ν : ∀ i, Measure (α i)) (c : κ → ℕ)
    (f g : PiLp 2 (fun i => Lp (H i) 2 (((c i : ENNReal))⁻¹ • ν i))) :
    ⟪f, g⟫_ℂ = ∑ i, ((c i : ℂ))⁻¹ * ∫ y, ⟪f i y, g i y⟫_ℂ ∂(ν i) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [L2.inner_def, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- A linear map preserving Lebesgue measure preserves the normalized measures `spectralMeasure`
(its source and target dimensions agree). -/
theorem measurePreserving_spectralMeasure_of_linearMap {n n' : ℕ}
    (L : (Fin n' → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (hL : MeasurePreserving L volume volume) :
    MeasurePreserving L (spectralMeasure n') (spectralMeasure n) := by
  have heq : n' = n := Langlands.Analysis.eq_of_measurePreserving_linearMap L hL
  subst heq
  unfold spectralMeasure
  exact hL.smul_measure _

end Uniform

section Pair

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {I : Type} [Fintype I] {P M U : I → GroupScheme (Spec (CommRingCat.of F))}
  {A : I → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ i, IsAffine (P i).X.left] [∀ i, IsAffine (M i).X.left]
  [∀ i, LocallyOfFiniteType (M i).X.hom] [∀ i, IsAffine (U i).X.left]
  {p : ∀ i, P i ⟶ G} [∀ i, IsClosedImmersion (p i).hom.hom.left] {iU : ∀ i, U i ⟶ P i}
  {l : ∀ i, M i ⟶ P i} [∀ i, IsClosedImmersion (iU i ≫ p i).hom.hom.left]
  {a : ∀ i, (A i).toGrp ⟶ M i} {r : ∀ i, ParabolicRootPresentation (p i) (l i) (a i)}
  [∀ i, Mono (r i).data.i.hom.hom.left] [∀ i, Fintype (relativeWeylGroup (r i).data.i)]
  [∀ i, Mono (CommGroupScheme.groupHom (r i).data.f).hom.hom.left]
  {hA : ∀ i, IsSplitTorus (A i).toGrp} {hT : ∀ i, IsSplitTorus (r i).data.T.toGrp}
  {π : ∀ i, P i ⟶ M i} [∀ i, LocallyOfFiniteType (P i).X.hom]
  {K : Subgroup (AdelicGroupPoints F G)} {hK : ∀ i, IsIwasawaCompact (p i) K} {N d : ℕ}
  {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {μM : ∀ i, Measure (AdelicGroupPoints F (M i))} [∀ i, (μM i).IsHaarMeasure]
  {n : I → ℕ} {e : ∀ i, (Fin (n i) → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (P i)}
  {β : ∀ i, (Fin (n i) → ℝ) → ℝ}
  {T : I → I → Type} [∀ i i', Fintype (T i i')]
  {w : ∀ i i', T i i' → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)}
  {cw : ∀ i i', T i i' → (M i' ⟶ M i)}
  {hw : ∀ i i' t, MeasurePreserving
    (fun x => (e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x))) volume volume}
  {nP : I → ℕ}
  {Mop : ∀ i i', T i i' → (Fin (n i) → ℝ) →
    inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) (μM i)
        (e i) (β i) →L[ℂ]
      inducedHilbertSpace K (hK i').isCompact rho hsmooth hcalc (p i') (iU i') (l i')
        (μM i') (e i') (β i')}

omit [Fintype I] [∀ i i', Fintype (T i i')] in
/-- The pointwise identity behind `wavePacket_pair_inner`: given expansions
`M(w_t, λ) v'_{i' j} = ∑ q, coeff (t, j) q λ ψ (t, j) q` in `A^2_{P_i}`, if `Φ'_{i'}(x)` and
`Φ_i(y)` are the classes of the restrictions of `∑ j, c' j x v' j` and `∑ j, c j y v j` and
`Φ'_i(y) = M(w_t, x) Φ'_{i'}(x)`, then the integrand of Lapid's formula at `(t, x)` equals
`⟨Φ_i(y), Φ'_i(y)⟩`. -/
theorem wavePacket_pair_pointwise
    (hβ : ∀ i, Continuous (β i) ∧ HasCompactSupport (β i) ∧ (∀ y, 0 ≤ β i y) ∧
      ∫ y, β i y = 1)
    (hMop : ∀ i i' t, IsImaginaryIntertwiningOperator (hK i) (hK i') rho hsmooth hcalc (iU i)
      (l i) (a i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t) (μM i) (μM i')
      (e i) (e i') (β i) (β i') (Mop i i' t))
    (hL' : ∀ i φ,
      IsSquareIntegrableInducedForm K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) φ →
      MemLp (inducedRestriction K (p i) (l i) φ) 2
        (inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i)))
    (Φ Φ' : symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop)
    {k : I → ℕ} {v : ∀ i, Fin (k i) → AdelicGroupPoints F G → ℂ}
    {c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ}
    {k' : I → ℕ} {v' : ∀ i, Fin (k' i) → AdelicGroupPoints F G → ℂ}
    {c' : ∀ i, Fin (k' i) → (Fin (n i) → ℝ) → ℂ}
    (hΦ : IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k v c Φ.1)
    (hΦ' : IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k' v' c' Φ'.1)
    (i' i : I) {m : ℕ} {ψ : T i' i × Fin (k' i') → Fin m → AdelicGroupPoints F G → ℂ}
    {coeff : T i' i × Fin (k' i') → Fin m → ComplexCharacterParameter F (P i') → ℂ}
    {DM : Set (ComplexCharacterParameter F (P i'))}
    (hψ : ∀ s q,
      IsSquareIntegrableInducedForm K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i)
        (ψ s q))
    (hDM : Set.range (imaginaryParameter F (P i')) ⊆ DM)
    (hmero : ∀ s q, IsMeromorphicInCoordinatesOn (coeff s q) DM)
    (hagree : ∀ s : T i' i × Fin (k' i'), ∃ R : ℝ, ∀ lam,
      (r i').IsRegularParameter (hA i') (hT i') R lam → ∀ g,
        (hK i').intertwiningOperator (hK i) (iU i') (l i') (iU i) (cw i' i s.1) (π i)
          (w i' i s.1) (v' i' s.2) lam g = ∑ q, coeff s q lam * ψ s q g)
    (t : T i' i) (x : Fin (n i') → ℝ) (y : Fin (n i) → ℝ)
    (hx1 : ⇑(Φ'.1 i' x : Lp ℂ 2 (inducedL2Measure K (hK i').isCompact (l i') (μM i') (e i')
        (β i')))
      =ᵐ[inducedL2Measure K (hK i').isCompact (l i') (μM i') (e i') (β i')]
      inducedRestriction K (p i') (l i') (fun g => ∑ j, c' i' j x * v' i' j g))
    (hx2 : ⇑(Φ.1 i y : Lp ℂ 2 (inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i)))
      =ᵐ[inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i)]
      inducedRestriction K (p i) (l i) (fun g => ∑ j, c i j y * v i j g))
    (hx3 : Φ'.1 i y = Mop i' i t x (Φ'.1 i' x)) :
    ∑ j, ∑ q, ∑ j', c' i' j x * coeff (t, j) q (imaginaryParameter F (P i') (e i' x)) *
        (starRingEnd ℂ) (c i j' y) *
        inducedInnerProduct K (hK i).isCompact (p i) (l i) (μM i) (e i) (β i) (ψ (t, j) q)
          (v i j') =
      ⟪Φ.1 i y, Φ'.1 i y⟫_ℂ := by
  have hmv : ∀ j, MemLp (inducedRestriction K (p i) (l i) (v i j)) 2
      (inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i)) :=
    fun j => hL' i _ (hΦ.1 i j)
  have hmv' : ∀ j, MemLp (inducedRestriction K (p i') (l i') (v' i' j)) 2
      (inducedL2Measure K (hK i').isCompact (l i') (μM i') (e i') (β i')) :=
    fun j => hL' i' _ (hΦ'.1 i' j)
  have hmψ : ∀ s q, MemLp (inducedRestriction K (p i) (l i) (ψ s q)) 2
      (inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i)) :=
    fun s q => hL' i _ (hψ s q)
  let h' : Fin (k' i') →
      inducedHilbertSpace K (hK i').isCompact rho hsmooth hcalc (p i') (iU i') (l i') (μM i')
        (e i') (β i') := fun j =>
    ⟨(hmv' j).toLp _, toLp_mem_inducedHilbertSpace K (hK i').isCompact rho hsmooth hcalc
      (p i') (iU i') (l i') (μM i') (e i') (β i') (hΦ'.1 i' j) (hmv' j)⟩
  have hY : ∀ j s q, ⟪(hmv j).toLp _, (hmψ s q).toLp _⟫_ℂ =
      inducedInnerProduct K (hK i).isCompact (p i) (l i) (μM i) (e i) (β i) (ψ s q) (v i j) :=
    fun j s q => inner_eq_inducedInnerProduct K (hK i).isCompact (p i) (l i) (μM i) (e i) (β i)
      (hβ i).1 (hβ i).2.2.1 _ _ _ _ (hmv j).coeFn_toLp (hmψ s q).coeFn_toLp
  have hA1 : Φ'.1 i' x = ∑ j, c' i' j x • h' j := by
    refine Subtype.ext ?_
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact Lp.ext (hx1.trans (sum_smul_toLp_mem_inducedHilbertSpace K (hK i').isCompact rho
      hsmooth hcalc (p i') (iU i') (l i') (μM i') (e i') (β i') (hΦ'.1 i') hmv'
      (fun j => c' i' j x)).2.symm)
  have hA2 : ∀ j, ((Mop i' i t x (h' j) :
      inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) (μM i)
        (e i) (β i)) : Lp ℂ 2 (inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i))) =
      ∑ q, coeff (t, j) q (imaginaryParameter F (P i') (e i' x)) • (hmψ (t, j) q).toLp _ :=
    fun j => Lp.ext ((hMop i' i t (v' i' j) (hΦ'.1 i' j) m (ψ (t, j)) (coeff (t, j)) DM
      (hψ (t, j)) hDM (hmero (t, j)) (hagree (t, j)) (h' j) (hmv' j).coeFn_toLp x).trans
      (sum_smul_toLp_mem_inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i)
        (iU i) (l i) (μM i) (e i) (β i) (hψ (t, j)) (hmψ (t, j))
        (fun q => coeff (t, j) q (imaginaryParameter F (P i') (e i' x)))).2.symm)
  have hA3 : ((Φ.1 i y : inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i)
      (iU i) (l i) (μM i) (e i) (β i)) :
        Lp ℂ 2 (inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i))) =
      ∑ j', c i j' y • (hmv j').toLp _ :=
    Lp.ext (hx2.trans (sum_smul_toLp_mem_inducedHilbertSpace K (hK i).isCompact rho hsmooth
      hcalc (p i) (iU i) (l i) (μM i) (e i) (β i) (hΦ.1 i) hmv (fun j' => c i j' y)).2.symm)
  have hA4 : ((Φ'.1 i y : inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i)
      (iU i) (l i) (μM i) (e i) (β i)) :
        Lp ℂ 2 (inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i))) =
      ((inducedHilbertSpace K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) (μM i)
        (e i) (β i)).subtype ∘ₗ (Mop i' i t x).toLinearMap) (∑ j, c' i' j x • h' j) := by
    rw [hx3, hA1]
    rfl
  have key := inner_sum_smul_map_sum_smul _ h' (fun j' => (hmv j').toLp _)
    (fun j q => (hmψ (t, j) q).toLp _)
    (fun j q => coeff (t, j) q (imaginaryParameter F (P i') (e i' x)))
    (fun j => c' i' j x) (fun j' => c i j' y) hA2 hA3 hA4
  refine Eq.trans ?_ ((Submodule.coe_inner _ _ _).trans key).symm
  simp only [hY]

omit [Fintype I] in
/-- Expansions `M(w_t, λ) v'_{i' j} = ∑ q, coeff (t, j) q λ • ψ (t, j) q` in `A^2_{P_i}`, of one
common length and with one common domain of holomorphy containing `i𝔞_{P_{i'}}^*`, for all
`(t, j) ∈ Ω(P_{i'}, P_i) × Fin (k' i')`. -/
theorem wavePacket_pair_expansions (hEx : IntertwiningSquareIntegrableExpansionStatement)
    (hG : IsConnectedReductive G) (hUR : ∀ i, LeviSubgroup.IsGeometricUnipotentRadical (iU i))
    (hMul : ∀ i, IsIso (subgroupMultiplication (l i) (iU i))) (hπ : ∀ i, l i ≫ π i = 𝟙 (M i))
    (hKmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho)
    (hW : ∀ i i' t, IsWeylConjugation (p i) (l i) (p i') (l i') (w i i' t) (cw i i' t))
    {k' : I → ℕ} {v' : ∀ i, Fin (k' i) → AdelicGroupPoints F G → ℂ} (i' i : I)
    (hv' : ∀ j, IsSquareIntegrableInducedForm K (hK i').isCompact rho hsmooth hcalc (p i')
      (iU i') (l i') (v' i' j)) :
    ∃ (m : ℕ) (ψ : T i' i × Fin (k' i') → Fin m → AdelicGroupPoints F G → ℂ)
      (coeff : T i' i × Fin (k' i') → Fin m → ComplexCharacterParameter F (P i') → ℂ)
      (DM : Set (ComplexCharacterParameter F (P i'))),
      (∀ s q, IsSquareIntegrableInducedForm K (hK i).isCompact rho hsmooth hcalc (p i) (iU i)
        (l i) (ψ s q)) ∧
      Set.range (imaginaryParameter F (P i')) ⊆ DM ∧
      (∀ s q, IsMeromorphicInCoordinatesOn (coeff s q) DM) ∧
      ∀ s : T i' i × Fin (k' i'), ∃ R : ℝ, ∀ lam,
        (r i').IsRegularParameter (hA i') (hT i') R lam → ∀ g,
          (hK i').intertwiningOperator (hK i) (iU i') (l i') (iU i) (cw i' i s.1) (π i)
            (w i' i s.1) (v' i' s.2) lam g = ∑ q, coeff s q lam * ψ s q g :=
  exists_uniform_expansions (S := T i' i × Fin (k' i')) (Set.range (imaginaryParameter F (P i')))
    (IsSquareIntegrableInducedForm K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i))
    (fun s lam g => (hK i').intertwiningOperator (hK i) (iU i') (l i') (iU i) (cw i' i s.1)
      (π i) (w i' i s.1) (v' i' s.2) lam g)
    (fun R lam => (r i').IsRegularParameter (hA i') (hT i') R lam)
    (fun s => hEx F G (P i') (M i') (U i') (P i) (M i) (U i) (A i') (A i) (p i') (iU i')
      (l i') (a i') (r i') (hA i') (hT i') (p i) (iU i) (l i) (a i) (r i) (π i) (w i' i s.1)
      (cw i' i s.1) hG (hUR i') (hUR i) (hMul i) (hπ i) (hW i' i s.1) K (hK i') (hK i) rho
      hsmooth hcalc (v' i' s.2) hKmax hrho (hv' s.2))

set_option maxHeartbeats 6400000 in
omit [Fintype I] in
/-- The inner product of the wave packets `Θ'_{i'}` of `(c' i', E' i')` and `Θ_i` of `(c i, E i)`
for two smooth compactly supported families `Φ`, `Φ'` of `L̂`, given expansions of
`M(w_t, λ) v'_{i' j}` in `A^2_{P_i}` as in `wavePacket_pair_expansions`: by Lapid's formula for
the pair `(P_{i'}, P_i)`, it equals `|Ω(P_{i'}, P_i)| ∫ ⟨Φ_i(λ), Φ'_i(λ)⟩ dλ`. -/
theorem wavePacket_pair_inner_of_expansions (hWP : WavePacketInnerProductStatement)
    (hG : IsConnectedReductive G) (hUR : ∀ i, LeviSubgroup.IsGeometricUnipotentRadical (iU i))
    (hπ : ∀ i, l i ≫ π i = 𝟙 (M i))
    (hKmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho)
    (hμM : ∀ i, IsIwasawaCompatibleMeasure K (hK i).isCompact (p i) (iU i) (l i) (μM i))
    (hβ : ∀ i, Continuous (β i) ∧ HasCompactSupport (β i) ∧ (∀ y, 0 ≤ β i y) ∧
      ∫ y, β i y = 1)
    (hW : ∀ i i' t, IsWeylConjugation (p i) (l i) (p i') (l i') (w i i' t) (cw i i' t))
    (hinj : ∀ i i', Function.Injective (fun t => weylParameter (l i) (cw i i' t) (π i')))
    (hsurj : ∀ i i', ∀ s ∈ weylParameterSet (p i) (l i) (p i') (l i') (π i'),
      ∃ t, weylParameter (l i) (cw i i' t) (π i') = s)
    (hnP : ∀ i, nP i ≠ 0)
    (hMop : ∀ i i' t, IsImaginaryIntertwiningOperator (hK i) (hK i') rho hsmooth hcalc (iU i)
      (l i) (a i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t) (μM i) (μM i')
      (e i) (e i') (β i) (β i') (Mop i i' t))
    (hL' : ∀ i φ,
      IsSquareIntegrableInducedForm K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) φ →
      MemLp (inducedRestriction K (p i) (l i) φ) 2
        (inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i)))
    (Φ Φ' : symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop)
    {k : I → ℕ} {v : ∀ i, Fin (k i) → AdelicGroupPoints F G → ℂ}
    {c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ}
    {E : ∀ i, Fin (k i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ}
    {D : ∀ i, Set (ComplexCharacterParameter F (P i))}
    {k' : I → ℕ} {v' : ∀ i, Fin (k' i) → AdelicGroupPoints F G → ℂ}
    {c' : ∀ i, Fin (k' i) → (Fin (n i) → ℝ) → ℂ}
    {E' : ∀ i, Fin (k' i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ}
    {D' : ∀ i, Set (ComplexCharacterParameter F (P i))}
    (hΦ : IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k v c Φ.1)
    (hE : ∀ i, IsEisensteinContinuation (hK i) (r i) (hA i) (hT i) (v i) (E i) (D i))
    (hΦ' : IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k' v' c' Φ'.1)
    (hE' : ∀ i, IsEisensteinContinuation (hK i) (r i) (hA i) (hT i) (v' i) (E' i) (D' i))
    (i' i : I) {m : ℕ} {ψ : T i' i × Fin (k' i') → Fin m → AdelicGroupPoints F G → ℂ}
    {coeff : T i' i × Fin (k' i') → Fin m → ComplexCharacterParameter F (P i') → ℂ}
    {DM : Set (ComplexCharacterParameter F (P i'))}
    (hψ : ∀ s q,
      IsSquareIntegrableInducedForm K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i)
        (ψ s q))
    (hDM : Set.range (imaginaryParameter F (P i')) ⊆ DM)
    (hmero : ∀ s q, IsMeromorphicInCoordinatesOn (coeff s q) DM)
    (hagree : ∀ s : T i' i × Fin (k' i'), ∃ R : ℝ, ∀ lam,
      (r i').IsRegularParameter (hA i') (hT i') R lam → ∀ g,
        (hK i').intertwiningOperator (hK i) (iU i') (l i') (iU i) (cw i' i s.1) (π i)
          (w i' i s.1) (v' i' s.2) lam g = ∑ q, coeff s q lam * ψ s q g) :
    MemLp (fun y : RationalQuotient F G => ∫ x, ∑ j, c' i' j x *
        E' i' j (imaginaryParameter F (P i') (e i' x)) y.out ∂(spectralMeasure (n i'))) 2
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
          (isDiscrete_rationalSubgroup F G) Measure.haar) ∧
      MemLp (fun y : RationalQuotient F G => ∫ x, ∑ j, c i j x *
        E i j (imaginaryParameter F (P i) (e i x)) y.out ∂(spectralMeasure (n i))) 2
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
          (isDiscrete_rationalSubgroup F G) Measure.haar) ∧
      ∫ y, (∫ x, ∑ j, c' i' j x *
          E' i' j (imaginaryParameter F (P i') (e i' x)) y.out ∂(spectralMeasure (n i'))) *
        (starRingEnd ℂ) (∫ x, ∑ j, c i j x *
          E i j (imaginaryParameter F (P i) (e i x)) y.out ∂(spectralMeasure (n i)))
        ∂(LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
          (isDiscrete_rationalSubgroup F G) Measure.haar) =
        (Fintype.card (T i' i) : ℂ) * ∫ y, ⟪Φ.1 i y, Φ'.1 i y⟫_ℂ ∂(spectralMeasure (n i)) := by
  have hc0 : ((nP i : ENNReal))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
  have hctop : ((nP i : ENNReal))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 (hnP i))
  have hJint : Integrable (fun y => ⟪Φ.1 i y, Φ'.1 i y⟫_ℂ) (spectralMeasure (n i)) :=
    (integrable_smul_measure hc0 hctop).1 (L2.integrable_inner (Φ.1 i) (Φ'.1 i))
  obtain ⟨h1, h2, h3⟩ := hWP F G (P i') (M i') (U i') (P i) (M i) (U i) (A i') (A i) (p i')
    (iU i') (l i') (a i') (r i') (hA i') (hT i') (p i) (iU i) (l i) (a i) (r i) (hA i) (hT i)
    (π i) hG (hUR i') (hUR i) (hπ i) K (hK i') (hK i) rho hsmooth hcalc hKmax hrho (μM i)
    (hμM i) (e i') (e i) (β i) (hβ i).1 (hβ i).2.1 (hβ i).2.2.2 (k' i') (v' i') (c' i')
    (E' i') (D' i') (hΦ'.1 i') (hΦ'.2.1 i') (hE' i').1 (hE' i').2.1 (hE' i').2.2 (k i) (v i)
    (c i) (E i) (D i) (hΦ.1 i) (hΦ.2.1 i) (hE i).1 (hE i).2.1 (hE i).2.2 (T i' i) (w i' i)
    (cw i' i) (hW i' i) (hinj i' i) (hsurj i' i) m (fun t j => ψ (t, j))
    (fun t j => coeff (t, j)) DM (fun t j => hψ (t, j)) hDM (fun t j => hmero (t, j))
    (fun t j => hagree (t, j))
  refine ⟨h1, h2, h3.trans ?_⟩
  -- for each `t`, the coordinate change `x ↦ w_t x`
  have hτ : ∀ t : T i' i, MeasurePreserving
      (fun x => (e i).symm (realWeylParameter (l i') (cw i' i t) (π i) (e i' x)))
      (spectralMeasure (n i')) (spectralMeasure (n i)) := fun t =>
    measurePreserving_spectralMeasure_of_linearMap
      ((e i).symm.toLinearMap ∘ₗ realWeylParameter (l i') (cw i' i t) (π i) ∘ₗ
        (e i').toLinearMap) (hw i' i t)
  refine integral_sum_eq_card_mul hτ hJint fun t => ?_
  have hsym : ∀ᵐ x ∂(spectralMeasure (n i')),
      Φ'.1 i ((e i).symm (realWeylParameter (l i') (cw i' i t) (π i) (e i' x))) =
        Mop i' i t x (Φ'.1 i' x) := Φ'.2 i' i t
  filter_upwards [hΦ'.2.2 i', (hτ t).quasiMeasurePreserving.ae (hΦ.2.2 i), hsym]
    with x hx1 hx2 hx3
  exact wavePacket_pair_pointwise hβ hMop hL' Φ Φ' hΦ hΦ' i' i hψ hDM hmero hagree t x _ hx1
    hx2 hx3

set_option maxHeartbeats 6400000 in
omit [Fintype I] in
/-- The inner product of the wave packets `Θ'_{i'}` of `(c' i', E' i')` and `Θ_i` of `(c i, E i)`
for two smooth compactly supported families `Φ`, `Φ'` of `L̂`: by Lapid's formula for the pair
`(P_{i'}, P_i)`, it equals `|Ω(P_{i'}, P_i)| ∫ ⟨Φ_i(λ), Φ'_i(λ)⟩ dλ`. -/
theorem wavePacket_pair_inner (hWP : WavePacketInnerProductStatement)
    (hEx : IntertwiningSquareIntegrableExpansionStatement)
    (hG : IsConnectedReductive G) (hUR : ∀ i, LeviSubgroup.IsGeometricUnipotentRadical (iU i))
    (hMul : ∀ i, IsIso (subgroupMultiplication (l i) (iU i))) (hπ : ∀ i, l i ≫ π i = 𝟙 (M i))
    (hKmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho)
    (hμM : ∀ i, IsIwasawaCompatibleMeasure K (hK i).isCompact (p i) (iU i) (l i) (μM i))
    (hβ : ∀ i, Continuous (β i) ∧ HasCompactSupport (β i) ∧ (∀ y, 0 ≤ β i y) ∧
      ∫ y, β i y = 1)
    (hW : ∀ i i' t, IsWeylConjugation (p i) (l i) (p i') (l i') (w i i' t) (cw i i' t))
    (hinj : ∀ i i', Function.Injective (fun t => weylParameter (l i) (cw i i' t) (π i')))
    (hsurj : ∀ i i', ∀ s ∈ weylParameterSet (p i) (l i) (p i') (l i') (π i'),
      ∃ t, weylParameter (l i) (cw i i' t) (π i') = s)
    (hnP : ∀ i, nP i ≠ 0)
    (hMop : ∀ i i' t, IsImaginaryIntertwiningOperator (hK i) (hK i') rho hsmooth hcalc (iU i)
      (l i) (a i) (r i) (hA i) (hT i) (iU i') (l i') (π i') (w i i' t) (cw i i' t) (μM i) (μM i')
      (e i) (e i') (β i) (β i') (Mop i i' t))
    (hL' : ∀ i φ,
      IsSquareIntegrableInducedForm K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) φ →
      MemLp (inducedRestriction K (p i) (l i) φ) 2
        (inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i)))
    (Φ Φ' : symmetricFamilySpace hK rho hsmooth hcalc iU l μM n e β nP T cw π hw Mop)
    {k : I → ℕ} {v : ∀ i, Fin (k i) → AdelicGroupPoints F G → ℂ}
    {c : ∀ i, Fin (k i) → (Fin (n i) → ℝ) → ℂ}
    {E : ∀ i, Fin (k i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ}
    {D : ∀ i, Set (ComplexCharacterParameter F (P i))}
    {k' : I → ℕ} {v' : ∀ i, Fin (k' i) → AdelicGroupPoints F G → ℂ}
    {c' : ∀ i, Fin (k' i) → (Fin (n i) → ℝ) → ℂ}
    {E' : ∀ i, Fin (k' i) → ComplexCharacterParameter F (P i) → AdelicGroupPoints F G → ℂ}
    {D' : ∀ i, Set (ComplexCharacterParameter F (P i))}
    (hΦ : IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k v c Φ.1)
    (hE : ∀ i, IsEisensteinContinuation (hK i) (r i) (hA i) (hT i) (v i) (E i) (D i))
    (hΦ' : IsSmoothCompactFamily hK rho hsmooth hcalc iU l μM n e β nP k' v' c' Φ'.1)
    (hE' : ∀ i, IsEisensteinContinuation (hK i) (r i) (hA i) (hT i) (v' i) (E' i) (D' i))
    (i' i : I) :
    MemLp (fun y : RationalQuotient F G => ∫ x, ∑ j, c' i' j x *
        E' i' j (imaginaryParameter F (P i') (e i' x)) y.out ∂(spectralMeasure (n i'))) 2
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
          (isDiscrete_rationalSubgroup F G) Measure.haar) ∧
      MemLp (fun y : RationalQuotient F G => ∫ x, ∑ j, c i j x *
        E i j (imaginaryParameter F (P i) (e i x)) y.out ∂(spectralMeasure (n i))) 2
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
          (isDiscrete_rationalSubgroup F G) Measure.haar) ∧
      ∫ y, (∫ x, ∑ j, c' i' j x *
          E' i' j (imaginaryParameter F (P i') (e i' x)) y.out ∂(spectralMeasure (n i'))) *
        (starRingEnd ℂ) (∫ x, ∑ j, c i j x *
          E i j (imaginaryParameter F (P i) (e i x)) y.out ∂(spectralMeasure (n i)))
        ∂(LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G)
          (isDiscrete_rationalSubgroup F G) Measure.haar) =
        (Fintype.card (T i' i) : ℂ) * ∫ y, ⟪Φ.1 i y, Φ'.1 i y⟫_ℂ ∂(spectralMeasure (n i)) := by
  obtain ⟨m, ψ, coeff, DM, hψ, hDM, hmero, hagree⟩ :=
    wavePacket_pair_expansions (r := r) (hA := hA) (hT := hT) hEx hG hUR hMul hπ hKmax hrho hW
      i' i (hΦ'.1 i')
  exact wavePacket_pair_inner_of_expansions hWP hG hUR hπ hKmax hrho hμM hβ hW hinj hsurj hnP
    hMop hL' Φ Φ' hΦ hE hΦ' hE' i' i hψ hDM hmero hagree

end Pair

/-- Lapid's inner product formula for wave packets, finite expansions of the intertwining
operators on `A^2_P` with coefficients holomorphic near the imaginary axis, and the square
integrability of restrictions of elements of `A^2_P` imply the Gram identity for wave packets of
smooth compactly supported families of `L̂`. -/
def SymmetricFamilyGramBridgeStatement : Prop :=
  WavePacketInnerProductStatement → IntertwiningSquareIntegrableExpansionStatement →
    InducedRestrictionMemLpStatement → SymmetricFamilyGramStatement

/-- Proof of `SymmetricFamilyGramBridgeStatement`. -/
theorem symmetricFamilyGramBridge : SymmetricFamilyGramBridgeStatement := by
  intro hWP hEx hL F _ _ G _ _ _ I _ P M U A _ _ _ _ p _ iU l _ a r _ _ _ hA hT π hG hUR hMul hπ
    K hK N d rho hsmooth hcalc hKmax hrho μM _ hμM n e β hβ T _ w cw hW hinj hsurj hw nP μG Mop
    hMop Φ Φ' k v c E D k' v' c' E' D' hΦ hE hΦ' hE'
  have : ∀ i, LocallyOfFiniteType (P i).X.hom := fun i =>
    IsClosedSubgroup.locallyOfFiniteType (j := p i)
      (inferInstance : IsClosedImmersion (p i).hom.hom.left)
  -- square integrability of restrictions
  have hL' : ∀ i φ,
      IsSquareIntegrableInducedForm K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) φ →
      MemLp (inducedRestriction K (p i) (l i) φ) 2
        (inducedL2Measure K (hK i).isCompact (l i) (μM i) (e i) (β i)) :=
    fun i φ hφ => hL F G (P i) (M i) (U i) (A i) (p i) (iU i) (l i) (a i) (r i) (hA i) (hT i)
      (π i) hG (hUR i) (hMul i) (hπ i) K (hK i) rho hsmooth hcalc hKmax hrho (μM i) (hμM i) (e i)
      (β i) (hβ i).1 (hβ i).2.1 (hβ i).2.2.1 φ hφ
  have hnP : ∀ i, nP i ≠ 0 := fun i => by
    have := nonempty_self T cw hsurj i
    exact (Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨i, Finset.mem_univ _, Fintype.card_pos⟩).ne'
  -- the pairs `(P_{i'}, P_i)`
  have hpair := fun i' i => wavePacket_pair_inner hWP hEx hG hUR hMul hπ hKmax hrho hμM hβ hW
    hinj hsurj hnP hMop hL' Φ Φ' hΦ hE hΦ' hE' i' i
  -- assembly
  have hMemΘ : ∀ i, MemLp (fun y : RationalQuotient F G => ∫ x, ∑ j, c i j x *
      E i j (imaginaryParameter F (P i) (e i x)) y.out ∂(spectralMeasure (n i))) 2 μG :=
    fun i => (hpair i i).2.1
  have hMemΘ' : ∀ i, MemLp (fun y : RationalQuotient F G => ∫ x, ∑ j, c' i j x *
      E' i j (imaginaryParameter F (P i) (e i x)) y.out ∂(spectralMeasure (n i))) 2 μG :=
    fun i => (hpair i i).1
  refine ⟨?_, ?_⟩
  · have : wavePacketSum e nP c E = fun y => ∑ i, ((nP i : ℂ))⁻¹ * ∫ x, ∑ j, c i j x *
        E i j (imaginaryParameter F (P i) (e i x)) y.out ∂(spectralMeasure (n i)) := rfl
    rw [this]
    exact memLp_finsetSum _ fun i _ => (hMemΘ i).const_mul _
  · exact (integral_conj_mul_eq_of_pairs hMemΘ hMemΘ' nP (fun i' i => Fintype.card (T i' i))
      (fun i => ∫ y, ⟪Φ.1 i y, Φ'.1 i y⟫_ℂ ∂(spectralMeasure (n i))) (fun i' i => (hpair i' i).2.2)
      (fun i => sum_card_div_card_eq_one hπ T w cw hW hinj hsurj i)
      (W := wavePacketSum e nP c E) (W' := wavePacketSum e nP c' E') rfl rfl).trans
      (piLp_L2_inner_eq (fun i => spectralMeasure (n i)) nP Φ.1 Φ'.1).symm

end Langlands.Global
