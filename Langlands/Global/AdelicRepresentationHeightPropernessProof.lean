import Langlands.Global.AdelicRepresentationHeightPropernessStatement
import Langlands.Global.IntegralFiniteAdeles
import Langlands.GroupScheme.AffinePointClosedImmersion
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Continuity and properness of full adelic representation heights: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Topology
open scoped CategoryTheory.MonObj RestrictedProduct NNReal

namespace Langlands.Global.AdelicMatrixHeight

open MatrixInverseHeight

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-! ### Continuity -/

theorem continuous_finiteLocal (v : FinitePlace F) :
    Continuous (fun g : AdelicGL F n => finiteLocal F n g v) := by
  have hp := continuous_finiteProjection F v
  exact (continuous_norm.comp (continuous_pi fun i => continuous_pi fun j =>
      hp.comp (Units.continuous_val.matrix_elem i j))).max
    (continuous_norm.comp (continuous_pi fun i => continuous_pi fun j =>
      hp.comp (Units.continuous_coe_inv.matrix_elem i j)))

theorem continuous_infiniteLocal (v : InfinitePlace F) :
    Continuous (fun g : AdelicGL F n => infiniteLocal F n g v) := by
  have hp := continuous_infiniteProjection F v
  exact (continuous_norm.comp (continuous_pi fun i => continuous_pi fun j =>
      hp.comp (Units.continuous_val.matrix_elem i j))).max
    (continuous_norm.comp (continuous_pi fun i => continuous_pi fun j =>
      hp.comp (Units.continuous_coe_inv.matrix_elem i j)))

theorem continuous_entry (i j : Fin n) :
    Continuous (fun g : AdelicGL F n => (g : Matrix (Fin n) (Fin n) (Adeles F)) i j) :=
  Units.continuous_val.matrix_elem i j

theorem continuous_inv_entry (i j : Fin n) :
    Continuous (fun g : AdelicGL F n =>
      ((g⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) i j) :=
  Units.continuous_coe_inv.matrix_elem i j

/-- Matrices whose entries and inverse entries are integral at every finite place outside `S`. -/
def integralAway (S : Set (FinitePlace F)) : Set (AdelicGL F n) :=
  {g | ∀ i j, ∀ v ∉ S, (g i j).2 v ∈ v.adicCompletionIntegers F ∧
    (g⁻¹ i j).2 v ∈ v.adicCompletionIntegers F}

/-- The integrality condition outside `S` is open in the restricted-product topology. -/
theorem isOpen_integralAway (S : Set (FinitePlace F)) : IsOpen (integralAway F n S) := by
  let O : Set (FiniteAdeles F) :=
    {a | ∀ v, v ∉ S → a.1 v ∈ v.adicCompletionIntegers F}
  have hO : IsOpen O := RestrictedProduct.isOpen_forall_imp_mem
    (fun v : FinitePlace F => Valued.isOpen_valuationSubring (v.adicCompletion F))
  have h : integralAway F n S = ⋂ i, ⋂ j,
      ((fun g : AdelicGL F n => (g i j).2) ⁻¹' O ∩
        (fun g : AdelicGL F n => (g⁻¹ i j).2) ⁻¹' O) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
    exact forall_congr' fun i => forall_congr' fun j =>
      ⟨fun h => ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩,
        fun h v hv => ⟨h.1 v hv, h.2 v hv⟩⟩
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (hO.preimage (continuous_snd.comp (continuous_entry F n i j))).inter
      (hO.preimage (continuous_snd.comp (continuous_inv_entry F n i j)))

variable {n}

/-- Integral entries and inverse entries give the local factor one. -/
theorem finiteLocal_eq_one (hn : 0 < n) (g : AdelicGL F n) (v : FinitePlace F)
    (hv : ∀ i j, (g i j).2 v ∈ v.adicCompletionIntegers F ∧
      (g⁻¹ i j).2 v ∈ v.adicCompletionIntegers F) :
    finiteLocal F n g v = 1 := by
  apply le_antisymm _ (one_le_finiteLocal F n hn g v)
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    change ‖(g i j).2 v‖ ≤ 1
    simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff] using (hv i j).1
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    change ‖(g⁻¹ i j).2 v‖ ≤ 1
    simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff] using (hv i j).2

/-- The finite product is continuous: near each point it is a fixed finite product. -/
theorem continuous_finiteProduct (hn : 0 < n) :
    Continuous (fun g : AdelicGL F n => ∏ᶠ v : FinitePlace F, finiteLocal F n g v) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have hval : ∀ᶠ v : FinitePlace F in Filter.cofinite,
      ∀ i j : Fin n, (g₀ i j).2 v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => (g₀ i j).2.property
  have hinv : ∀ᶠ v : FinitePlace F in Filter.cofinite,
      ∀ i j : Fin n, (g₀⁻¹ i j).2 v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => (g₀⁻¹ i j).2.property
  have hfin : {v : FinitePlace F | ¬ ∀ i j, (g₀ i j).2 v ∈ v.adicCompletionIntegers F ∧
      (g₀⁻¹ i j).2 v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp ((hval.and hinv).mono fun v h i j => ⟨h.1 i j, h.2 i j⟩)
  set S := hfin.toFinset
  have hmem : g₀ ∈ integralAway F n (S : Set (FinitePlace F)) := by
    intro i j v hv
    simp only [S, Set.Finite.coe_toFinset, Set.mem_ofPred_eq, not_not] at hv
    exact hv i j
  have heq : ∀ g ∈ integralAway F n (S : Set (FinitePlace F)),
      ∏ᶠ v, finiteLocal F n g v = ∏ v ∈ S, finiteLocal F n g v := by
    intro g hg
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hvS
    exact hv (finiteLocal_eq_one F hn g v fun i j => hg i j v hvS)
  have hcont : Continuous (fun g : AdelicGL F n => ∏ v ∈ S, finiteLocal F n g v) :=
    continuous_finsetProd S fun v _ => continuous_finiteLocal F n v
  refine hcont.continuousAt.congr ?_
  filter_upwards [(isOpen_integralAway F n S).mem_nhds hmem] with g hg
  exact (heq g hg).symm

/-- The dimension-scaled full adelic matrix height is continuous at positive rank. -/
theorem continuous_height (hn : 0 < n) : Continuous (height F n) := by
  have hinf : Continuous (fun g : AdelicGL F n =>
      ∏ v : InfinitePlace F, ((n : ℝ) * infiniteLocal F n g v) ^ v.mult) :=
    continuous_finsetProd _ fun v _ =>
      (continuous_const.mul (continuous_infiniteLocal F n v)).pow _
  exact hinf.mul (continuous_finiteProduct F hn)

/-! ### Local bounds -/

theorem mem_adicCompletionIntegers_iff_norm_le_one (v : FinitePlace F)
    (x : FiniteCompletion F v) : x ∈ v.adicCompletionIntegers F ↔ ‖x‖ ≤ 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    Valued.toNormedField.norm_le_one_iff]

/-- A nonintegral element has normalized norm at least the absolute norm of the prime. -/
theorem absNorm_le_norm_of_one_lt (v : FinitePlace F) {x : FiniteCompletion F v}
    (h : 1 < ‖x‖) : (Ideal.absNorm v.asIdeal : ℝ) ≤ ‖x‖ := by
  have key : ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ) ≤ ‖x‖ := by
    rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply
      (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (by aesop)]
    norm_cast
    conv_lhs => rw [← zpow_one (v.asIdeal.absNorm : NNReal)]
    apply zpow_le_zpow_right₀ (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v).le
    simpa [← Int.sub_one_lt_iff, sub_self, ← toAdd_one, Multiplicative.toAdd_lt,
      WithZero.lt_unzero_iff] using Valued.toNormedField.one_lt_norm_iff.1 h
  simpa using key

/-- Only finitely many finite places have absolute norm at most a fixed real bound. -/
theorem finite_absNorm_le (B : ℝ) :
    {v : FinitePlace F | (Ideal.absNorm v.asIdeal : ℝ) ≤ B}.Finite := by
  have h := Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊B⌋₊
  refine (h.preimage HeightOneSpectrum.asIdeal_injective.injOn).subset ?_
  intro v hv
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hv ⊢
  exact Nat.le_floor hv

theorem isCompact_closedBall_finiteCompletion (v : FinitePlace F) (B : ℝ) :
    IsCompact (Metric.closedBall (0 : FiniteCompletion F v) B) := by
  let : NontriviallyNormedField (FiniteCompletion F v) :=
    Valued.toNontriviallyNormedField (FiniteCompletion F v) (WithZero (Multiplicative ℤ))
  have : LocallyCompactSpace (FiniteCompletion F v) :=
    (isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((Valued.isOpen_valuationSubring _).mem_nhds (v.adicCompletionIntegers F).zero_mem)
  have : ProperSpace (FiniteCompletion F v) :=
    ProperSpace.of_locallyCompactSpace (FiniteCompletion F v)
  exact isCompact_closedBall 0 B

omit [NumberField F] in
theorem isCompact_closedBall_infiniteCompletion (w : InfinitePlace F) (B : ℝ) :
    IsCompact (Metric.closedBall (0 : InfiniteCompletion F w) B) := by
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  have h : Metric.closedBall (0 : InfiniteCompletion F w) B =
      InfinitePlace.Completion.extensionEmbedding w ⁻¹' Metric.closedBall 0 B := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_preimage]
    rw [hi.norm_map_of_map_zero (map_zero _)]
  rw [h]
  exact hi.isClosedEmbedding.isCompact_preimage (isCompact_closedBall 0 B)

/-- Finite adeles bounded by `B` and integral at every place of absolute norm above `B`. -/
def finiteBox (B : ℝ) : Set (FiniteAdeles F) :=
  {a | ∀ v : FinitePlace F, ‖a v‖ ≤ B ∧
    (B < Ideal.absNorm v.asIdeal → a v ∈ v.adicCompletionIntegers F)}

/-- The bounded box lies in a compact set of the restricted product. -/
theorem exists_isCompact_superset_finiteBox (B : ℝ) :
    ∃ E : Set (FiniteAdeles F), IsCompact E ∧ finiteBox F B ⊆ E := by
  classical
  let T : Set (FinitePlace F) := {v | B < Ideal.absNorm v.asIdeal}
  have hT : Filter.cofinite ≤ Filter.principal T := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite]
    refine (finite_absNorm_le F B).subset ?_
    intro v hv
    simpa [T] using hv
  let Q : Set ((v : FinitePlace F) → FiniteCompletion F v) :=
    Set.univ.pi fun v => if v ∈ T then (v.adicCompletionIntegers F : Set (FiniteCompletion F v))
      else Metric.closedBall 0 B
  have hQ : IsCompact Q := isCompact_univ_pi fun v => by
    split_ifs
    · exact isCompact_adicCompletionIntegers F v
    · exact isCompact_closedBall_finiteCompletion F v B
  let P : Set (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]_[Filter.principal T]) :=
    (fun f => (f : (v : FinitePlace F) → FiniteCompletion F v)) ⁻¹' Q
  have hP : IsCompact P := by
    refine (RestrictedProduct.isEmbedding_coe_of_principal.isInducing.isCompact_preimage_iff
      ?_).mpr hQ
    rw [RestrictedProduct.range_coe_principal]
    intro f hf v hv
    have := hf v (Set.mem_univ v)
    simpa [hv] using this
  refine ⟨RestrictedProduct.inclusion _ _ hT '' P,
    hP.image (RestrictedProduct.continuous_inclusion hT), ?_⟩
  intro a ha
  refine ⟨⟨a.1, Filter.eventually_principal.mpr fun v hv => (ha v).2 hv⟩, ?_, rfl⟩
  intro v _
  show a.1 v ∈ _
  by_cases hv : v ∈ T
  · simp only [hv, ↓reduceIte]
    exact (ha v).2 hv
  · simp only [hv, ↓reduceIte]
    exact mem_closedBall_zero_iff.mpr (ha v).1

/-- Full adeles bounded by `B` at every infinite place and lying in `finiteBox`. -/
def adeleBox (B : ℝ) : Set (Adeles F) :=
  {a | (∀ w, ‖a.1 w‖ ≤ B) ∧ a.2 ∈ finiteBox F B}

theorem exists_isCompact_superset_adeleBox (B : ℝ) :
    ∃ E : Set (Adeles F), IsCompact E ∧ adeleBox F B ⊆ E := by
  obtain ⟨E, hE, hsub⟩ := exists_isCompact_superset_finiteBox F B
  refine ⟨(Set.univ.pi fun w : InfinitePlace F =>
      Metric.closedBall (0 : InfiniteCompletion F w) B) ×ˢ E,
    (isCompact_univ_pi fun w => isCompact_closedBall_infiniteCompletion F w B).prod hE, ?_⟩
  rintro a ⟨ha1, ha2⟩
  exact ⟨fun w _ => by simpa using ha1 w, hsub ha2⟩

variable (n) in
/-- Matrices whose entries and inverse entries lie in a fixed set of adeles. -/
def entryBox (E : Set (Adeles F)) : Set (AdelicGL F n) :=
  {g | (g : Matrix (Fin n) (Fin n) (Adeles F)) ∈ {M | ∀ i j, M i j ∈ E} ∧
    ((g⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)) ∈ {M | ∀ i j, M i j ∈ E}}

variable (n) in
/-- A compact entry set gives a compact matrix set in the units topology. -/
theorem isCompact_entryBox {E : Set (Adeles F)} (hE : IsCompact E) :
    IsCompact (entryBox F n E) := by
  have : T2Space (InfiniteAdeles F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  have : T2Space (FiniteAdeles F) := inferInstanceAs
    (T2Space (Πʳ v : FinitePlace F, [FiniteCompletion F v, v.adicCompletionIntegers F]))
  have : T2Space (Adeles F) := inferInstanceAs (T2Space (InfiniteAdeles F × FiniteAdeles F))
  have hM : IsCompact {M : Matrix (Fin n) (Fin n) (Adeles F) | ∀ i j, M i j ∈ E} := by
    have h := isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin n => hE
    have heq : {M : Matrix (Fin n) (Fin n) (Adeles F) | ∀ i j, M i j ∈ E} =
        Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => E := by
      ext M
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [heq]
    exact h
  have h : IsCompact ({M : Matrix (Fin n) (Fin n) (Adeles F) | ∀ i j, M i j ∈ E} ×ˢ
      (MulOpposite.unop ⁻¹' {M : Matrix (Fin n) (Fin n) (Adeles F) | ∀ i j, M i j ∈ E})) :=
    hM.prod (MulOpposite.opHomeomorph.isCompact_preimage.mp hM)
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage h

/-- On a positive-rank sublevel set every entry and inverse entry lies in `adeleBox`. -/
theorem sublevel_subset (hn : 0 < n) (B : ℝ) :
    {g : AdelicGL F n | height F n g ≤ B} ⊆ entryBox F n (adeleBox F B) := by
  classical
  intro g hg
  have hg' : height F n g ≤ B := hg
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn
  have hinf1 : ∀ w : InfinitePlace F, 1 ≤ ((n : ℝ) * infiniteLocal F n g w) ^ w.mult :=
    fun w => one_le_pow₀ (one_le_nat_mul_localMaximum (infiniteProjection F w) hn g)
  have hA : 1 ≤ ∏ w : InfinitePlace F, ((n : ℝ) * infiniteLocal F n g w) ^ w.mult :=
    Finset.one_le_prod₀ fun w _ => hinf1 w
  have hFp : 1 ≤ ∏ᶠ v : FinitePlace F, finiteLocal F n g v :=
    one_le_finprod (one_le_finiteLocal F n hn g)
  have hAB : ∏ w : InfinitePlace F, ((n : ℝ) * infiniteLocal F n g w) ^ w.mult ≤ B :=
    (le_mul_of_one_le_right (zero_le_one.trans hA) hFp).trans hg'
  have hFB : ∏ᶠ v : FinitePlace F, finiteLocal F n g v ≤ B :=
    (le_mul_of_one_le_left (zero_le_one.trans hFp) hA).trans hg'
  -- Infinite places.
  have hinfB : ∀ w : InfinitePlace F, infiniteLocal F n g w ≤ B := by
    intro w
    have h1 : ((n : ℝ) * infiniteLocal F n g w) ^ w.mult ≤
        ∏ w : InfinitePlace F, ((n : ℝ) * infiniteLocal F n g w) ^ w.mult := by
      have := Finset.prod_le_prod_of_subset_of_one_le₀
        (f := fun w : InfinitePlace F => ((n : ℝ) * infiniteLocal F n g w) ^ w.mult)
        (Finset.subset_univ {w}) (fun i _ => zero_le_one.trans (hinf1 i))
        (fun i _ _ => hinf1 i)
      simpa using this
    have h2 : (n : ℝ) * infiniteLocal F n g w ≤ ((n : ℝ) * infiniteLocal F n g w) ^ w.mult :=
      le_self_pow₀ (one_le_nat_mul_localMaximum (infiniteProjection F w) hn g)
        InfinitePlace.mult_ne_zero
    have h3 : infiniteLocal F n g w ≤ (n : ℝ) * infiniteLocal F n g w :=
      le_mul_of_one_le_left (localMaximum_nonneg _ _) hn1
    exact h3.trans (h2.trans (h1.trans hAB))
  -- Finite places.
  have hfinB : ∀ v : FinitePlace F, finiteLocal F n g v ≤ B := by
    intro v
    have hfs : (Function.mulSupport (finiteLocal F n g)).Finite :=
      hasFiniteMulSupport_finiteLocal F n hn g
    have hsub : Function.mulSupport (finiteLocal F n g) ⊆
        ((insert v hfs.toFinset : Finset (FinitePlace F)) : Set (FinitePlace F)) := by
      intro w hw
      simp only [Finset.coe_insert, Set.Finite.coe_toFinset]
      exact Set.mem_insert_of_mem _ hw
    have h1 : finiteLocal F n g v ≤ ∏ᶠ w : FinitePlace F, finiteLocal F n g w := by
      rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
      have := Finset.prod_le_prod_of_subset_of_one_le₀
        (f := fun w : FinitePlace F => finiteLocal F n g w)
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self v hfs.toFinset))
        (fun i _ => zero_le_one.trans (one_le_finiteLocal F n hn g i))
        (fun i _ _ => one_le_finiteLocal F n hn g i)
      simpa using this
    exact h1.trans hFB
  have hbox : ∀ x : Adeles F, (∀ w, ‖infiniteProjection F w x‖ ≤ B) →
      (∀ v, ‖finiteProjection F v x‖ ≤ B) → x ∈ adeleBox F B := by
    intro x hx1 hx2
    refine ⟨hx1, fun v => ⟨hx2 v, fun hv => ?_⟩⟩
    rw [mem_adicCompletionIntegers_iff_norm_le_one]
    by_contra hlt
    have := absNorm_le_norm_of_one_lt F v (lt_of_not_ge hlt)
    exact absurd ((this.trans (hx2 v)).trans_lt hv) (lt_irrefl _)
  refine ⟨fun i j => hbox _ (fun w => ?_) (fun v => ?_),
    fun i j => hbox _ (fun w => ?_) (fun v => ?_)⟩
  · exact (entry_le_localMaximum (infiniteProjection F w) g i j).trans (hinfB w)
  · exact (entry_le_localMaximum (finiteProjection F v) g i j).trans (hfinB v)
  · have h := entry_le_localMaximum (infiniteProjection F w) g⁻¹ i j
    rw [localMaximum_inv] at h
    exact h.trans (hinfB w)
  · have h := entry_le_localMaximum (finiteProjection F v) g⁻¹ i j
    rw [localMaximum_inv] at h
    exact h.trans (hfinB v)

/-- Positive-rank sublevel sets of the full adelic matrix height are compact. -/
theorem isCompact_sublevel (hn : 0 < n) (B : ℝ) :
    IsCompact {g : AdelicGL F n | height F n g ≤ B} := by
  obtain ⟨E, hE, hsub⟩ := exists_isCompact_superset_adeleBox F B
  refine (isCompact_entryBox F n hE).of_isClosed_subset
    (isClosed_le (continuous_height F hn) continuous_const) ?_
  intro g hg
  obtain ⟨h1, h2⟩ := sublevel_subset F hn B hg
  exact ⟨fun i j => hsub (h1 i j), fun i j => hsub (h2 i j)⟩

/-- The positive-rank full adelic matrix height is a proper map. -/
theorem isProperMap_height (hn : 0 < n) : IsProperMap (height F n) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_height F hn, fun K hK => ?_⟩
  obtain ⟨B, hB⟩ := hK.bddAbove
  exact (isCompact_sublevel F hn B).of_isClosed_subset
    (hK.isClosed.preimage (continuous_height F hn)) fun g hg => hB hg

end Langlands.Global.AdelicMatrixHeight

namespace Langlands.Global.RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin N))

omit [IsAffine G.X.left] in
/-- The full adelic representation height is continuous at positive rank. -/
theorem continuous_adelicHeight (hN : 0 < N) : Continuous (adelicHeight F G rho) :=
  (AdelicMatrixHeight.continuous_height F hN).comp (adelicMatrix F G rho).continuous

/-- A closed immersion gives a closed embedding of actual adelic points into `GL_N(𝔸_F)`. -/
theorem isClosedEmbedding_adelicMatrix (hrho : GroupScheme.IsClosedSubgroup rho) :
    IsClosedEmbedding (adelicMatrix F G rho) := by
  let : IsClosedImmersion rho.hom.hom.left := hrho
  let : T2Space (InfiniteAdeles F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  let : T2Space (FiniteAdeles F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  let : T2Space (Adeles F) :=
    inferInstanceAs (T2Space (InfiniteAdeles F × FiniteAdeles F))
  let : IsAffine (GroupScheme.GeneralLinear.groupScheme
      (Fin N) (CommRingCat.of F)).X.left :=
    GroupScheme.GeneralLinear.isAffine_groupScheme (Fin N) (CommRingCat.of F)
  exact (GeneralLinearGroupPoints.adelicHomeomorph F N).isClosedEmbedding.comp
    (G.isClosedEmbedding_affinePointsTarget _ (CommAlgCat.of F (Adeles F)) rho)

/-- For a closed immersion the full adelic representation height is a proper map. -/
theorem isProperMap_adelicHeight (hN : 0 < N) (hrho : GroupScheme.IsClosedSubgroup rho) :
    IsProperMap (adelicHeight F G rho) :=
  (AdelicMatrixHeight.isProperMap_height F hN).comp
    (isClosedEmbedding_adelicMatrix F G rho hrho).isProperMap

theorem adelicRepresentationHeightProperness :
    AdelicRepresentationHeightPropernessStatement.{u} :=
  fun F _ _ G _ _ rho hN =>
    ⟨continuous_adelicHeight F G rho hN, isProperMap_adelicHeight F G rho hN⟩

end Langlands.Global.RepresentationGrowth
