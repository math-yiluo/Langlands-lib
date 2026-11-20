import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.LaurentInductionStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRelativeRationalRefinement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectrumIdealCriterionProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain

/-! # Proof of induction along iterated real-radius binary Laurent splits -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

namespace LaurentInduction

open CategoryTheory

section Spectrum

variable {A : Type*} [NormedCommRing A]

theorem spec_one (x : BanachSpectrum A) : x 1 = 1 := map_one x.toMulRingSeminorm

theorem spec_mul (x : BanachSpectrum A) (a b : A) : x (a * b) = x a * x b :=
  map_mul x.toMulRingSeminorm a b

theorem spec_nonneg (x : BanachSpectrum A) (a : A) : 0 ≤ x a :=
  apply_nonneg x.toMulRingSeminorm a

theorem spec_prod {ι : Type*} (x : BanachSpectrum A) (s : Finset ι) (f : ι → A) :
    x (∏ i ∈ s, f i) = ∏ i ∈ s, x (f i) :=
  map_prod x.toMulRingSeminorm f s

end Spectrum

section Real

/-- In a finite set on which a transitive relation is total, some element
dominates all others. -/
theorem exists_max_of_total {α : Type*} [DecidableEq α] (r : α → α → Prop)
    (htrans : ∀ a b c, r a b → r b c → r a c) (s : Finset α)
    (htot : ∀ a ∈ s, ∀ b ∈ s, r a b ∨ r b a) (hs : s.Nonempty) :
    ∃ m ∈ s, ∀ a ∈ s, r a m := by
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | insert a s ha ih =>
    have hrefl : r a a :=
      (htot a (Finset.mem_insert_self _ _) a (Finset.mem_insert_self _ _)).elim id id
    rcases s.eq_empty_or_nonempty with hse | hsne
    · subst hse
      refine ⟨a, Finset.mem_insert_self _ _, fun b hb => ?_⟩
      rw [Finset.mem_insert] at hb
      rcases hb with rfl | hb
      · exact hrefl
      · exact absurd hb (Finset.notMem_empty b)
    · obtain ⟨m, hm, hmax⟩ := ih (fun b hb c hc =>
        htot b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc)) hsne
      rcases htot a (Finset.mem_insert_self _ _) m (Finset.mem_insert_of_mem hm) with ham | hma
      · refine ⟨m, Finset.mem_insert_of_mem hm, fun b hb => ?_⟩
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact ham
        · exact hmax b hb
      · refine ⟨a, Finset.mem_insert_self _ _, fun b hb => ?_⟩
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact hrefl
        · exact htrans _ _ _ (hmax b hb) hma

variable {n : ℕ} {m : Fin n → ℕ}

/-- A point of a chart `k0` gives a positive product with zero `k0`-coordinate. -/
theorem exists_prod_pos (φ : (k : Fin n) → Fin (m k + 1) → ℝ)
    (hpos : ∀ k, ∃ j, 0 < φ k j) (k0 : Fin n) (hk0 : ∀ j, φ k0 j ≤ φ k0 0) :
    ∃ μ : (k : Fin n) → Fin (m k + 1), μ k0 = 0 ∧ 0 < ∏ k, φ k (μ k) := by
  classical
  choose J hJ using hpos
  refine ⟨Function.update J k0 0, by simp, Finset.prod_pos fun k _ => ?_⟩
  by_cases hk : k = k0
  · subst hk
    rw [Function.update_self]
    exact (hJ k).trans_le (hk0 _)
  · rw [Function.update_of_ne hk]
    exact hJ k

/-- If a product with zero `k`-coordinate is maximal among the products with
zero `k0`-coordinate, where `k0` is a chart containing the point, then the
zeroth entry of the `k`-th family is its largest. -/
theorem le_zero_of_isMax (φ : (k : Fin n) → Fin (m k + 1) → ℝ)
    (h0 : ∀ k j, 0 ≤ φ k j) (hpos : ∀ k, ∃ j, 0 < φ k j) (k0 : Fin n)
    (hk0 : ∀ j, φ k0 j ≤ φ k0 0) (ν : (k : Fin n) → Fin (m k + 1)) (k : Fin n)
    (hνk : ν k = 0)
    (hmax : ∀ μ : (k : Fin n) → Fin (m k + 1), μ k0 = 0 →
      ∏ k', φ k' (μ k') ≤ ∏ k', φ k' (ν k')) (j : Fin (m k + 1)) :
    φ k j ≤ φ k 0 := by
  classical
  by_contra hlt
  push Not at hlt
  have hM : ∀ k', ∃ j', ∀ j'', φ k' j'' ≤ φ k' j' := fun k' => by
    obtain ⟨j', -, hj'⟩ := Finset.exists_max_image Finset.univ (φ k') Finset.univ_nonempty
    exact ⟨j', fun j'' => hj' j'' (Finset.mem_univ _)⟩
  choose J hJ using hM
  have hMpos : ∀ k', 0 < φ k' (J k') := fun k' => by
    obtain ⟨j', hj'⟩ := hpos k'
    exact hj'.trans_le (hJ k' j')
  have h1 : ∏ k', φ k' (J k') ≤ ∏ k', φ k' (Function.update J k0 0 k') := by
    refine Finset.prod_le_prod₀ (fun k' _ => (hMpos k').le) (fun k' _ => ?_)
    by_cases hk : k' = k0
    · subst hk
      rw [Function.update_self]
      exact hk0 _
    · rw [Function.update_of_ne hk]
  have h2 : ∏ k', φ k' (ν k') < ∏ k', φ k' (J k') := by
    by_cases hall : ∀ k', 0 < φ k' (ν k')
    · refine Finset.prod_lt_prod₀ (fun k' _ => hall k') (fun k' _ => hJ k' _)
        ⟨k, Finset.mem_univ _, ?_⟩
      rw [hνk]
      exact hlt.trans_le (hJ k j)
    · push Not at hall
      obtain ⟨k', hk'⟩ := hall
      have hz : φ k' (ν k') = 0 := le_antisymm hk' (h0 _ _)
      rw [Finset.prod_eq_zero (Finset.mem_univ k') hz]
      exact Finset.prod_pos fun k' _ => hMpos k'
  have h3 := hmax (Function.update J k0 0) (by simp)
  linarith

theorem le_mul_iff_div_le {p q a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    p ≤ a / b * q ↔ p / a ≤ q / b := by
  rw [div_le_div_iff₀ ha hb, div_mul_eq_mul_div, le_div_iff₀ hb, mul_comm q a]

theorem mul_le_iff_div_le {p q a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a / b * q ≤ p ↔ q / b ≤ p / a := by
  rw [div_le_div_iff₀ hb ha, div_mul_eq_mul_div, div_le_iff₀ hb, mul_comm q a]

end Real

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}

/-- The lower side `{|f| ≤ ρ |g|}` of a test. -/
def lowerSide (f g : R) (ρ : ℝ) : Set (BanachSpectrum R) := {x | x f ≤ ρ * x g}

/-- The upper side `{ρ |g| ≤ |f|}` of a test. -/
def upperSide (f g : R) (ρ : ℝ) : Set (BanachSpectrum R) := {x | ρ * x g ≤ x f}

/-- Sets refined by a finite tree of tests `(f, g, ρ)`, each test splitting along
`{|f| ≤ ρ |g|}` and `{ρ |g| ≤ |f|}` with `g` nonvanishing on the set, until every
leaf satisfies `Q`. -/
inductive Fine (Q : Set (BanachSpectrum R) → Prop) : Set (BanachSpectrum R) → Prop
  | leaf {S : Set (BanachSpectrum R)} : Q S → Fine Q S
  | split {S : Set (BanachSpectrum R)} (f g : R) (ρ : ℝ) : 0 < ρ →
      (∀ x ∈ S, x g ≠ 0) → Fine Q (S ∩ lowerSide f g ρ) →
      Fine Q (S ∩ upperSide f g ρ) → Fine Q S

/-- A property satisfying the base and step hypotheses of the statement holds on
every domain whose locus lies in a set refined by a test tree. -/
theorem prop_of_fine {Q : Set (BanachSpectrum R) → Prop} (P : Domain K R → Prop)
    (hbase : ∀ S, Q S → ∀ U : Domain K R, U.locus ⊆ S → P U)
    (hstep : ∀ U : Domain K R, (∃ (a : U.algebra) (ρ : ℝ), 0 < ρ ∧
        ∀ U₁ U₂ : Domain K R,
          U₁.locus = U.spectrumMap '' {y | y a ≤ ρ} →
          U₂.locus = U.spectrumMap '' {y | ρ ≤ y a} → P U₁ ∧ P U₂) → P U)
    {S : Set (BanachSpectrum R)} (hS : Fine Q S) :
    ∀ U : Domain K R, U.locus ⊆ S → P U := by
  induction hS with
  | leaf hQ => exact hbase _ hQ
  | split f g ρ hρ hg _ _ ih₁ ih₂ =>
    intro U hU
    apply hstep U
    have hunit : IsUnit (U.baseMap g) :=
      (isUnit_iff_forall_spectrum_ne_zero U.algebra _).mpr
        (fun y => hg _ (hU (U.represents.hasImageIn y)))
    obtain ⟨u, hu⟩ := hunit
    have key : ∀ y : BanachSpectrum U.algebra,
        y (U.baseMap f * ↑u⁻¹) * y (U.baseMap g) = y (U.baseMap f) := by
      intro y
      rw [← spec_mul, ← hu, mul_assoc, Units.inv_mul, mul_one]
    refine ⟨U.baseMap f * ↑u⁻¹, ρ, hρ, fun U₁ U₂ h₁ h₂ => ⟨ih₁ U₁ ?_, ih₂ U₂ ?_⟩⟩
    · rw [h₁]
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨hU (U.represents.hasImageIn y), ?_⟩
      change y (U.baseMap f) ≤ ρ * y (U.baseMap g)
      rw [← key y]
      exact mul_le_mul_of_nonneg_right hy (spec_nonneg _ _)
    · rw [h₂]
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨hU (U.represents.hasImageIn y), ?_⟩
      change ρ * y (U.baseMap g) ≤ y (U.baseMap f)
      rw [← key y]
      exact mul_le_mul_of_nonneg_right hy (spec_nonneg _ _)

omit [CompleteSpace K] in
/-- Splitting a set successively along every test of a finite family: it suffices
that every subset lying on one side of each test is refined. -/
theorem fine_of_tests {Q : Set (BanachSpectrum R) → Prop} {ι : Type*}
    (f g : ι → R) (ρ : ι → ℝ) (s : Finset ι) (hρ : ∀ i ∈ s, 0 < ρ i)
    (S : Set (BanachSpectrum R)) (hg : ∀ i ∈ s, ∀ x ∈ S, x (g i) ≠ 0)
    (h : ∀ C ⊆ S, (∀ i ∈ s, C ⊆ lowerSide (f i) (g i) (ρ i) ∨
      C ⊆ upperSide (f i) (g i) (ρ i)) → Fine Q C) :
    Fine Q S := by
  classical
  induction s using Finset.induction_on generalizing S with
  | empty => exact h S subset_rfl (by simp)
  | insert i s hi ih =>
    refine Fine.split (f i) (g i) (ρ i) (hρ i (Finset.mem_insert_self _ _))
      (hg i (Finset.mem_insert_self _ _)) ?_ ?_
    · refine ih (fun j hj => hρ j (Finset.mem_insert_of_mem hj)) _
        (fun j hj x hx => hg j (Finset.mem_insert_of_mem hj) x hx.1) ?_
      intro C hC hCs
      refine h C (hC.trans Set.inter_subset_left) ?_
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Or.inl (hC.trans Set.inter_subset_right)
      · exact hCs j hj
    · refine ih (fun j hj => hρ j (Finset.mem_insert_of_mem hj)) _
        (fun j hj x hx => hg j (Finset.mem_insert_of_mem hj) x hx.1) ?_
      intro C hC hCs
      refine h C (hC.trans Set.inter_subset_left) ?_
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Or.inr (hC.trans Set.inter_subset_right)
      · exact hCs j hj

section Charts

variable {n : ℕ} {m : Fin n → ℕ}

/-- The product element `∏ₖ h k (ν k)`. -/
def prodElt (h : (k : Fin n) → Fin (m k + 1) → R) (ν : (k : Fin n) → Fin (m k + 1)) : R :=
  ∏ k, h k (ν k)

/-- The product weight `∏ₖ w k (ν k)`. -/
def prodWt (w : (k : Fin n) → Fin (m k + 1) → ℝ) (ν : (k : Fin n) → Fin (m k + 1)) : ℝ :=
  ∏ k, w k (ν k)

omit [CompleteSpace K] in
/-- Finite families of weighted elements whose chart sets
`{x | ∀ j, |h k j| / w k j ≤ |h k 0| / w k 0}` cover the spectrum, and whose
families have no common zero, give a test tree of the whole spectrum whose
leaves lie in chart sets or are empty. -/
theorem fine_univ_of_charts {Q : Set (BanachSpectrum R) → Prop}
    (hmono : ∀ S S', S ⊆ S' → Q S' → Q S) (hempty : Q ∅)
    (h : (k : Fin n) → Fin (m k + 1) → R)
    (w : (k : Fin n) → Fin (m k + 1) → ℝ) (hw : ∀ k j, 0 < w k j)
    (hcov : ∀ x : BanachSpectrum R, ∃ k, ∀ j, x (h k j) / w k j ≤ x (h k 0) / w k 0)
    (hpos : ∀ (x : BanachSpectrum R) k, ∃ j, x (h k j) ≠ 0)
    (hleaf : ∀ k, Q {x | ∀ j, x (h k j) / w k j ≤ x (h k 0) / w k 0}) :
    Fine Q Set.univ := by
  classical
  have hWpos : ∀ ν, 0 < prodWt w ν := fun ν => Finset.prod_pos fun k _ => hw k (ν k)
  have hΦ : ∀ ν (x : BanachSpectrum R),
      x (prodElt h ν) / prodWt w ν = ∏ k, x (h k (ν k)) / w k (ν k) := by
    intro ν x
    rw [prodElt, prodWt, spec_prod, Finset.prod_div_distrib]
  have hφ0 : ∀ (x : BanachSpectrum R) k j, 0 ≤ x (h k j) / w k j :=
    fun x k j => div_nonneg (spec_nonneg _ _) (hw k j).le
  have hφpos : ∀ (x : BanachSpectrum R) k, ∃ j, 0 < x (h k j) / w k j := by
    intro x k
    obtain ⟨j, hj⟩ := hpos x k
    exact ⟨j, div_pos (lt_of_le_of_ne (spec_nonneg _ _) (Ne.symm hj)) (hw k j)⟩
  set N := Finset.univ.filter (fun ν : (k : Fin n) → Fin (m k + 1) => ∃ k, ν k = 0) with hN
  have hNpos : ∀ x : BanachSpectrum R, ∃ μ ∈ N, 0 < x (prodElt h μ) / prodWt w μ := by
    intro x
    obtain ⟨k0, hk0⟩ := hcov x
    obtain ⟨μ, hμ, hμpos⟩ :=
      exists_prod_pos (fun k j => x (h k j) / w k j) (hφpos x) k0 hk0
    exact ⟨μ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, k0, hμ⟩, (hΦ μ x).symm ▸ hμpos⟩
  -- A uniform positive threshold below the maximal product.
  obtain ⟨c, hc, hcx⟩ : ∃ c : ℝ, 0 < c ∧
      ∀ x : BanachSpectrum R, ∃ μ ∈ N, c < x (prodElt h μ) / prodWt w μ := by
    rcases isEmpty_or_nonempty (BanachSpectrum R) with hX | hX
    · exact ⟨1, one_pos, fun x => isEmptyElim x⟩
    · let G : BanachSpectrum R → ℝ := fun x => ∑ μ ∈ N, x (prodElt h μ) / prodWt w μ
      have hG : Continuous G := continuous_finsetSum _ fun μ _ =>
        (BanachSpectrum.evaluation (prodElt h μ)).continuous.div_const _
      obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hG.continuousOn
      have hGpos : 0 < G x0 := by
        obtain ⟨μ, hμ, hμpos⟩ := hNpos x0
        exact Finset.sum_pos' (fun ν _ => div_nonneg (spec_nonneg _ _) (hWpos ν).le)
          ⟨μ, hμ, hμpos⟩
      refine ⟨G x0 / (N.card + 1), by positivity, fun x => ?_⟩
      refine Finset.exists_lt_of_sum_lt (s := N) (f := fun _ => G x0 / (N.card + 1))
        (g := fun μ => x (prodElt h μ) / prodWt w μ) ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      calc (N.card : ℝ) * (G x0 / (N.card + 1)) < G x0 := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
            nlinarith
        _ ≤ G x := isMinOn_iff.mp hx0 x (Set.mem_univ x)
  -- Stage one: compare every product with the threshold.
  refine fine_of_tests (prodElt h) (fun _ => 1) (fun ν => c * prodWt w ν) N
    (fun ν _ => mul_pos hc (hWpos ν)) Set.univ
    (fun ν _ x _ => by rw [spec_one]; exact one_ne_zero) ?_
  intro C _ hC
  set T := N.filter (fun ν => ¬ C ⊆ lowerSide (prodElt h ν) 1 (c * prodWt w ν)) with hT
  have hlow : ∀ ν ∈ N, ν ∉ T → ∀ x ∈ C, x (prodElt h ν) / prodWt w ν ≤ c := by
    intro ν hν hνT x hx
    have hsub : C ⊆ lowerSide (prodElt h ν) 1 (c * prodWt w ν) := by
      by_contra hcon
      exact hνT (Finset.mem_filter.mpr ⟨hν, hcon⟩)
    have hx' := hsub hx
    simp only [lowerSide, Set.mem_ofPred_eq, spec_one, mul_one] at hx'
    rw [div_le_iff₀ (hWpos ν)]
    exact hx'
  have hup : ∀ ν ∈ T, ∀ x ∈ C, c ≤ x (prodElt h ν) / prodWt w ν := by
    intro ν hνT x hx
    obtain ⟨hν, hcon⟩ := Finset.mem_filter.mp hνT
    have hsub : C ⊆ upperSide (prodElt h ν) 1 (c * prodWt w ν) := (hC ν hν).resolve_left hcon
    have hx' := hsub hx
    simp only [upperSide, Set.mem_ofPred_eq, spec_one, mul_one] at hx'
    rw [le_div_iff₀ (hWpos ν)]
    exact hx'
  -- Stage two: compare the products that stay above the threshold.
  refine fine_of_tests (fun p : _ × _ => prodElt h p.1) (fun p => prodElt h p.2)
    (fun p => prodWt w p.1 / prodWt w p.2) (T ×ˢ T)
    (fun p _ => div_pos (hWpos _) (hWpos _)) C ?_ ?_
  · intro p hp x hx h0
    have := hup p.2 (Finset.mem_product.mp hp).2 x hx
    rw [h0, zero_div] at this
    linarith
  intro C' hC'C hC'
  have hcmp : ∀ μ ∈ T, ∀ ν ∈ T,
      (∀ x ∈ C', x (prodElt h μ) / prodWt w μ ≤ x (prodElt h ν) / prodWt w ν) ∨
      (∀ x ∈ C', x (prodElt h ν) / prodWt w ν ≤ x (prodElt h μ) / prodWt w μ) := by
    intro μ hμ ν hν
    rcases hC' (μ, ν) (Finset.mem_product.mpr ⟨hμ, hν⟩) with hs | hs
    · left
      intro x hx
      exact (le_mul_iff_div_le (hWpos μ) (hWpos ν)).mp (hs hx)
    · right
      intro x hx
      exact (mul_le_iff_div_le (hWpos μ) (hWpos ν)).mp (hs hx)
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · refine Fine.leaf (hmono C' ∅ ?_ hempty)
    intro x hx
    obtain ⟨μ, hμN, hμ⟩ := hcx x
    have hμT : μ ∉ T := by
      rw [hTe]
      exact Finset.notMem_empty μ
    have := hlow μ hμN hμT x (hC'C hx)
    exact absurd (hμ.trans_le this) (lt_irrefl c)
  · obtain ⟨ν, hνT, hmax⟩ := exists_max_of_total
      (fun μ ν => ∀ x ∈ C', x (prodElt h μ) / prodWt w μ ≤ x (prodElt h ν) / prodWt w ν)
      (fun a b c hab hbc x hx => (hab x hx).trans (hbc x hx)) T hcmp hTne
    obtain ⟨-, k, hk⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hνT).1
    refine Fine.leaf (hmono C' _ ?_ (hleaf k))
    intro x hx
    obtain ⟨k0, hk0⟩ := hcov x
    intro j
    refine le_zero_of_isMax (fun k j => x (h k j) / w k j) (hφ0 x) (hφpos x) k0 hk0 ν k hk
      ?_ j
    intro μ hμ0
    rw [← hΦ, ← hΦ]
    by_cases hμT : μ ∈ T
    · exact hmax μ hμT x hx
    · exact (hlow μ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, k0, hμ0⟩) hμT x
        (hC'C hx)).trans (hup ν hνT x (hC'C hx))

end Charts

section Rational

/-- The denominator followed by the numerators of a rational chart. -/
def chartElt (d : RationalChart K R) : Fin (d.arity + 1) → R :=
  Fin.cons (presentationMap K R d.denominator) fun j => presentationMap K R (d.numerators j)

/-- The weight one followed by the radii of a rational chart. -/
def chartWt (d : RationalChart K R) : Fin (d.arity + 1) → ℝ :=
  Fin.cons 1 fun j => d.radii j

omit [CompleteSpace K] in
theorem chartWt_pos (d : RationalChart K R) (j : Fin (d.arity + 1)) : 0 < chartWt d j := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [chartWt]
  · simp only [chartWt, Fin.cons_succ]
    exact d.radii.positive j

omit [CompleteSpace K] in
theorem mem_locus_iff (d : RationalChart K R) (x : BanachSpectrum R) :
    x ∈ d.locus ↔
      ∀ j, x (chartElt d j) / chartWt d j ≤ x (chartElt d 0) / chartWt d 0 := by
  change (∀ j, x (presentationMap K R (d.numerators j)) ≤
    d.radii j * x (presentationMap K R d.denominator)) ↔ _
  constructor
  · intro hx j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact le_rfl
    · simp only [chartElt, chartWt, Fin.cons_succ, Fin.cons_zero, div_one]
      rw [div_le_iff₀ (d.radii.positive j), mul_comm]
      exact hx j
  · intro hx j
    have := hx j.succ
    simp only [chartElt, chartWt, Fin.cons_succ, Fin.cons_zero, div_one] at this
    rw [div_le_iff₀ (d.radii.positive j), mul_comm] at this
    exact this

theorem exists_chartElt_ne_zero (d : RationalChart K R) (x : BanachSpectrum R) :
    ∃ j, x (chartElt d j) ≠ 0 := by
  have hspan : Ideal.span (Set.range (chartElt d)) = ⊤ := by
    rw [chartElt, Fin.range_cons]
    exact d.generates
  exact (span_range_eq_top_iff_forall_spectrum_exists_ne_zero R _ (chartElt d)).mp hspan x

end Rational

end LaurentInduction

open LaurentInduction in
/-- Every nonempty finite full-domain cover of the whole spectrum is refined by a
finite tree of real-radius binary Laurent splits. -/
theorem finiteCoverBinaryLaurentInduction :
    FiniteCoverBinaryLaurentInductionStatement.{u} := by
  intro K _ _ _ R c P hc hbase hstep
  classical
  let Q : Set (BanachSpectrum R) → Prop := fun S => ∃ i, S ⊆ (c.obj i).locus
  let r := c.relativeRationalRefinement
  have hsub : ∀ k, (r.chart k).locus ⊆ (c.obj (r.index k)).locus := by
    intro k x hx
    have hx' : x ∈ ((Domain.whole K R).extend (r.chart k).toDomain).locus := by
      rw [Domain.extend_locus, RationalChart.toDomain_locus]
      exact ⟨x, hx, BanachSpectrum.ext fun _ => rfl⟩
    exact Domain.Inclusion.subset (r.map k) hx'
  have hfine : Fine Q Set.univ := by
    refine fine_univ_of_charts (n := r.size) (m := fun k => (r.chart k).arity)
      (fun S S' hSS' ⟨i, hi⟩ => ⟨i, hSS'.trans hi⟩) ⟨⟨0, hc⟩, Set.empty_subset _⟩
      (fun k => chartElt (r.chart k)) (fun k => chartWt (r.chart k))
      (fun k j => chartWt_pos (r.chart k) j) ?_ ?_ ?_
    · intro x
      obtain ⟨k, hk⟩ := r.covers x
      exact ⟨k, (mem_locus_iff (r.chart k) x).mp hk⟩
    · intro x k
      exact exists_chartElt_ne_zero (r.chart k) x
    · intro k
      refine ⟨r.index k, fun x hx => hsub k ?_⟩
      exact (mem_locus_iff (r.chart k) x).mpr hx
  exact prop_of_fine P (fun S ⟨i, hi⟩ U hU => hbase U ⟨i, hU.trans hi⟩) hstep hfine _
    (Set.subset_univ _)

end Langlands.Analytic.PresentedAffinoidAlgebra
