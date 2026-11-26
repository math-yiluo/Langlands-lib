import Langlands.Global.ArthurTruncationAverage

/-! # Pairing a periodized compact radical average -/

noncomputable section

set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme LeftCosetSpace
open RankinSelbergGlobal.Unfolding (cosetRep cosetRep_mem existsUnique_cosetRep)

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G
local notation "haarA" => (Measure.haar : Measure A)

section Discrete

variable (Γ Λ : Subgroup (AdelicGroupPoints F G))

local notation "Index" => LeftCosetSpace (Λ.subgroupOf Γ)
local notation "rep" => cosetRep Λ Γ

/-- The periodization of a function on the smaller rational quotient. -/
def periodize (f : A → ℂ) (x : A) : ℂ := ∑' c : Index, f (rep c * x)

private theorem periodize_invariant {f : A → ℂ}
    (hf : ∀ l ∈ Λ, ∀ x, f (l * x) = f x) (g : Γ) (x : A) :
    periodize Γ Λ f ((g : A) * x) = periodize Γ Λ f x := by
  let e := rightTranslateHomeomorph (Λ.subgroupOf Γ) g
  have h (c : Index) : f (rep c * ((g : A) * x)) = f (rep (e c) * x) := by
    have he : mk (Λ.subgroupOf Γ) (c.out * g) = mk (Λ.subgroupOf Γ) (e c).out := by
      calc
        mk (Λ.subgroupOf Γ) (c.out * g) = e (mk (Λ.subgroupOf Γ) c.out) := rfl
        _ = e c := congrArg e (Quotient.out_eq c)
        _ = mk (Λ.subgroupOf Γ) (e c).out := (Quotient.out_eq (e c)).symm
    have hc : (e c).out * (c.out * g)⁻¹ ∈ Λ.subgroupOf Γ :=
      (mk_eq_mk_iff (Λ.subgroupOf Γ) (c.out * g) (e c).out).mp he
    have hl : rep (e c) * (rep c * (g : A))⁻¹ ∈ Λ := by
      simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, cosetRep] using hc
    have hprod : rep (e c) * x = (rep (e c) * (rep c * (g : A))⁻¹) * (rep c * ((g : A) * x)) := by group
    rw [hprod, hf _ hl]
  unfold periodize
  calc
    (∑' c : Index, f (rep c * ((g : A) * x))) = ∑' c : Index, f (rep (e c) * x) := tsum_congr h
    _ = _ := e.toEquiv.tsum_eq (fun c : Index => f (rep c * x))

/-- A uniformly finite cutoff on compact sets makes periodization preserve local boundedness. -/
theorem periodize_locallyBounded (hΓ : IsDiscrete (Γ : Set A))
    {f w : A → ℂ} (hf : IsLocallyBoundedInvariant Λ f)
    (hw : Measurable w) (hwΛ : ∀ l ∈ Λ, ∀ x, w (l * x) = w x) (hw₁ : ∀ x, ‖w x‖ ≤ 1)
    (hfin : ∀ C : Set A, IsCompact C → ∃ E : Finset Index,
      ∀ c ∉ E, ∀ x ∈ C, w (rep c * x) = 0) :
    IsLocallyBoundedInvariant Γ (periodize Γ Λ (fun x => f x * w x)) := by
  let : Countable Γ := countable_of_isDiscrete Γ hΓ
  let : Countable Index := (mk_surjective (Λ.subgroupOf Γ)).countable
  have hinv (l : A) (hl : l ∈ Λ) (x : A) : f (l * x) * w (l * x) = f x * w x := by
    rw [hf.2.2 _ hl, hwΛ _ hl]
  refine ⟨Measurable.tsum (fun c : Index => (hf.1.mul hw).comp (measurable_const.mul measurable_id)),
    ?_, fun g hg x => periodize_invariant Γ Λ hinv ⟨g, hg⟩ x⟩
  intro C hC
  obtain ⟨E, hE⟩ := hfin C hC
  let R := rep '' (E : Set Index) * C
  have hR : IsCompact R := (E.finite_toSet.image rep).isCompact.mul hC
  obtain ⟨M, hM⟩ := hf.2.1 R hR
  refine ⟨(E.card : ℝ) * M, fun x hx => ?_⟩
  unfold periodize
  rw [tsum_eq_sum (s := E) (fun c hc => by
    change f (rep c * x) * w (rep c * x) = 0
    rw [hE c hc x hx, mul_zero])]
  calc
    ‖∑ c ∈ E, f (rep c * x) * w (rep c * x)‖ ≤ ∑ c ∈ E, ‖f (rep c * x) * w (rep c * x)‖ :=
      norm_sum_le E _
    _ ≤ ∑ _ ∈ E, M := Finset.sum_le_sum fun c hc => by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hw₁ _)).trans
        (hM _ (Set.mul_mem_mul ⟨c, hc, rfl⟩ hx))
    _ = _ := by simp

private theorem out_mk_value {f : A → ℂ}
    (hf : ∀ l ∈ Λ, ∀ x, f (l * x) = f x) (x : A) : f (mk Λ x).out = f x := by
  obtain ⟨l, hl⟩ := RankinSelbergGlobal.Unfolding.exists_out_mk_eq Λ x
  rw [hl, hf _ l.2]

private theorem integrableOn_fundamentalDomain_of_compact_support (hΛ : IsDiscrete (Λ : Set A))
    {f : A → ℂ} (hf : IsLocallyBoundedInvariant Λ f)
    (hs : ∃ C : Set A, IsCompact C ∧ ∀ x, f x ≠ 0 → ∃ l ∈ Λ, l * x ∈ C) :
    IntegrableOn f (fundamentalDomain Λ hΛ) haarA := by
  let : BorelSpace (LeftCosetSpace Λ) := discreteQuotientBorelSpace Λ hΛ
  let : IsClosed (Λ : Set A) := Λ.isClosed_of_isDiscrete hΛ
  let μΛ := discreteQuotientMeasure Λ hΛ haarA
  let : IsLocallyFiniteMeasure μΛ := isLocallyFiniteMeasure_discreteQuotientMeasure Λ hΛ haarA
  let fQ : LeftCosetSpace Λ → ℂ := fun y => f y.out
  have hm : Measurable fQ := by
    apply measurable_from_quotient.mpr
    change Measurable (fQ ∘ mk Λ)
    rw [show fQ ∘ mk Λ = f from funext (out_mk_value Λ hf.2.2)]
    exact hf.1
  obtain ⟨C, hC, hCov⟩ := hs
  let Cq := mk Λ '' C
  have hCq : IsCompact Cq := hC.image (continuous_mk Λ)
  obtain ⟨M, hM⟩ := hf.2.1 C hC
  have hbd : ∀ y ∈ Cq, ‖fQ y‖ ≤ M := by
    rintro y ⟨x, hx, rfl⟩
    simpa only [fQ, out_mk_value Λ hf.2.2] using hM x hx
  have hzero : ∀ y ∉ Cq, fQ y = 0 := by
    intro y hy
    by_contra hfne
    obtain ⟨l, hl, hxy⟩ := hCov y.out hfne
    apply hy
    refine ⟨l * y.out, hxy, ?_⟩
    exact (mk_subgroup_mul Λ ⟨l, hl⟩ _).trans (Quotient.out_eq y)
  have hi : IntegrableOn fQ Cq μΛ := μΛ.integrableOn_of_bounded hCq.measure_lt_top.ne
    hm.aestronglyMeasurable ((ae_restrict_iff' hCq.isClosed.measurableSet).mpr
      (Filter.Eventually.of_forall hbd))
  have he : Cq.indicator fQ = fQ := by
    funext y
    by_cases hy : y ∈ Cq
    · exact Set.indicator_of_mem hy _
    · rw [Set.indicator_of_notMem hy, hzero y hy]
  have hfQ : Integrable fQ μΛ := he ▸ hi.integrable_indicator hCq.isClosed.measurableSet
  exact (RankinSelbergGlobal.Unfolding.integrable_out_iff Λ hf.1
    (fun l x => hf.2.2 l l.2 x) haarA _).mp hfQ

private theorem unfold_periodize (hle : Λ ≤ Γ) (hΓ : IsDiscrete (Γ : Set A))
    {f : A → ℂ} (hf : ∀ l ∈ Λ, ∀ x, f (l * x) = f x)
    (hint : IntegrableOn f (fundamentalDomain Λ (hΓ.mono hle)) haarA) :
    IntegrableOn (periodize Γ Λ f) (fundamentalDomain Γ hΓ) haarA ∧
      (∫ x in fundamentalDomain Γ hΓ, periodize Γ Λ f x ∂haarA) =
        ∫ x in fundamentalDomain Λ (hΓ.mono hle), f x ∂haarA := by
  let : Countable Γ := countable_of_isDiscrete Γ hΓ
  let : Countable Λ := countable_of_isDiscrete Λ (hΓ.mono hle)
  let : Countable Index := (mk_surjective (Λ.subgroupOf Γ)).countable
  have hd := isFundamentalDomain Λ (hΓ.mono hle) haarA
  have hUnion := EisensteinConstantTerm.isFundamentalDomain_iUnion_smul hle
    (measurableSet_fundamentalDomain Γ hΓ) (fundamentalDomain_unique Γ hΓ)
    rep (cosetRep_mem Λ Γ) (existsUnique_cosetRep Λ Γ) haarA
  have hi := (hd.integrableOn_iff hUnion (fun l x => hf l l.2 x)).mp hint
  obtain ⟨hI, hEq⟩ := RankinSelbergGlobal.Unfolding.integrableOn_tsum_and_setIntegral_eq haarA
    (measurableSet_fundamentalDomain Γ hΓ) (fundamentalDomain_unique Γ hΓ)
    rep (cosetRep_mem Λ Γ) (existsUnique_cosetRep Λ Γ) hi
  exact ⟨hI, hEq.trans (hUnion.setIntegral_eq hd (fun l x => hf l l.2 x))⟩

end Discrete

section Radical

open AdelicSubgroupPoints

variable (U : SubgroupFunctor G)
  [hclosed : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]
  [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G U)]
  (Γ Λ : Subgroup (AdelicGroupPoints F G))
  (hle : Λ ≤ Γ) (hΓ : IsDiscrete (Γ : Set (AdelicGroupPoints F G)))
  (hUΛ : ∀ n ∈ AdelicSubgroupPoints.rationalSubgroup F G U,
    ((n : adelicPoints F G U) : AdelicGroupPoints F G) ∈ Λ)
  (hconj : ∀ l ∈ Λ, ∀ n ∈ AdelicSubgroupPoints.rationalSubgroup F G U,
    ∃ n' ∈ AdelicSubgroupPoints.rationalSubgroup F G U,
      ((n' : adelicPoints F G U) : AdelicGroupPoints F G) = l * n * l⁻¹)
  (hnorm : ∀ l ∈ Λ, ∀ n ∈ adelicPoints F G U, l * n * l⁻¹ ∈ adelicPoints F G U)

local notation "Avg" => ConstantTermComposition.average U
local notation "N" => adelicPoints F G U
local notation "Δ" => AdelicSubgroupPoints.rationalSubgroup F G U
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G U
local notation "Index" => LeftCosetSpace (Λ.subgroupOf Γ)
local notation "rep" => cosetRep Λ Γ
local notation "μU" => normalizedRationalQuotientHaarMeasure F G U
local notation "dΓ" => fundamentalDomain Γ hΓ
local notation "dΛ" => fundamentalDomain Λ (IsDiscrete.mono hΓ hle)

include hUΛ hconj hnorm in
/-- The compact radical average preserves local boundedness, measurability and rational
invariance under the normalizing subgroup. -/
theorem IsLocallyBoundedInvariant.average {f : A → ℂ}
    (hΛ : IsDiscrete (Λ : Set A)) (hf : IsLocallyBoundedInvariant Λ f) :
    IsLocallyBoundedInvariant Λ (Avg f) := by
  obtain ⟨hm, hb⟩ := compactAverage_locallyBounded U hUΛ hΛ hf
  exact ⟨hm, hb, fun l hl x => compactAverage_mul_left U hUΛ hconj hnorm hf.2.2 ⟨l, hl⟩ x⟩

private theorem locallyBounded_mul {f g : A → ℂ}
    (hf : IsLocallyBoundedInvariant Λ f) (hg : IsLocallyBoundedInvariant Λ g) :
    IsLocallyBoundedInvariant Λ (fun x => f x * g x) := by
  have hinv (l : A) (hl : l ∈ Λ) (x : A) : f (l * x) * g (l * x) = f x * g x := by
    rw [hf.2.2 _ hl, hg.2.2 _ hl]
  refine ⟨hf.1.mul hg.1, fun C hC => ?_, hinv⟩
  obtain ⟨B, hB⟩ := hf.2.1 C hC
  obtain ⟨M, hM⟩ := hg.2.1 C hC
  refine ⟨max B 0 * max M 0, fun x hx => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hB x hx).trans (le_max_left _ _)) ((hM x hx).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

include hUΛ hnorm in
private theorem compact_support_weighted_averages {w b : A → ℂ}
    (hwΛ : ∀ l ∈ Λ, ∀ x, w (l * x) = w x) (hwN : ∀ n : N, ∀ x, w ((n : A) * x) = w x)
    (hfin : ∀ C : Set A, IsCompact C → ∃ E : Finset Index,
      ∀ c ∉ E, ∀ x ∈ C, w (rep c * x) = 0)
    (hbs : ∃ C : Set A, IsCompact C ∧ ∀ x, b x ≠ 0 → ∃ g ∈ Γ, g * x ∈ C) :
    (∃ C : Set A, IsCompact C ∧ ∀ x, w x ≠ 0 → b x ≠ 0 → ∃ l ∈ Λ, l * x ∈ C) ∧
    (∃ C : Set A, IsCompact C ∧ ∀ x, w x ≠ 0 → Avg b x ≠ 0 → ∃ l ∈ Λ, l * x ∈ C) := by
  classical
  obtain ⟨C, hC, hC'⟩ := hbs
  obtain ⟨E, hE⟩ := hfin C hC
  let L := rep '' (E : Set Index) * C
  have hL : IsCompact L := (E.finite_toSet.image rep).isCompact.mul hC
  have hLift (x : A) (hwx : w x ≠ 0) (hbx : b x ≠ 0) :
      ∃ l ∈ Λ, ∃ y ∈ L, x = l * y := by
    obtain ⟨g, hg, hy⟩ := hC' x hbx
    let a : Γ := ⟨g⁻¹, Γ.inv_mem hg⟩
    let c : Index := mk (Λ.subgroupOf Γ) a
    let l := g⁻¹ * (rep c)⁻¹
    have hl : l ∈ Λ := (mk_eq_mk_iff (Λ.subgroupOf Γ) c.out a).mp (Quotient.out_eq c)
    have he : x = l * (rep c * (g * x)) := by dsimp only [l]; group
    have hce : c ∈ E := by
      by_contra hn
      exact hwx (by rw [he, hwΛ _ hl, hE c hn _ hy])
    exact ⟨l, hl, _, Set.mul_mem_mul ⟨c, hce, rfl⟩ hy, he⟩
  refine ⟨⟨L, hL, fun x hwx hbx => ?_⟩, ?_⟩
  · obtain ⟨l, hl, y, hy, hxy⟩ := hLift x hwx hbx
    exact ⟨l⁻¹, Λ.inv_mem hl, by rwa [hxy, inv_mul_cancel_left]⟩
  obtain ⟨D, hD, hD'⟩ := exists_compact_radical_representatives U
  refine ⟨(fun n : N => (n : A)) '' D * L, (hD.image continuous_subtype_val).mul hL,
    fun x hwx hbx => ?_⟩
  have hsome : ∃ n : N, b ((n : A) * x) ≠ 0 := by
    by_contra! hnone
    apply hbx
    change (∫ q : Q, b (((q.out : N) : A) * x) ∂μU) = 0
    simp only [hnone, integral_zero]
  obtain ⟨n, hn⟩ := hsome
  obtain ⟨l, hl, y, hy, he⟩ := hLift ((n : A) * x) (by simpa only [hwN n x] using hwx) hn
  let v : N := ⟨l⁻¹ * (n : A)⁻¹ * l, by
    simpa only [inv_inv] using hnorm _ (Λ.inv_mem hl) _ ((adelicPoints F G U).inv_mem n.2)⟩
  obtain ⟨m, hm, hm'⟩ := hD' (mk Δ v)
  let a : N := v * m⁻¹
  have ha : a ∈ Δ := (mk_eq_mk_iff Δ m v).mp hm'
  have hla : l * (a : A) ∈ Λ := Λ.mul_mem hl (hUΛ _ ha)
  have hx : x = (l * (a : A)) * ((m : A) * y) := by
    calc
      x = (n : A)⁻¹ * (l * y) := by rw [← he, inv_mul_cancel_left]
      _ = _ := by
        change (n : A)⁻¹ * (l * y) = (l * (((l⁻¹ * (n : A)⁻¹ * l) * (m : A)⁻¹))) * ((m : A) * y)
        group
  exact ⟨(l * (a : A))⁻¹, Λ.inv_mem hla, by
    rw [hx, inv_mul_cancel_left]
    exact Set.mul_mem_mul ⟨m, hm, rfl⟩ hy⟩

include hle hΓ hUΛ hconj hnorm in
/-- Unfolding a weighted periodization transfers the normalized radical average between the
factors of the pairing. Both products are integrable on a fundamental domain for `Γ`. -/
theorem periodize_radical_pairing {f b w : A → ℂ}
    (hf : IsLocallyBoundedInvariant Γ f) (hb : IsLocallyBoundedInvariant Γ b)
    (hw : Measurable w) (hw₁ : ∀ x, ‖w x‖ ≤ 1)
    (hwΛ : ∀ l ∈ Λ, ∀ x, w (l * x) = w x) (hwN : ∀ n : N, ∀ x, w ((n : A) * x) = w x)
    (hfin : ∀ C : Set A, IsCompact C → ∃ E : Finset Index,
      ∀ c ∉ E, ∀ x ∈ C, w (rep c * x) = 0)
    (hbs : ∃ C : Set A, IsCompact C ∧ ∀ x, b x ≠ 0 → ∃ g ∈ Γ, g * x ∈ C) :
    let left := fun x => periodize Γ Λ (fun y => Avg f y * w y) x * b x
    let right := fun x => f x * periodize Γ Λ (fun y => Avg b y * w y) x
    IntegrableOn left dΓ haarA ∧ IntegrableOn right dΓ haarA ∧
      (∫ x in dΓ, left x ∂haarA) = ∫ x in dΓ, right x ∂haarA := by
  let hΛ := hΓ.mono hle
  have hfΛ : IsLocallyBoundedInvariant Λ f := ⟨hf.1, hf.2.1, fun l hl => hf.2.2 l (hle hl)⟩
  have hbΛ : IsLocallyBoundedInvariant Λ b := ⟨hb.1, hb.2.1, fun l hl => hb.2.2 l (hle hl)⟩
  have hAf := IsLocallyBoundedInvariant.average U Λ hUΛ hconj hnorm hΛ hfΛ
  have hAb := IsLocallyBoundedInvariant.average U Λ hUΛ hconj hnorm hΛ hbΛ
  have hwbl : IsLocallyBoundedInvariant Λ w := ⟨hw, fun _ _ => ⟨1, fun x _ => hw₁ x⟩, hwΛ⟩
  let p := fun x => Avg f x * b x * w x
  let q := fun x => f x * Avg b x * w x
  have hp : IsLocallyBoundedInvariant Λ p := locallyBounded_mul Λ (locallyBounded_mul Λ hAf hbΛ) hwbl
  have hq : IsLocallyBoundedInvariant Λ q := locallyBounded_mul Λ (locallyBounded_mul Λ hfΛ hAb) hwbl
  obtain ⟨⟨C, hC, hC'⟩, ⟨D, hD, hD'⟩⟩ :=
    compact_support_weighted_averages U Γ Λ hUΛ hnorm hwΛ hwN hfin hbs
  have hpI : IntegrableOn p dΛ haarA := integrableOn_fundamentalDomain_of_compact_support Λ hΛ hp
    ⟨C, hC, fun x hx => hC' x (fun h => hx (by simp [p, h])) (fun h => hx (by simp [p, h]))⟩
  have hqI : IntegrableOn q dΛ haarA := integrableOn_fundamentalDomain_of_compact_support Λ hΛ hq
    ⟨D, hD, fun x hx => hD' x (fun h => hx (by simp [q, h])) (fun h => hx (by simp [q, h]))⟩
  obtain ⟨hPL, hPE⟩ := unfold_periodize Γ Λ hle hΓ hp.2.2 hpI
  obtain ⟨hQR, hQE⟩ := unfold_periodize Γ Λ hle hΓ hq.2.2 hqI
  have pEq (x : A) : periodize Γ Λ p x = periodize Γ Λ (fun y => Avg f y * w y) x * b x := by
    unfold periodize
    rw [← tsum_mul_right]
    exact tsum_congr fun c => by
      dsimp only [p]
      rw [hb.2.2 _ (cosetRep_mem Λ Γ c)]
      ring
  have qEq (x : A) : periodize Γ Λ q x = f x * periodize Γ Λ (fun y => Avg b y * w y) x := by
    unfold periodize
    rw [← tsum_mul_left]
    exact tsum_congr fun c => by
      dsimp only [q]
      rw [hf.2.2 _ (cosetRep_mem Λ Γ c), mul_assoc]
  have hNf : ConstantTermComposition.IsRationalInvariant F G U f := fun n hn => hfΛ.2.2 _ (hUΛ _ hn)
  have hNb : ConstantTermComposition.IsRationalInvariant F G U b := fun n hn => hbΛ.2.2 _ (hUΛ _ hn)
  have havg (x : A) : Avg p x = Avg q x := by
    have hp' (z : Q) : p (((z.out : N) : A) * x) = Avg f x * b (((z.out : N) : A) * x) * w x := by
      dsimp only [p]
      rw [ConstantTermComposition.average_subgroup_mul hNf, hwN]
    have hq' (z : Q) : q (((z.out : N) : A) * x) = f (((z.out : N) : A) * x) * Avg b x * w x := by
      dsimp only [q]
      rw [ConstantTermComposition.average_subgroup_mul hNb, hwN]
    have hpEq : Avg p x = Avg f x * Avg b x * w x := by
      change (∫ z : Q, p (((z.out : N) : A) * x) ∂μU) = _
      simp_rw [hp', integral_mul_const, integral_const_mul]
      rfl
    have hqEq : Avg q x = Avg f x * Avg b x * w x := by
      change (∫ z : Q, q (((z.out : N) : A) * x) ∂μU) = _
      simp_rw [hq', integral_mul_const]
      rfl
    exact hpEq.trans hqEq.symm
  have hSwap : (∫ x in dΛ, p x ∂haarA) = ∫ x in dΛ, q x ∂haarA := by
    rw [← setIntegral_compactAverage U hUΛ hconj hnorm hΛ hp.1 hp.2.2 hpI,
      ← setIntegral_compactAverage U hUΛ hconj hnorm hΛ hq.1 hq.2.2 hqI]
    exact integral_congr_ae (Filter.Eventually.of_forall havg)
  rw [funext pEq] at hPL hPE
  rw [funext qEq] at hQR hQE
  exact ⟨hPL, hQR, hPE.trans (hSwap.trans hQE.symm)⟩

end Radical

end Langlands.Global.ArthurTruncation
