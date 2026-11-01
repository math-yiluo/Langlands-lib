import Langlands.Geometry.Analytic.Spectrum.NonarchimedeanDominationStatement
import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm
import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Zorn

/-! # Multiplicative domination by minimal ultrametric seminorms -/

noncomputable section

universe u

namespace Langlands.Analytic.BanachSpectrum

private def dominationConditions {A : Type u} [CommRing A]
    (p : RingSeminorm A) (f : A → ℝ) : Prop :=
  f 0 = 0 ∧ f 1 = 1 ∧
  (∀ a b, f (a + b) ≤ max (f a) (f b)) ∧
  (∀ a, f (-a) = f a) ∧ (∀ a b, f (a * b) ≤ f a * f b) ∧
  (∀ a, 0 ≤ f a) ∧ ∀ a, f a ≤ p a

private theorem dominationConditions_closed {A : Type u} [CommRing A]
    (p : RingSeminorm A) :
    IsClosed {f : A → ℝ | dominationConditions p f} := by
  simp only [dominationConditions, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_eq (continuous_apply 0) continuous_const).inter
    ((isClosed_eq (continuous_apply 1) continuous_const).inter
    ((isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le (continuous_apply (a + b))
        ((continuous_apply a).max (continuous_apply b))).inter
    ((isClosed_iInter fun a =>
      isClosed_eq (continuous_apply (-a)) (continuous_apply a)).inter
    ((isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le (continuous_apply (a * b))
        ((continuous_apply a).mul (continuous_apply b))).inter
    ((isClosed_iInter fun a => isClosed_le continuous_const (continuous_apply a)).inter
      (isClosed_iInter fun a => isClosed_le (continuous_apply a) continuous_const))))))

private theorem dominationConditions_compact {A : Type u} [CommRing A]
    (p : RingSeminorm A) :
    IsCompact {f : A → ℝ | dominationConditions p f} := by
  apply (isCompact_univ_pi fun a : A =>
    isCompact_Icc (a := (0 : ℝ)) (b := p a)).of_isClosed_subset
      (dominationConditions_closed p)
  intro f hf a _
  exact ⟨hf.2.2.2.2.2.1 a, hf.2.2.2.2.2.2 a⟩

private theorem exists_minimal_of_compact_functions {A : Type u}
    (S : Set (A → ℝ)) (hS : IsCompact S) (hne : S.Nonempty) :
    ∃ f, Minimal (· ∈ S) f := by
  apply zorn_ge₀ S
  intro c hc hchain
  rcases c.eq_empty_or_nonempty with rfl | hcne
  · obtain ⟨f, hf⟩ := hne
    exact ⟨f, hf, by simp⟩
  · let t : c → Set (A → ℝ) := fun g => S ∩ {f | f ≤ (g : A → ℝ)}
    have htclosed (g : c) : IsClosed (t g) := by
      apply hS.isClosed.inter
      change IsClosed {f : A → ℝ | ∀ a, f a ≤ g.val a}
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun a =>
        isClosed_le (continuous_apply a) continuous_const
    have htdir : Directed (· ⊇ ·) t := by
      intro g h
      rcases hchain.total g.property h.property with hgh | hhg
      · refine ⟨h, ?_, Set.Subset.rfl⟩
        intro f hf
        exact ⟨hf.1, hf.2.trans hgh⟩
      · refine ⟨g, Set.Subset.rfl, ?_⟩
        intro f hf
        exact ⟨hf.1, hf.2.trans hhg⟩
    have htnonempty (g : c) : (t g).Nonempty := by
      change ∃ f : A → ℝ, f ∈ S ∧ f ≤ g.val
      exact ⟨g.val, hc g.property, le_rfl⟩
    have htcompact (g : c) : IsCompact (t g) :=
      hS.of_isClosed_subset (htclosed g) (fun _ hf => hf.1)
    let : Nonempty c := hcne.to_subtype
    obtain ⟨f, hf⟩ :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        t htdir htnonempty htcompact htclosed
    obtain ⟨g, hg⟩ := hcne
    refine ⟨f, (Set.mem_iInter.mp hf ⟨g, hg⟩).1, ?_⟩
    intro h hh
    exact (Set.mem_iInter.mp hf ⟨h, hh⟩).2

private def dominationSeminorm {A : Type u} [CommRing A]
    {p : RingSeminorm A} {f : A → ℝ} (hf : dominationConditions p f) :
    RingSeminorm A where
  toFun := f
  map_zero' := hf.1
  add_le' _ _ := IsNonarchimedean.add_le hf.2.2.2.2.2.1 hf.2.2.1
  neg' := hf.2.2.2.1
  mul_le' := hf.2.2.2.2.1

private theorem dominationConditions_of_seminorm {A : Type u} [CommRing A]
    (p q : RingSeminorm A) (hq1 : q 1 = 1)
    (hqna : IsNonarchimedean q) (hqp : ∀ a, q a ≤ p a) :
    dominationConditions p q :=
  ⟨map_zero q, hq1, hqna, map_neg_eq_map q, map_mul_le_mul q,
    apply_nonneg q, hqp⟩

/-- A normalized ultrametric ring seminorm dominates a multiplicative one. -/
theorem nonarchimedeanDomination : NonarchimedeanDominationStatement.{u} := by
  intro A _ p hp1 hpna
  obtain ⟨f, hf⟩ := exists_minimal_of_compact_functions
    {f : A → ℝ | dominationConditions p f} (dominationConditions_compact p)
    ⟨p, dominationConditions_of_seminorm p p hp1 hpna (fun _ => le_rfl)⟩
  let q : RingSeminorm A := dominationSeminorm hf.1
  have hq1 : q 1 = 1 := hf.1.2.1
  have hqna : IsNonarchimedean q := hf.1.2.2.1
  have hqp (a : A) : q a ≤ p a := hf.1.2.2.2.2.2.2 a
  have hqminimal (r : RingSeminorm A) (hr1 : r 1 = 1)
      (hrna : IsNonarchimedean r) (hrq : ∀ a, r a ≤ q a) : r = q := by
    apply RingSeminorm.ext
    have heq := hf.eq_of_le
      (dominationConditions_of_seminorm p r hr1 hrna
        (fun a => (hrq a).trans (hqp a))) hrq
    exact congrFun heq
  have hqsmooth : smoothingSeminorm q hq1.le hqna = q := by
    apply hqminimal
    · change smoothingFun q 1 = 1
      rw [smoothingFun]
      simp only [one_pow, hq1, Real.one_rpow, ciInf_const]
    · exact isNonarchimedean_smoothingFun q hq1.le hqna
    · exact smoothingFun_le_self q
  have hqpow : IsPowMul q := by
    have h := isPowMul_smoothingFun q hq1.le
    change IsPowMul (smoothingSeminorm q hq1.le hqna) at h
    rwa [hqsmooth] at h
  have hqmul (a b : A) : q (a * b) = q a * q b := by
    by_cases ha : q a = 0
    · apply le_antisymm (map_mul_le_mul q a b)
      rw [ha, zero_mul]
      exact apply_nonneg q _
    · have heq : seminormFromConst ha hqpow = q := by
        apply hqminimal
        · exact seminormFromConst_one ha hqpow
        · exact seminormFromConst_isNonarchimedean ha hqpow hqna
        · exact seminormFromConst_le_seminorm ha hqpow
      have h := seminormFromConst_const_mul ha hqpow b
      change seminormFromConst ha hqpow (a * b) =
        seminormFromConst ha hqpow a * seminormFromConst ha hqpow b at h
      rwa [heq] at h
  refine ⟨{
    toFun := q
    map_zero' := map_zero q
    map_one' := hq1
    map_mul' := hqmul
    add_le' := map_add_le_add q
    neg' := map_neg_eq_map q
  }, hqna, hqp⟩

end Langlands.Analytic.BanachSpectrum
