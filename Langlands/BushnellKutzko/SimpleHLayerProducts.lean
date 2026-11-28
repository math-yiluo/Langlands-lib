import Langlands.BushnellKutzko.SimpleStratumLatticeInduction

/-! # Products of the layers `𝔥^t(β, 𝔄)` (BK93 (8.2.13) and (8.2.28))

For `t ≥ 1` the product `𝔥^t 𝔥^t` lies in `𝔔_β 𝔥^t`, where `𝔔_β = 𝔓 ∩ B`. The proof is the
induction along `β` of BK93 (8.2.13): above the cutoff the layer agrees with the layer of the
approximation, and the fractional centralizers of `β` and of the approximation act in the same
way on it (BK93 (3.1.3), (3.1.9)). Below the cutoff the layer is `𝔔^t + 𝔥^{[r/2]+1}`.
The same induction puts both products of `𝔧^1` with `𝔥^t` in `𝔔_β 𝔥^t` for `t ≥ 2`. -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.SimpleStratumLattice

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (L : LatticeChain 𝒪[F] F V)

local notation "A" => Module.End F V
local notation "P" => L.endFiltration
local notation "Q" => centralizerLattice L
local notation "N" => adjointLattice L
local notation "crit" => criticalExponent L

variable {L} {n : ℤ}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `𝔓^{t+1} ⊆ 𝔔_β 𝔓^t` for a parameter `β`. -/
theorem endFiltration_succ_le_centralizer_mul {b : A} (hb : Parameter L n b) (t : ℤ) :
    P (t + 1) ≤ Q b 1 * P t := by
  intro x hx
  have h1 := Submodule.mul_mem_mul (hb.inverse 1) hx
  rw [one_mul] at h1
  have h2 : Q b 1 * Q b (-1) * P (t + 1) ≤ Q b 1 * P t := by
    rw [mul_assoc]
    refine mul_le_mul_right ?_ _
    refine (filtration_products L _ _ inf_le_left le_rfl).trans ?_
    exact L.endFiltration_antitone (by omega)
  exact h2 h1

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `𝔔^{2t} ⊆ 𝔔 𝔔^t` for `t ≥ 1` and a parameter `β`. -/
theorem centralizer_two_le {b : A} (hb : Parameter L n b) {t : ℤ} (ht : 1 ≤ t) :
    Q b t * Q b t ≤ Q b 1 * Q b t := by
  rw [centralizer_mul L b hb.inverse, centralizer_mul L b hb.inverse]
  intro x hx
  exact ⟨L.endFiltration_antitone (by omega) hx.1, hx.2⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The integral centralizer acts on each positive layer. -/
theorem centralizer_mul_layer_le (i : Kind) {b : A} {tail : List A}
    (hprop : Properties L n i b tail) (k : ℤ) :
    Q b 0 * layer L n i b tail k ≤ layer L n i b tail k := by
  apply Submodule.mul_le.mpr
  intro x hx y hy
  refine ⟨hprop.mul (Submodule.mul_mem_mul (centralizer_le_lattice L i b tail hx) hy.1), ?_⟩
  simpa using L.mul_mem_endFiltration hx.1 hy.2

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem layer_nil_eq (i : Kind) (b : A) {t : ℤ} (ht : 0 ≤ t)
    (htc : t ≤ cutoff i n) : layer L n i b [] t = Q b t ⊔ P (cutoff i n) := by
  have hX : lattice L n i b [] = Q b 0 ⊔ P (cutoff i n) := by cases i <;> rfl
  have h : Q b 0 ⊓ P t = Q b t := by
    unfold centralizerLattice
    rw [inf_right_comm, inf_eq_right.mpr (L.endFiltration_antitone ht)]
  rw [layer, hX, sup_comm (Q b 0), sup_inf_assoc_of_le _ (L.endFiltration_antitone htc), h,
    sup_comm]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem layer_nil_high (i : Kind) (b : A) {t : ℤ} (htc : cutoff i n ≤ t) :
    layer L n i b [] t = P t := by
  have hX : lattice L n i b [] = Q b 0 ⊔ P (cutoff i n) := by cases i <;> rfl
  rw [layer, hX]
  exact inf_eq_right.mpr ((L.endFiltration_antitone htc).trans le_sup_right)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem layer_cons_low (i : Kind) {b c : A} {tail : List A} {r t : ℤ}
    (hr : crit b = ((-r : ℤ) : WithBot ℤ)) (ht : 0 ≤ t) (htc : t ≤ cutoff i r) :
    layer L n i b (c :: tail) t = Q b t ⊔ layer L n i c tail (cutoff i r) := by
  have hdepth : finiteCriticalDepth L n b = r := by
    simp [finiteCriticalDepth, simpleCriticalDepth_eq L hr]
  have hX : lattice L n i b (c :: tail) = Q b 0 ⊔ layer L n i c tail (cutoff i r) := by
    cases i <;> simp [lattice, layer, simpleHLattice, simpleJLattice, simpleStratumLattices,
      hdepth, cutoff]
  have h : Q b 0 ⊓ P t = Q b t := by
    unfold centralizerLattice
    rw [inf_right_comm, inf_eq_right.mpr (L.endFiltration_antitone ht)]
  have hle : layer L n i c tail (cutoff i r) ≤ P t :=
    inf_le_right.trans (L.endFiltration_antitone htc)
  rw [layer, hX, sup_comm (Q b 0), sup_inf_assoc_of_le (Q b 0) hle, h, sup_comm]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The square of `𝔔^t + Y` lies in `𝔔 (𝔔^t + Y)` when `Y` is stable under `𝔔^0` on both
sides, commutes with `𝔔^t`, and satisfies `Y Y ⊆ 𝔔 Y`. -/
private theorem sup_square_le {b : A} (hb : Parameter L n b) {t : ℤ} (ht : 1 ≤ t)
    {Y : Submodule 𝒪[F] A} (hQY : Q b 0 * Y ≤ Y) (hcomm : Y * Q b t = Q b t * Y)
    (hYY : Y * Y ≤ Q b 1 * Y) :
    (Q b t ⊔ Y) * (Q b t ⊔ Y) ≤ Q b 1 * (Q b t ⊔ Y) := by
  have hQtY : Q b t * Y ≤ Q b 1 * Y := by
    calc Q b t * Y = Q b 1 * Q b (t - 1) * Y := by
          rw [centralizer_mul L b hb.inverse]; ring_nf
      _ ≤ Q b 1 * Y := by
          rw [mul_assoc]
          refine mul_le_mul_right ?_ _
          refine le_trans (mul_le_mul_left ?_ Y) hQY
          intro x hx
          exact ⟨L.endFiltration_antitone (by omega) hx.1, hx.2⟩
  rw [Submodule.sup_mul, Submodule.mul_sup, Submodule.mul_sup]
  refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
  · exact (centralizer_two_le hb ht).trans (mul_le_mul_right le_sup_left _)
  · exact hQtY.trans (mul_le_mul_right le_sup_right _)
  · rw [hcomm]
    exact hQtY.trans (mul_le_mul_right le_sup_right _)
  · exact hYY.trans (mul_le_mul_right le_sup_right _)

/-- **BK93 (8.2.13).** For the H layers of a defining sequence and `t ≥ 1`,
`𝔥^t 𝔥^t ⊆ 𝔔_β 𝔥^t`. -/
theorem Sequence.layer_mul_layer_le {b : A} {tail : List A} (hseq : Sequence L n b tail)
    (hn : 0 < n) (t : ℤ) (ht : 1 ≤ t) :
    layer L n .H b tail t * layer L n .H b tail t ≤ Q b 1 * layer L n .H b tail t := by
  induction hseq generalizing t with
  | terminal hb hcrit =>
    rename_i b
    have hprop := (Sequence.terminal hb hcrit).properties hn .H
    by_cases hth : cutoff .H n ≤ t
    · rw [layer_nil_high .H b hth]
      refine (filtration_products L _ _ le_rfl le_rfl).trans ?_
      exact (L.endFiltration_antitone (by omega)).trans (endFiltration_succ_le_centralizer_mul hb t)
    · push Not at hth
      have hc : 1 ≤ cutoff .H n := by
        have := cutoff_le .H hn
        simp only [cutoff, simpleHCutoff] at hth ⊢
        omega
      rw [layer_nil_eq .H b (by omega) hth.le]
      refine sup_square_le hb ht ?_ ?_ ?_
      · exact (filtration_products L _ _ inf_le_left le_rfl).trans (le_of_eq (by rw [zero_add]))
      · have := hprop.fractional (cutoff .H n) (by omega) t
        rw [layer_nil_high .H b le_rfl] at this
        exact this.symm
      · refine (filtration_products L _ _ le_rfl le_rfl).trans ?_
        exact (L.endFiltration_antitone (by omega)).trans
          (endFiltration_succ_le_centralizer_mul hb _)
  | step hb hr hrn hcrit hc hsub next ih =>
    rename_i b c tail r
    have hseqb := Sequence.step hb hr hrn hcrit hc hsub next
    have hpropb := hseqb.properties hn .H
    have hpropc := next.properties hn .H
    -- above the cutoff
    have hhigh : ∀ s : ℤ, cutoff .H r ≤ s → 1 ≤ s →
        layer L n .H b (c :: tail) s * layer L n .H b (c :: tail) s ≤
          Q b 1 * layer L n .H b (c :: tail) s := by
      intro s hs hs1
      rw [hseqb.high_eq hn hcrit .H hs]
      have hX := hpropc.adjoint r hr.le hc.le s hs
      rw [(transfer_products L hb next.parameter hsub hX 1).1]
      exact ih s hs1
    by_cases hth : cutoff .H r ≤ t
    · exact hhigh t hth ht
    · push Not at hth
      have hcut : 1 ≤ cutoff .H r := by
        simp only [cutoff, simpleHCutoff]
        omega
      rw [layer_cons_low .H hcrit (by omega) hth.le]
      have hY : layer L n .H c tail (cutoff .H r) = layer L n .H b (c :: tail) (cutoff .H r) :=
        (hseqb.high_eq hn hcrit .H le_rfl).symm
      rw [hY]
      refine sup_square_le hb ht (centralizer_mul_layer_le .H hpropb _) ?_
        (hhigh _ le_rfl hcut)
      exact (hpropb.fractional _ (by omega) t).symm

private theorem centralizer_mul_firstJ_le {b : A} {tail : List A} (hseq : Sequence L n b tail)
    (hn : 0 < n) {t : ℤ} (ht : 2 ≤ t) :
    Q b t * layer L n .J b tail 1 ≤ Q b 1 * layer L n .H b tail t := by
  have hq : Q b (t - 1) ≤ Q b 1 :=
    inf_le_inf_right _ (L.endFiltration_antitone (by omega))
  have hqj : Q b (t - 1) * layer L n .J b tail 1 ≤ layer L n .H b tail t := by
    apply le_inf
    · exact (mul_le_mul' hq inf_le_left).trans (hseq.cross_products hn).1
    · exact (filtration_products L _ _ inf_le_left inf_le_right).trans
        (L.endFiltration_antitone (by omega))
  have heq : Q b t = Q b 1 * Q b (t - 1) := by
    rw [centralizer_mul L b hseq.parameter.inverse, show (1 : ℤ) + (t - 1) = t by omega]
  rw [heq, mul_assoc]
  exact mul_le_mul_right hqj _

set_option maxHeartbeats 450000 in
/-- Both products of the first J layer with the H layer at depth `t ≥ 2`
lie in `𝔔_β 𝔥^t`. The cutoff argument extends the J-layer estimate of BK93 (8.2.28). -/
theorem Sequence.jOne_mul_hLayer_le {b : A} {tail : List A} (hseq : Sequence L n b tail)
    (hn : 0 < n) (t : ℤ) (ht : 2 ≤ t) :
    layer L n .J b tail 1 * layer L n .H b tail t ≤ Q b 1 * layer L n .H b tail t ∧
      layer L n .H b tail t * layer L n .J b tail 1 ≤ Q b 1 * layer L n .H b tail t := by
  induction hseq generalizing t with
  | terminal hb hcrit =>
    rename_i b
    have hs := Sequence.terminal hb hcrit
    have hhigh (k : ℤ) (hk : cutoff .H n ≤ k) :
        layer L n .J b [] 1 * layer L n .H b [] k ≤ Q b 1 * layer L n .H b [] k ∧
          layer L n .H b [] k * layer L n .J b [] 1 ≤ Q b 1 * layer L n .H b [] k := by
      rw [layer_nil_high .H b hk]
      refine ⟨?_, ?_⟩
      · exact (filtration_products L _ _ inf_le_right le_rfl).trans
          (by simpa only [add_comm 1 k] using endFiltration_succ_le_centralizer_mul hb k)
      · exact (filtration_products L _ _ le_rfl inf_le_right).trans
          (endFiltration_succ_le_centralizer_mul hb k)
    by_cases hth : cutoff .H n ≤ t
    · exact hhigh t hth
    · have hY := hhigh (cutoff .H n) le_rfl
      rw [layer_nil_high .H b le_rfl] at hY
      have hq := centralizer_mul_firstJ_le hs hn ht
      have hlow := layer_nil_eq (L := L) (n := n) .H b (t := t) (by omega) (by omega)
      rw [hlow, Submodule.mul_sup] at hq
      rw [hlow]
      rw [Submodule.mul_sup, Submodule.sup_mul, Submodule.mul_sup]
      have hcomm := (hs.properties hn .J).fractional 1 (by omega) t
      exact ⟨sup_le (hcomm ▸ hq) (hY.1.trans le_sup_right),
        sup_le hq (hY.2.trans le_sup_right)⟩
  | step hb hr hrn hcrit hc hsub next ih =>
    rename_i b c ds r
    let hs := Sequence.step hb hr hrn hcrit hc hsub next
    have hj : 1 ≤ cutoff .J r := by
      simp only [cutoff, simpleJCutoff]
      omega
    have hhigh (k : ℤ) (hk : cutoff .H r ≤ k) (hk' : 2 ≤ k) :
        layer L n .J b (c :: ds) 1 * layer L n .H b (c :: ds) k ≤
            Q b 1 * layer L n .H b (c :: ds) k ∧
          layer L n .H b (c :: ds) k * layer L n .J b (c :: ds) 1 ≤
            Q b 1 * layer L n .H b (c :: ds) k := by
      have hle : layer L n .J c ds (cutoff .J r) ≤ layer L n .J c ds 1 :=
        inf_le_inf_left _ (L.endFiltration_antitone hj)
      have hprod := transfer_products L hb next.parameter hsub
        ((next.properties hn .H).adjoint r hr.le hc.le k hk) 1
      rw [hs.high_eq hn hcrit .H hk, layer_cons_low (n := n) (c := c) (tail := ds) .J hcrit (by omega) hj,
        Submodule.sup_mul, Submodule.mul_sup]
      refine ⟨sup_le le_rfl ?_, sup_le ?_ ?_⟩
      · rw [hprod.1]
        have hrec := ih k hk'
        exact (mul_le_mul_left hle (layer L n .H c ds k)).trans hrec.1
      · rw [hprod.2, hprod.1, (next.properties hn .H).fractional k (by omega) 1]
      · rw [hprod.1]
        exact (mul_le_mul_right hle (layer L n .H c ds k)).trans (ih k hk').2
    by_cases hth : cutoff .H r ≤ t
    · exact hhigh t hth ht
    · have hY := hhigh (cutoff .H r) le_rfl (by omega)
      rw [hs.high_eq hn hcrit .H (k := cutoff .H r) le_rfl] at hY
      have hq := centralizer_mul_firstJ_le hs hn ht
      have hlow := layer_cons_low (n := n) (c := c) (tail := ds) .H hcrit
        (t := t) (by omega) (by omega)
      rw [hlow, Submodule.mul_sup] at hq
      rw [hlow]
      rw [Submodule.mul_sup, Submodule.sup_mul, Submodule.mul_sup]
      have hcomm := (hs.properties hn .J).fractional 1 (by omega) t
      exact ⟨sup_le (hcomm ▸ hq) (hY.1.trans le_sup_right),
        sup_le hq (hY.2.trans le_sup_right)⟩

/-- The H layer square estimate and the two mixed estimates with the first J layer. -/
def HLayerProductsStatement : Prop :=
  ∀ {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
    {L : LatticeChain 𝒪[F] F V} {n : ℤ} {b : Module.End F V} {tail : List (Module.End F V)},
    Sequence L n b tail → 0 < n →
    (∀ t : ℤ, 1 ≤ t →
      layer L n .H b tail t * layer L n .H b tail t ≤
        centralizerLattice L b 1 * layer L n .H b tail t) ∧
    (∀ t : ℤ, 2 ≤ t →
      layer L n .J b tail 1 * layer L n .H b tail t ≤
        centralizerLattice L b 1 * layer L n .H b tail t ∧
      layer L n .H b tail t * layer L n .J b tail 1 ≤
        centralizerLattice L b 1 * layer L n .H b tail t)

theorem hLayerProducts : HLayerProductsStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ L n b tail hseq hn
  exact ⟨hseq.layer_mul_layer_le hn, hseq.jOne_mul_hLayer_le hn⟩

end Langlands.BushnellKutzko.SimpleStratumLattice
