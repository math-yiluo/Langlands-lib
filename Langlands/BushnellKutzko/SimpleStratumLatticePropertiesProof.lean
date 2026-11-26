import Langlands.BushnellKutzko.SimpleStratumLatticeInduction

/-! # Lattice properties of a simple stratum (BK93 (3.1.9)–(3.1.13)) -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

open SimpleStratumLattice

section LocalField

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (L : LatticeChain 𝒪[F] F V)

local notation "A" => Module.End F V
local notation "P" => L.endFiltration
local notation "Q" => centralizerLattice L
local notation "crit" => criticalExponent L

private theorem isLattice_of_between {X : Submodule 𝒪[F] A} {n : ℤ}
    (hfull : P n ≤ X) (hX : X ≤ P 0) : X.IsLattice F := by
  constructor
  · let : Module.Finite 𝒪[F] (P 0) := Module.Finite.iff_fg.mpr L.endFiltration_zero_fg
    exact Submodule.FG.of_le_of_isNoetherian hX
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    apply top_unique
    intro x _
    obtain ⟨t, ht⟩ := L.exists_uniformizer_pow_mem_endFiltration hπ x n
    have hmem := Submodule.subset_span (R := F) (hfull ht)
    have hπ₀ : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    have hsmul := (Submodule.span F (X : Set A)).smul_mem ((π : F) ^ t)⁻¹ hmem
    rwa [inv_smul_smul₀ (pow_ne_zero _ hπ₀)] at hsmul

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem subalgebra_of_mult {X : Submodule 𝒪[F] A} (h₁ : (1 : A) ∈ X)
    (hX : X * X ≤ X) : ∃ R : Subalgebra 𝒪[F] A, R.toSubmodule = X := by
  let hm : ∀ x y, x ∈ X → y ∈ X → x * y ∈ X := fun _ _ hx hy => hX (Submodule.mul_mem_mul hx hy)
  exact ⟨X.toSubalgebra h₁ hm, X.toSubalgebra_toSubmodule h₁ hm⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem bimodule_inf_filtration {R X : Submodule 𝒪[F] A} (hR : R ≤ P 0)
    (h : Bimodule R X) (k : ℤ) : Bimodule R (X ⊓ P k) := by
  refine ⟨le_inf ((mul_le_mul_right inf_le_left R).trans h.1) ?_,
    le_inf ((mul_le_mul_left inf_le_left R).trans h.2) ?_⟩
  · simpa only [zero_add] using filtration_products L _ _ hR (inf_le_right : X ⊓ P k ≤ P k)
  · simpa only [add_zero] using filtration_products L _ _ (inf_le_right : X ⊓ P k ≤ P k) hR

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem criticalExponent_lt_of_depth_lt {b : A} {t : ℤ}
    (ht : (t : WithTop ℤ) < simpleCriticalDepth L b) : crit b < ((-t : ℤ) : WithBot ℤ) := by
  cases h : crit b using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe j =>
    have hEq := simpleCriticalDepth_eq L (r := -j) (by rwa [neg_neg])
    rw [hEq, WithTop.coe_lt_coe] at ht
    rw [WithBot.coe_lt_coe]
    omega

private theorem criticalExponent_on_order {S : Stratum 𝒪[F] F V}
    (h : S.chain.order = L.order) : criticalExponent S.chain S.b = crit S.b :=
  StratumEquivalence.criticalExponent_congr (StratumEquivalence.endFiltration_eq_of_eq
    (show S.chain.endFiltration 0 = P 0 from congrArg Subalgebra.toSubmodule h)) S.b

end LocalField

/-- Bushnell–Kutzko (3.1.9)–(3.1.13), for the lattices computed from defining sequences. -/
theorem simpleStratumLatticeProperties : SimpleStratumLatticePropertiesStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ S hzero hS q
  dsimp only
  let L := S.chain
  let n := S.n
  let b := S.b
  let A := Module.End F V
  let P := L.endFiltration
  let Q := centralizerLattice L b
  let X := lattice L n
  let Xk := layer L n
  have hn : 0 < n := by simpa only [n, ← hzero] using S.r_lt_n
  have hcrit : criticalExponent L b < (0 : WithBot ℤ) := by simpa only [hzero, neg_zero, WithBot.coe_zero] using hS.2
  have hseq : Sequence L n b q.tail := sequence_of_choice L q rfl hcrit
  have hp (i : Kind) := hseq.properties hn i
  have hQ (i : Kind) : Q 0 ≤ X i b q.tail := centralizer_le_lattice L i b q.tail
  have h₁ (i : Kind) : (1 : A) ∈ X i b q.tail := hQ i (one_mem_centralizer L b)
  have hJ : X .H b q.tail ≤ X .J b q.tail := lattice_H_le_J L n b q.tail
  have hI (i : Kind) (k : ℤ) : Bimodule (X i b q.tail) (Xk i b q.tail k) :=
    bimodule_inf_filtration L (hp i).integral ⟨(hp i).mul, (hp i).mul⟩ k
  have hprod := hseq.cross_products hn
  have hJJ {k l : ℤ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
      Xk .J b q.tail k * Xk .J b q.tail l ≤ Xk .H b q.tail (k + l) :=
    le_inf ((mul_le_mul' (inf_le_inf_left _ (L.endFiltration_antitone hk))
      (inf_le_inf_left _ (L.endFiltration_antitone hl))).trans hprod.2)
      (filtration_products L _ _ inf_le_right inf_le_right)
  have high {T : Stratum 𝒪[F] F V} (ho : T.chain.order = L.order) (hTn : T.n = n)
      (hT : T.IsSimple) (ht : criticalExponent L b < ((-T.r : ℤ) : WithBot ℤ)) (hsub : T.b - b ∈ P (-T.r))
      (q' : T.DefiningSequenceChoice) :
      ∀ i k, 0 ≤ k → (∀ {r : ℤ}, criticalExponent L b = ((-r : ℤ) : WithBot ℤ) → T.r + cutoff i r - r ≤ k) →
        Xk i T.b q'.tail k = Xk i b q.tail k := by
    have ht' : criticalExponent L T.b < ((-T.r : ℤ) : WithBot ℤ) := (criticalExponent_on_order L ho) ▸ hT.2
    have hparam : Parameter L n T.b := hTn ▸ parameter_of_pure L hT.1 ho
    have heq := criticalExponent_eq_of_equiv L hseq.parameter hparam ht ht' hsub
    have hseq' : Sequence L n T.b q'.tail := hTn ▸ sequence_of_choice L q' ho (heq ▸ hcrit)
    intro i k hk hbound
    exact (hseq.layer_eq_of_equiv hseq' hn i ht heq hsub hk hbound).symm
  refine ⟨?_, ⟨isLattice_of_between L (hp .H).full (hp .H).integral,
    isLattice_of_between L (hp .J).full (hp .J).integral,
    subalgebra_of_mult (h₁ .H) (hp .H).mul, subalgebra_of_mult (h₁ .J) (hp .J).mul,
    hQ .H, hJ, (hp .J).integral, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro q'
    have hseq' : Sequence L n b q'.tail := sequence_of_choice L q' rfl hcrit
    have heq (i : Kind) : X i b q.tail = X i b q'.tail := by
      have heq := hseq.layer_eq_of_equiv hseq' hn i (t := 0) (k := 0)
        (by simpa only [neg_zero, WithBot.coe_zero] using hcrit) rfl
        (by rw [sub_self]; exact zero_mem _) le_rfl (fun {r} hr => ?_)
      · simpa only [layer, inf_eq_left.mpr (hp i).integral,
          inf_eq_left.mpr (hseq'.properties hn i).integral] using heq
      · have hr₀ : 0 < r := by
          have hh := hcrit
          rw [hr, ← WithBot.coe_zero, WithBot.coe_lt_coe] at hh
          omega
        have := cutoff_le i hr₀
        omega
    exact ⟨heq .H, heq .J⟩
  · intro k
    exact ⟨⟨inf_le_left, (hI .H k).1, (hI .H k).2⟩,
      ⟨inf_le_left, (hI .J k).1, (hI .J k).2⟩, inf_le_inf_right _ hJ⟩
  · intro T hT q'
    obtain ⟨ho, hTn, hT, hr, hsub⟩ := hT
    change T.n = n at hTn
    change criticalExponent L b = _ at hr
    have hr₀ : 0 < T.r := by
      rw [hr, ← WithBot.coe_zero, WithBot.coe_lt_coe] at hcrit
      omega
    have hc : criticalExponent L T.b < ((-T.r : ℤ) : WithBot ℤ) := (criticalExponent_on_order L ho) ▸ hT.2
    have hseq' : Sequence L n T.b q'.tail := hTn ▸ sequence_of_choice L q' ho
      (hc.trans (WithBot.coe_lt_coe.mpr (neg_neg_of_pos hr₀)))
    have hrn : T.r < n := hTn ▸ T.r_lt_n
    have hr' : finiteCriticalDepth L n b = T.r := by simp [finiteCriticalDepth, simpleCriticalDepth_eq L hr]
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · exact hseq.approximation_eq hseq' hn .H hrn hr hc hsub (by rwa [← hr'])
    · exact hseq.approximation_eq hseq' hn .J hrn hr hc hsub (by rwa [← hr'])
  · intro k
    have hk : 0 ≤ (k : ℤ) := Int.natCast_nonneg k
    refine ⟨fun m => ⟨(hp .H).fractional k hk m, (hp .J).fractional k hk m⟩, fun g hg x => ?_⟩
    have hright (i : Kind) : Xk i b q.tail k * Q 0 ≤ Xk i b q.tail k :=
      (mul_le_mul_right (hQ i) _).trans (hI i k).2
    exact ⟨conjugate_mem_iff L ((hp .H).fractional k hk) (hright .H) hg x,
      conjugate_mem_iff L ((hp .J).fractional k hk) (hright .J) hg x⟩
  · intro k
    change Q 1 * Xk .J b q.tail k ≤ Xk .H b q.tail ((k + 1 : ℕ) : ℤ)
    push_cast
    apply le_inf ((mul_le_mul_right inf_le_left _).trans hprod.1)
    change Q 1 * Xk .J b q.tail k ≤ P ((k : ℤ) + 1)
    rw [add_comm (k : ℤ) 1]
    exact filtration_products L _ _ (inf_le_left : Q 1 ≤ P 1) (inf_le_right : Xk .J b q.tail k ≤ P k)
  · intro k l hk hl
    change Xk .J b q.tail k * Xk .J b q.tail l ≤ Xk .H b q.tail ((k + l : ℕ) : ℤ)
    push_cast
    exact hJJ (by exact_mod_cast hk) (by exact_mod_cast hl)
  · intro k hk
    have hk' : 1 ≤ (k : ℤ) := by exact_mod_cast hk
    have hle : Xk .H b q.tail k ≤ Xk .J b q.tail 1 :=
      inf_le_inf hJ (L.endFiltration_antitone hk')
    have hs : X .J b q.tail = Q 0 ⊔ Xk .J b q.tail 1 :=
      hseq.lattice_eq_sup_layer_one hn .J
    have hact : Bimodule (X .J b q.tail) (X .H b q.tail ⊓ P k) := by
      have hq₁ := (mul_le_mul_left (hQ .H) _).trans (hI .H k).1
      have hq₂ := (mul_le_mul_right (hQ .H) _).trans (hI .H k).2
      have hcross : Xk .J b q.tail 1 * Xk .J b q.tail 1 ≤ X .H b q.tail := hprod.2
      refine ⟨?_, ?_⟩
      · apply le_inf ?_ (by simpa only [zero_add] using
          (filtration_products L _ _ (hp .J).integral (inf_le_right : Xk .H b q.tail k ≤ P k)))
        rw [hs, Submodule.sup_mul]
        exact sup_le (hq₁.trans inf_le_left) ((mul_le_mul_right hle _).trans hcross)
      · apply le_inf ?_ (by simpa only [add_zero] using
          (filtration_products L _ _ (inf_le_right : Xk .H b q.tail k ≤ P k) (hp .J).integral))
        rw [hs, Submodule.mul_sup]
        exact sup_le (hq₂.trans inf_le_left) ((mul_le_mul_left hle _).trans hcross)
    exact ⟨inf_le_left.trans hJ, hact.1, hact.2⟩
  · intro T ho hTn hT ht hsub q'
    have ht' := criticalExponent_lt_of_depth_lt L ht
    refine ⟨fun k hk => high ho hTn hT ht' hsub q' .H k (Int.natCast_nonneg k) ?_,
      fun k hk => high ho hTn hT ht' hsub q' .J k (Int.natCast_nonneg k) ?_⟩
    · intro r hr
      have hd : simpleCriticalDepth S.chain S.b = (r : WithTop ℤ) := simpleCriticalDepth_eq L hr
      simp only [hd, WithTop.coe_ne_top, ↓reduceIte, finiteCriticalDepth, WithTop.untopD_coe] at hk
      have h := (le_max_right 0 (T.r + 1 - simpleJCutoff r)).trans hk
      simp only [cutoff, simpleHCutoff, simpleJCutoff] at h ⊢
      omega
    · intro r hr
      have hd : simpleCriticalDepth S.chain S.b = (r : WithTop ℤ) := simpleCriticalDepth_eq L hr
      simp only [hd, WithTop.coe_ne_top, ↓reduceIte, finiteCriticalDepth, WithTop.untopD_coe] at hk
      have h := (le_max_right 0 (T.r - r / 2)).trans hk
      simp only [cutoff, simpleJCutoff]
      omega

end Langlands.BushnellKutzko
