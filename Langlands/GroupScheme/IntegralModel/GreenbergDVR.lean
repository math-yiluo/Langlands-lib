import Langlands.GroupScheme.IntegralModel.GreenbergRing
import Langlands.GroupScheme.IntegralModel.GreenbergMixed.RingScheme

/-! # Greenberg ring schemes of a mixed-characteristic DVR

Let `R` be a discrete valuation ring whose residue field `k` is algebraically closed and
whose characteristic differs from that of `k`, and let `n` be a positive level. The
congruence ring `A = R ⧸ 𝔪ⁿ` receives the Witt-vector ring map `W(k) → A`, is generated as
a `W(k)`-module by the powers of a uniformizer and is killed by `pⁿ`; it therefore has
cyclic Witt coordinates, and the associated Greenberg ring functor is a Greenberg
coefficient ring scheme of level `n`.
-/

set_option maxSynthPendingDepth 2

noncomputable section

universe u

open CategoryTheory WittVector IsLocalRing

namespace Langlands.GroupScheme.IntegralModel.Greenberg

/-- Digit expansion: if `a - d a = π * f a` for all `a`, then every `a` is the sum of the
first `j` digits `d (f^[i] a)` weighted by `π ^ i`, plus `π ^ j` times a remainder. -/
theorem eq_sum_iterate {A : Type*} [CommRing A] (f d : A → A) (π : A)
    (h : ∀ a, a - d a = π * f a) (j : ℕ) (a : A) :
    a = ∑ i ∈ Finset.range j, d (f^[i] a) * π ^ i + π ^ j * f^[j] a := by
  induction j generalizing a with
  | zero => simp
  | succ j ih =>
    have hS : ∑ i ∈ Finset.range j, d (f^[i + 1] a) * π ^ (i + 1) =
        (∑ i ∈ Finset.range j, d (f^[i] (f a)) * π ^ i) * π := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Function.iterate_succ_apply, pow_succ, mul_assoc]
    rw [Finset.sum_range_succ', hS, Function.iterate_succ_apply, Function.iterate_zero_apply,
      pow_zero, mul_one, pow_succ]
    linear_combination h a + π * ih (f a)

section DVR

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The residue map of the level-`n` congruence ring `R ⧸ 𝔪ⁿ`. -/
def levelResidue (n : ℕ+) : congruenceRing R n →+* ResidueField R :=
  Ideal.Quotient.lift _ (residue R) fun a ha => by
    rw [residue_eq_zero_iff]
    exact Ideal.pow_le_self n.ne_zero ha

theorem levelResidue_mk (n : ℕ+) (a : R) :
    levelResidue R n (Ideal.Quotient.mk _ a) = residue R a :=
  Ideal.Quotient.lift_mk _ _ _

theorem levelResidue_surjective (n : ℕ+) : Function.Surjective (levelResidue R n) := by
  intro x
  obtain ⟨a, rfl⟩ := residue_surjective x
  exact ⟨Ideal.Quotient.mk _ a, levelResidue_mk R n a⟩

/-- The kernel of the residue map of `R ⧸ 𝔪ⁿ` is nilpotent of order `n`. -/
theorem ker_levelResidue_pow (n : ℕ+) :
    RingHom.ker (levelResidue R n) ^ ((n : ℕ) - 1 + 1) = ⊥ := by
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 n.ne_zero), ← le_bot_iff]
  have hle : RingHom.ker (levelResidue R n) ≤
      Ideal.map (Ideal.Quotient.mk ((maximalIdeal R) ^ (n : ℕ))) (maximalIdeal R) := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, levelResidue_mk, residue_eq_zero_iff] at hx
    exact Ideal.mem_map_of_mem _ hx
  refine (Ideal.pow_right_mono hle _).trans (le_of_eq ?_)
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

variable {R}

theorem exists_eq_mul_of_levelResidue_eq_zero (n : ℕ+) {ϖ : R} (hϖ : Irreducible ϖ)
    {x : congruenceRing R n} (hx : levelResidue R n x = 0) :
    ∃ y, x = Ideal.Quotient.mk _ ϖ * y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [levelResidue_mk, residue_eq_zero_iff,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    Ideal.mem_span_singleton'] at hx
  obtain ⟨b, rfl⟩ := hx
  exact ⟨Ideal.Quotient.mk _ b, by rw [map_mul, mul_comm]⟩

theorem mk_pow_eq_zero (n : ℕ+) {a : R} (ha : a ∈ maximalIdeal R) :
    (Ideal.Quotient.mk ((maximalIdeal R) ^ (n : ℕ)) a) ^ (n : ℕ) = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow ha _

theorem natCast_pow_eq_zero (n : ℕ+) (p : ℕ) [CharP (ResidueField R) p] :
    (p : congruenceRing R n) ^ (n : ℕ) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk ((maximalIdeal R) ^ (n : ℕ))) p]
  refine mk_pow_eq_zero n ?_
  rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]

variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p] [PerfectRing (ResidueField R) p]

omit [CharP (ResidueField R) p] [PerfectRing (ResidueField R) p] in
/-- The congruence ring is generated over `W(k)` by the powers of a uniformizer. -/
theorem exists_eq_sum_witt (n : ℕ+) {ϖ : R} (hϖ : Irreducible ϖ)
    (ψ : WittVector p (ResidueField R) →+* congruenceRing R n)
    (hψ : ∀ c, levelResidue R n (ψ c) = c.coeff 0) (a : congruenceRing R n) :
    ∃ c : Fin n → WittVector p (ResidueField R),
      a = ∑ i, ψ (c i) * (Ideal.Quotient.mk _ ϖ) ^ (i : ℕ) := by
  have hd : ∀ b : congruenceRing R n,
      levelResidue R n (b - ψ (teichmuller p (levelResidue R n b))) = 0 := fun b => by
    rw [map_sub, hψ, teichmuller_coeff_zero, sub_self]
  choose f hf using fun b => exists_eq_mul_of_levelResidue_eq_zero n hϖ (hd b)
  have key := eq_sum_iterate f (fun b => ψ (teichmuller p (levelResidue R n b)))
    (Ideal.Quotient.mk _ ϖ) hf n a
  rw [mk_pow_eq_zero n (by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
    exact Ideal.mem_span_singleton_self ϖ), zero_mul, add_zero,
    Finset.sum_range (fun i => ψ (teichmuller p (levelResidue R n (f^[i] a))) *
      Ideal.Quotient.mk _ ϖ ^ i)] at key
  exact ⟨fun i => teichmuller p (levelResidue R n (f^[i] a)), key⟩

/-- Cyclic Witt coordinates of the congruence ring `R ⧸ 𝔪ⁿ`. -/
theorem nonempty_wittDecomposition_congruenceRing (n : ℕ+)
    (ψ : WittVector p (ResidueField R) →+* congruenceRing R n)
    (hψ : ∀ c, levelResidue R n (ψ c) = c.coeff 0) : Nonempty (WittDecomposition p ψ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact nonempty_wittDecomposition p ψ (fun i : Fin n => (Ideal.Quotient.mk _ ϖ) ^ (i : ℕ))
    (exists_eq_sum_witt p n hϖ ψ hψ) n (natCast_pow_eq_zero n p)

local notation "κ" => CommRingCat.of (ResidueField R)

variable {p}

/-- **The Greenberg ring scheme** attached to cyclic Witt coordinates of `R ⧸ 𝔪ⁿ`. -/
def greenbergRingScheme (n : ℕ+) {ψ : WittVector p (ResidueField R) →+* congruenceRing R n}
    (D : WittDecomposition p ψ) (hψ : ∀ c, levelResidue R n (ψ c) = c.coeff 0) :
    GreenbergMixed.GreenbergRingScheme R n where
  functor :=
    { obj := fun B => CommAlgCat.of (CommRingCat.of R) (GreenbergRing D B)
      map := fun f => CommAlgCat.ofHom (gmap D R f.hom)
      map_id := fun B => CommAlgCat.hom_ext (gmap_id D R)
      map_comp := fun f g => CommAlgCat.hom_ext (gmap_comp D R f.hom g.hom) }
  dim := Fintype.card (Σ i : D.ι, Fin (D.m i))
  coord B := (coordEquiv D B).trans
    (Equiv.arrowCongr (Fintype.equivFin (Σ i : D.ι, Fin (D.m i))) (Equiv.refl B))
  coord_map f x j := coordEquiv_gmap D R f.hom x _
  levelEquiv := levelEquiv D R
  red B := red D B (levelResidue R n) hψ
  red_coord := ⟨fun j => if (((Fintype.equivFin (Σ i : D.ι, Fin (D.m i))).symm j).2 : ℕ) = 0
      then levelResidue R n (D.e ((Fintype.equivFin (Σ i : D.ι, Fin (D.m i))).symm j).1)
      else 0, fun B x => by
    refine (red_eq_sum D B (levelResidue R n) hψ x).trans ?_
    exact (Equiv.sum_comp (Fintype.equivFin (Σ i : D.ι, Fin (D.m i))).symm _).symm⟩
  red_algebraMap B c := by
    refine (red_algebraMap D B (levelResidue R n) hψ R c).trans ?_
    rw [Ideal.Quotient.algebraMap_eq, levelResidue_mk]
  ker_red_nilpotent B :=
    ⟨_, (ker_red_pow D B (levelResidue R n) hψ _ (ker_levelResidue_pow R n)).trans
      Ideal.zero_eq_bot.symm⟩
  ker_map_nilpotent B I hI := by
    have hf : ∀ a ∈ RingHom.ker (Ideal.Quotient.mkₐ κ I),
        ∀ b ∈ RingHom.ker (Ideal.Quotient.mkₐ κ I), a * b = 0 := by
      intro a ha b hb
      rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at ha hb
      have := Ideal.mul_mem_mul ha hb
      rw [← sq, hI] at this
      exact (Ideal.mem_bot).1 this
    exact ⟨_, (ker_gmap_pow D R (levelResidue R n) (Ideal.Quotient.mkₐ κ I) hf _
      (ker_levelResidue_pow R n)).trans Ideal.zero_eq_bot.symm⟩

end DVR

/-- **Existence of Greenberg ring schemes (KP A.4.19, mixed characteristic).** A discrete
valuation ring with algebraically closed residue field of a different characteristic has a
Greenberg coefficient ring scheme at every positive level. -/
theorem nonempty_greenbergRingScheme (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAlgClosed (ResidueField R)]
    (hchar : ringChar R ≠ ringChar (ResidueField R)) (n : ℕ+) :
    Nonempty (GreenbergMixed.GreenbergRingScheme R n) := by
  obtain ⟨p, hp⟩ : ∃ p, ringChar (ResidueField R) = p := ⟨_, rfl⟩
  have : CharP (ResidueField R) p := ringChar.of_eq hp
  have hprime : p.Prime := by
    refine (CharP.char_is_prime_or_zero (ResidueField R) p).resolve_right fun h0 => hchar ?_
    subst h0
    have : CharZero (ResidueField R) := CharP.charP_to_charZero (ResidueField R)
    have : CharZero R := RingHom.charZero (residue R)
    rw [ringChar.eq_zero, hp]
  have : Fact p.Prime := ⟨hprime⟩
  let r := levelResidue R n
  let ψ := wittToLocal p r (levelResidue_surjective R n) _ (ker_levelResidue_pow R n)
  have hψ : ∀ c, r (ψ c) = c.coeff 0 :=
    residue_wittToLocal p r (levelResidue_surjective R n) _ (ker_levelResidue_pow R n)
  obtain ⟨D⟩ := nonempty_wittDecomposition_congruenceRing p n ψ hψ
  exact ⟨greenbergRingScheme n D hψ⟩

end Langlands.GroupScheme.IntegralModel.Greenberg
