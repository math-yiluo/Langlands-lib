import Langlands.AbelianScheme.Tate.PrimeAdicFreeness
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Compatible residue coordinates on the actual prime-adic Tate module -/

set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate.PrimeAdic

namespace GeometricRank

variable {S : Scheme.{u}} {G : Grp (Over S)} [IsCommMonObj G.X] {T : Over S}
  {p : ℕ} [Fact p.Prime] {r : ℕ}

/-- The level-`p` torsion points included in level `p ^ (n + 1)`. -/
def levelInclusion (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S) (p n : ℕ) :
    Level G T p →+ Level G T (p ^ (n + 1)) :=
  MonoidHom.toAdditive (Subgroup.inclusion (by
    intro x hx
    rw [mem_levelGroup] at hx ⊢
    rw [pow_succ', pow_mul, hx, one_pow]))

omit [Fact p.Prime] in
lemma levelInclusion_injective (n : ℕ) : Function.Injective (levelInclusion G T p n) := by
  intro x y h
  apply toSection_injective G T p
  exact congrArg (toSection G T (p ^ (n + 1))) h

/-- The kernel of a successive transition is the level-`p` torsion. -/
lemma ker_transition_eq_range (n : ℕ) :
    (transition G T (pow_dvd_pow p (Nat.le_succ n))).ker =
      (levelInclusion G T p n).range := by
  ext x
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  constructor
  · intro hx
    have h := congrArg (toSection G T (p ^ n)) hx
    rw [toSection_transition_succ, map_zero] at h
    refine ⟨Additive.ofMul ⟨(Additive.toMul x).val, ?_⟩, ?_⟩
    · rw [mem_levelGroup]
      exact h
    · rfl
  · rintro ⟨y, rfl⟩
    apply toSection_injective G T (p ^ n)
    rw [toSection_transition_succ, map_zero]
    exact (mem_levelGroup G T p _).mp (Additive.toMul y).property

section Counting

variable (hL : ∀ n : ℕ,
  Nonempty ((Fin r → ZMod (p ^ n)) ≃ₗ[ZMod (p ^ n)] Level G T (p ^ n)) ∧
    Nat.card (Level G T (p ^ n)) = (p ^ n) ^ r)

include hL

lemma finite_level (n : ℕ) : Finite (Level G T (p ^ n)) := by
  apply Nat.finite_of_card_ne_zero
  rw [(hL n).2]
  exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

/-- Counting: the successive transition between levels of rank `r` is surjective. -/
lemma transition_surjective (n : ℕ) :
    Function.Surjective (transition G T (pow_dvd_pow p (Nat.le_succ n))) := by
  have := finite_level hL (n + 1)
  have := finite_level hL n
  set f := transition G T (pow_dvd_pow p (Nat.le_succ n))
  have hker : Nat.card f.ker = p ^ r := by
    have h1 := (hL 1).2
    rw [pow_one] at h1
    rw [ker_transition_eq_range,
      ← Nat.card_congr (AddMonoidHom.ofInjective (levelInclusion_injective (G := G) (T := T)
        (p := p) n)).toEquiv, h1]
  have hrange : Nat.card f.range = Nat.card (Level G T (p ^ n)) := by
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, hker,
      (hL (n + 1)).2] at h1
    rw [(hL n).2]
    have hp : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos r
    apply Nat.eq_of_mul_eq_mul_right hp
    rw [← h1]
    ring
  rw [← AddMonoidHom.range_eq_top, ← AddSubgroup.card_eq_iff_eq_top]
  exact hrange

end Counting

/-- A family of `r` torsion points is a residue basis when its coordinate map is bijective. -/
def IsResidueBasis (n : ℕ) (b : Fin r → Level G T (p ^ n)) : Prop :=
  Function.Bijective (Fintype.linearCombination (ZMod (p ^ n)) b)

/-- Residue bases of the actual level `p ^ n`. -/
def Bases (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S) (p r n : ℕ) : Type u :=
  {b : Fin r → Level G T (p ^ n) // IsResidueBasis n b}

section Bases

variable (hL : ∀ n : ℕ,
  Nonempty ((Fin r → ZMod (p ^ n)) ≃ₗ[ZMod (p ^ n)] Level G T (p ^ n)) ∧
    Nat.card (Level G T (p ^ n)) = (p ^ n) ^ r)

include hL

omit [Fact p.Prime] in
lemma bases_nonempty (n : ℕ) : Nonempty (Bases G T p r n) := by
  obtain ⟨e⟩ := (hL n).1
  let b := (Pi.basisFun (ZMod (p ^ n)) (Fin r)).map e
  refine ⟨⟨b, ?_⟩⟩
  have h : ⇑(Fintype.linearCombination (ZMod (p ^ n)) b) = ⇑b.equivFun.symm := by
    funext a
    rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
  rw [IsResidueBasis, h]
  exact b.equivFun.symm.bijective

lemma bases_finite (n : ℕ) : Finite (Bases G T p r n) := by
  have := finite_level hL n
  exact Subtype.finite

/-- The successive transition carries residue bases to residue bases. -/
lemma isResidueBasis_transition {n : ℕ} {b : Fin r → Level G T (p ^ (n + 1))}
    (hb : IsResidueBasis (n + 1) b) :
    IsResidueBasis n (fun i => transition G T (pow_dvd_pow p (Nat.le_succ n)) (b i)) := by
  have := finite_level hL n
  have hsurj : Function.Surjective (Fintype.linearCombination (ZMod (p ^ n))
      (fun i => transition G T (pow_dvd_pow p (Nat.le_succ n)) (b i))) := by
    intro y
    obtain ⟨x, rfl⟩ := transition_surjective hL n y
    obtain ⟨a, rfl⟩ := hb.2 x
    refine ⟨fun i => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) (a i), ?_⟩
    simp only [Fintype.linearCombination_apply, map_sum, transition_zmod_smul]
  refine hsurj.bijective_of_nat_card_le ?_
  rw [(hL n).2, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

/-- Restriction of residue bases along the successive transition. -/
def restrictBasis (n : ℕ) : Bases G T p r (n + 1) → Bases G T p r n :=
  fun b => ⟨fun i => transition G T (pow_dvd_pow p (Nat.le_succ n)) (b.1 i),
    isResidueBasis_transition hL b.2⟩

/-- The inverse system of finite nonempty sets of residue bases. -/
def basisSystem : ℕᵒᵖ ⥤ Type u :=
  Functor.ofOpSequence (X := fun n => Bases G T p r n) (fun n => ↾(restrictBasis hL n))

/-- Kőnig's lemma gives residue bases at all levels, compatible under the transitions. -/
lemma exists_compatible_bases : ∃ c : ∀ n, Fin r → Level G T (p ^ n),
    (∀ n, IsResidueBasis n (c n)) ∧
      ∀ n i, transition G T (pow_dvd_pow p (Nat.le_succ n)) (c (n + 1) i) = c n i := by
  have : ∀ j : ℕᵒᵖ, Finite ((basisSystem hL).obj j) := fun j => bases_finite hL j.unop
  have : ∀ j : ℕᵒᵖ, Nonempty ((basisSystem hL).obj j) := fun j => bases_nonempty hL j.unop
  obtain ⟨σ, hσ⟩ := nonempty_sections_of_finite_inverse_system (basisSystem hL)
  refine ⟨fun n => (σ (Opposite.op n)).1, fun n => (σ (Opposite.op n)).2, ?_⟩
  intro n i
  have h := hσ (homOfLE (Nat.le_add_right n 1)).op
  rw [show (basisSystem hL).map (homOfLE (Nat.le_add_right n 1)).op = ↾(restrictBasis hL n) from
    Functor.ofOpSequence_map_homOfLE_succ _ n] at h
  exact congrArg (fun b : Bases G T p r n => b.1 i) h

end Bases

/-- A compatible system of `p`-adic digits defines a `p`-adic integer. -/
lemma exists_padicInt (k : ∀ n : ℕ, ZMod (p ^ n))
    (hk : ∀ n, ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) (k (n + 1)) = k n) :
    ∃ a : ℤ_[p], ∀ n, PadicInt.toZModPow n a = k n := by
  have hi : ∀ i, (p : ℤ) ^ i ∣ ((k (i + 1)).val : ℤ) - ((k i).val : ℤ) := by
    intro i
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub ((k i).val : ℤ) ((k (i + 1)).val : ℤ)
      (p ^ i)).mp (by
        rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_val,
          ← ZMod.castHom_apply (h := pow_dvd_pow p (Nat.le_succ i)), hk])
    exact_mod_cast h
  refine ⟨PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun i => ((k i).val : ℤ)) p hi), fun n => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ p hi]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

variable {c : ∀ n, Fin r → Level G T (p ^ n)}

/-- The linear map from `p`-adic coordinates to the actual Tate module. -/
def coordinates
    (hc : ∀ n i, transition G T (pow_dvd_pow p (Nat.le_succ n)) (c (n + 1) i) = c n i) :
    (Fin r → ℤ_[p]) →ₗ[ℤ_[p]] Integral G T p :=
  lift G T p (fun n => Fintype.linearCombination ℤ_[p] (c n)) (by
    intro n a
    simp only [Fintype.linearCombination_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [transition_smul G T p (Nat.le_succ n), hc n i])

lemma evaluation_coordinates
    (hc : ∀ n i, transition G T (pow_dvd_pow p (Nat.le_succ n)) (c (n + 1) i) = c n i)
    (n : ℕ) (a : Fin r → ℤ_[p]) :
    evaluation G T p n (coordinates hc a) =
      Fintype.linearCombination (ZMod (p ^ n)) (c n) (fun i => PadicInt.toZModPow n (a i)) :=
  rfl

lemma coordinates_injective (hb : ∀ n, IsResidueBasis n (c n))
    (hc : ∀ n i, transition G T (pow_dvd_pow p (Nat.le_succ n)) (c (n + 1) i) = c n i) :
    Function.Injective (coordinates hc) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  funext i
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  have h := congrArg (evaluation G T p n) ha
  rw [map_zero, evaluation_coordinates, ← map_zero (Fintype.linearCombination (ZMod (p ^ n)) (c n))]
    at h
  have := congrFun ((hb n).1 h) i
  simpa using this

lemma coordinates_surjective (hb : ∀ n, IsResidueBasis n (c n))
    (hc : ∀ n i, transition G T (pow_dvd_pow p (Nat.le_succ n)) (c (n + 1) i) = c n i) :
    Function.Surjective (coordinates hc) := by
  intro x
  choose k hk using fun n => (hb n).2 (evaluation G T p n x)
  have hcompat : ∀ n,
      (fun i => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) (k (n + 1) i)) =
        k n := by
    intro n
    apply (hb n).1
    rw [hk n, ← evaluation_transition G T p n x, ← hk (n + 1)]
    simp only [Fintype.linearCombination_apply, map_sum, transition_zmod_smul, hc]
  choose a ha using fun i => exists_padicInt (p := p) (fun n => k n i)
    (fun n => congrFun (hcompat n) i)
  refine ⟨a, ?_⟩
  apply Subtype.ext
  funext n
  change evaluation G T p n (coordinates hc a) = evaluation G T p n x
  rw [evaluation_coordinates, ← hk n]
  congr 1
  funext i
  exact ha i n

section Assembly

variable (hL : ∀ n : ℕ,
  Nonempty ((Fin r → ZMod (p ^ n)) ≃ₗ[ZMod (p ^ n)] Level G T (p ^ n)) ∧
    Nat.card (Level G T (p ^ n)) = (p ^ n) ^ r)

include hL in
/-- Free residue levels of rank `r` give a free `p`-adic Tate module of rank `r`. -/
theorem integral_linearEquiv : Nonempty ((Fin r → ℤ_[p]) ≃ₗ[ℤ_[p]] Integral G T p) := by
  obtain ⟨c, hb, hc⟩ := exists_compatible_bases hL
  exact ⟨LinearEquiv.ofBijective (coordinates hc)
    ⟨coordinates_injective hb hc, coordinates_surjective hb hc⟩⟩

end Assembly

end GeometricRank

end Langlands.GroupScheme.Tate.PrimeAdic
