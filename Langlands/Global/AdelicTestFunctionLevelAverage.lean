import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.AdelicRightConvolutionDifferentiation
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Averaging adelic test functions over a compact open level by finite coset sums

For subgroups `L`, `L'` of `G(𝔸_f)`, the average `h_L(g) = [L : L ∩ L']⁻¹ ∑_c h(l_c⁻¹ g)` runs
over the left cosets `c` of `L ∩ L'` in `L` (written `L / L'` when `L' ≤ L`), with chosen
representatives `l_c`; it is the zero function when there are infinitely many cosets. If `h`
is left invariant under `L'`, then `h_L` is left invariant under `L`. If moreover `L` is open,
there are finitely many cosets and `h` is a test function, then `h_L` is a test function.
For a continuous compactly supported `h`, finitely many cosets and a locally integrable `f`,
right convolution by `h_L` is the average over `c` of the right translates by `l_c` of the
right convolution by `h`. Consequently, if `f` is moreover right `L`-invariant, a
Harish-Chandra equation `∑ₖ bₖ δ(hₖ) f = c f` stays true when every `hₖ` is replaced by its
average.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left]

local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G

/-- The coset space `L / (L ∩ L')` for subgroups `L'`, `L` of the finite adelic points (the
quotient of `L` by `L'.subgroupOf L`), written `L / L'` when `L' ≤ L`. -/
abbrev LevelCosets (L L' : Subgroup Gf) := L ⧸ L'.subgroupOf L

/-- The average of `h` over the left cosets of `L ∩ L'` in `L`:
`g ↦ [L : L ∩ L']⁻¹ ∑ᶠ_c h(l_c⁻¹ g)`, with `l_c` the chosen representative of `c`. The index is
`Nat.card`, so for infinitely many cosets the function is zero. -/
def levelAverage (L L' : Subgroup Gf) (h : A → ℂ) (g : A) : ℂ :=
  (Nat.card (LevelCosets L L') : ℂ)⁻¹ *
    ∑ᶠ c : LevelCosets L L', h (ofFinite F G ((c.out : L) : Gf)⁻¹ * g)

/-- An open subgroup of a compact subgroup has finitely many cosets. -/
theorem finite_levelCosets {L L' : Subgroup Gf} (hLc : IsCompact (L : Set Gf))
    (hL'o : IsOpen (L' : Set Gf)) : Finite (LevelCosets L L') := by
  have : CompactSpace L := isCompact_iff_compactSpace.mp hLc
  exact Subgroup.quotient_finite_of_isOpen (L'.subgroupOf L)
    (hL'o.preimage continuous_subtype_val)

/-- Two representatives of the same coset give the same translate of a left `L'`-invariant
function. -/
theorem translate_eq_of_mk_eq {L L' : Subgroup Gf} {h : A → ℂ}
    (hh : ∀ k ∈ L', ∀ g, h (ofFinite F G k * g) = h g) {a b : L}
    (hab : (QuotientGroup.mk a : LevelCosets L L') = QuotientGroup.mk b) (g : A) :
    h (ofFinite F G (a : Gf)⁻¹ * g) = h (ofFinite F G (b : Gf)⁻¹ * g) := by
  have hk : ((a⁻¹ * b : L) : Gf) ∈ L' :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq (s := L'.subgroupOf L)).mp hab)
  have hsplit : (a : Gf)⁻¹ = ((a⁻¹ * b : L) : Gf) * (b : Gf)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel, mul_one]
  rw [hsplit, map_mul, mul_assoc, hh _ hk]

/-- The level average is left invariant under `L`. -/
theorem levelAverage_mul_left {L L' : Subgroup Gf} {h : A → ℂ}
    (hh : ∀ k ∈ L', ∀ g, h (ofFinite F G k * g) = h g) {l : Gf} (hl : l ∈ L) (g : A) :
    levelAverage L L' h (ofFinite F G l * g) = levelAverage L L' h g := by
  unfold levelAverage
  congr 1
  let l' : L := ⟨l, hl⟩
  have hterm (c : LevelCosets L L') :
      h (ofFinite F G ((c.out : L) : Gf)⁻¹ * (ofFinite F G l * g)) =
        h (ofFinite F G (((l'⁻¹ • c).out : L) : Gf)⁻¹ * g) := by
    have hmk : (QuotientGroup.mk ((l'⁻¹ • c).out) : LevelCosets L L') =
        QuotientGroup.mk (l'⁻¹ * c.out) := by
      rw [QuotientGroup.out_eq']
      conv_lhs => rw [← QuotientGroup.out_eq' c]
      rfl
    rw [translate_eq_of_mk_eq hh hmk g]
    simp only [l', Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, map_mul, mul_assoc]
  simp_rw [hterm]
  exact finsum_comp_equiv (MulAction.toPerm (l'⁻¹ : L))
    (f := fun c : LevelCosets L L' => h (ofFinite F G ((c.out : L) : Gf)⁻¹ * g))

theorem levelAverage_eq_sum {L L' : Subgroup Gf} [Fintype (LevelCosets L L')] (h : A → ℂ) (g : A) :
    levelAverage L L' h g = (Nat.card (LevelCosets L L') : ℂ)⁻¹ *
      ∑ c : LevelCosets L L', h (ofFinite F G ((c.out : L) : Gf)⁻¹ * g) := by
  rw [levelAverage, finsum_eq_sum_of_fintype]

/-- For an open subgroup `L` with finitely many cosets of `L ∩ L'` and a test function `h` that is
left invariant under `L'`, the level average is a test function, left invariant under `L`. -/
theorem isAdelicTestFunction_levelAverage {L L' : Subgroup Gf} [Finite (LevelCosets L L')]
    (hLo : IsOpen (L : Set Gf)) {h : A → ℂ} (hh : IsAdelicTestFunction F G h)
    (hL' : ∀ k ∈ L', ∀ g, h (ofFinite F G k * g) = h g) :
    IsAdelicTestFunction F G (levelAverage L L' h) := by
  have := Fintype.ofFinite (LevelCosets L L')
  obtain ⟨⟨hcont, hslice, R, hRo, hR⟩, hcpt, -⟩ := hh
  have heq : levelAverage L L' h = fun g => (Nat.card (LevelCosets L L') : ℂ)⁻¹ *
      ∑ c : LevelCosets L L', h (ofFinite F G ((c.out : L) : Gf)⁻¹ * g) :=
    funext (levelAverage_eq_sum h)
  refine ⟨⟨?_, ?_, R, hRo, ?_⟩, ?_, L, hLo, fun l hl g => levelAverage_mul_left hL' hl g⟩
  · rw [heq]
    exact continuous_const.mul (continuous_finsetSum _ fun c _ =>
      hcont.comp (continuous_const.mul continuous_id))
  · intro b
    have hsl : functionInfiniteSlice F G (levelAverage L L' h) b =
        (Nat.card (LevelCosets L L') : ℂ)⁻¹ • ∑ c : LevelCosets L L',
          functionInfiniteSlice F G h (((c.out : L) : Gf)⁻¹ * b) := by
      funext a
      simp only [functionInfiniteSlice, heq, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
        ofFinite_eq_pair, pair_mul, one_mul]
    rw [hsl]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun c _ => hslice _)
  · intro l hl g
    simp only [heq]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_assoc, hR l hl]
  · refine HasCompactSupport.intro (K := ⋃ c : LevelCosets L L',
      (fun g => ofFinite F G ((c.out : L) : Gf) * g) '' tsupport h)
      (isCompact_iUnion fun c => hcpt.image (continuous_const.mul continuous_id)) ?_
    intro x hx
    rw [heq]
    simp only
    rw [Finset.sum_eq_zero, mul_zero]
    intro c _
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hx
    refine Set.mem_iUnion.mpr ⟨c, ofFinite F G ((c.out : L) : Gf)⁻¹ * x, hmem, ?_⟩
    simp only [map_inv, mul_inv_cancel_left]

/-- For finitely many test functions and a compact open subgroup `L`, there is an open
subgroup `L' ≤ L` under which all of them are left invariant; it has finitely many cosets
in `L`. -/
theorem exists_common_level {I : Type*} [Finite I] (h : I → A → ℂ)
    (hh : ∀ k, IsAdelicTestFunction F G (h k)) {L : Subgroup Gf}
    (hLo : IsOpen (L : Set Gf)) (hLc : IsCompact (L : Set Gf)) :
    ∃ L' : Subgroup Gf, L' ≤ L ∧ IsOpen (L' : Set Gf) ∧ Finite (LevelCosets L L') ∧
      ∀ k, ∀ l ∈ L', ∀ g, h k (ofFinite F G l * g) = h k g := by
  choose M hMo hM using fun k => (hh k).2.2
  let L' : Subgroup Gf := L ⊓ ⨅ k, M k
  have hL'o : IsOpen (L' : Set Gf) := by
    have := Fintype.ofFinite I
    refine hLo.inter ?_
    have hc : ((⨅ k, M k : Subgroup Gf) : Set Gf) = ⋂ k, (M k : Set Gf) := Subgroup.coe_iInf
    change IsOpen ((⨅ k, M k : Subgroup Gf) : Set Gf)
    rw [hc]
    exact isOpen_iInter_of_finite hMo
  refine ⟨L', inf_le_left, hL'o, finite_levelCosets hLc hL'o, fun k l hl g => ?_⟩
  exact hM k l (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp hl).2 k) g

variable [LocallyOfFiniteType G.X.hom]

local notation "μG" => (Measure.haar : Measure A)

/-- Right convolution by a left translate is the right translate of the right convolution. -/
theorem rightConvolution_translate (h f : A → ℂ) (l : Gf) (x : A) :
    rightConvolution F G (fun g => h (ofFinite F G l⁻¹ * g)) f x =
      rightConvolution F G h f (x * ofFinite F G l) := by
  unfold rightConvolution
  rw [← integral_mul_left_eq_self («μ» := μG)
    (fun g => h (ofFinite F G l⁻¹ * g) * f (x * g)) (ofFinite F G l)]
  simp only [map_inv, inv_mul_cancel_left, mul_assoc]

/-- Right convolution by the level average is the average of the right translates. -/
theorem rightConvolution_levelAverage {L L' : Subgroup Gf} [Finite (LevelCosets L L')]
    {h f : A → ℂ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hf : LocallyIntegrable f μG) (x : A) :
    rightConvolution F G (levelAverage L L' h) f x =
      (Nat.card (LevelCosets L L') : ℂ)⁻¹ *
        ∑ᶠ c : LevelCosets L L', rightConvolution F G h f (x * ofFinite F G ((c.out : L) : Gf)) := by
  have := Fintype.ofFinite (LevelCosets L L')
  simp only [finsum_eq_sum_of_fintype]
  unfold rightConvolution levelAverage
  simp only [finsum_eq_sum_of_fintype, mul_assoc]
  rw [integral_const_mul]
  congr 1
  simp only [Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun c _ => ?_
    have := rightConvolution_translate h f ((c.out : L) : Gf) x
    unfold rightConvolution at this
    simpa only [mul_assoc] using this
  · intro c _
    have hcont : Continuous fun g => h (ofFinite F G ((c.out : L) : Gf)⁻¹ * g) :=
      hh.comp (continuous_const.mul continuous_id)
    have hsupp : HasCompactSupport fun g => h (ofFinite F G ((c.out : L) : Gf)⁻¹ * g) :=
      hc.comp_homeomorph (Homeomorph.mulLeft _)
    exact integrable_kernel_mul hcont hsupp hf x

/-- On a right `L`-invariant function satisfying a Harish-Chandra equation, replacing each
kernel by its level average preserves the equation. -/
theorem sum_rightConvolution_levelAverage {L L' : Subgroup Gf} [Finite (LevelCosets L L')]
    {I : Type*} (s : Finset I) (h : I → A → ℂ) (b : I → ℂ) (c : ℂ) {f : A → ℂ}
    (hh : ∀ k, Continuous (h k)) (hc : ∀ k, HasCompactSupport (h k))
    (hf : LocallyIntegrable f μG) (hfL : ∀ l ∈ L, ∀ x, f (x * ofFinite F G l) = f x)
    (heq : ∀ x, ∑ k ∈ s, b k * rightConvolution F G (h k) f x = c * f x) (x : A) :
    ∑ k ∈ s, b k * rightConvolution F G (levelAverage L L' (h k)) f x = c * f x := by
  have := Fintype.ofFinite (LevelCosets L L')
  simp only [fun k => rightConvolution_levelAverage (L := L) (L' := L') (hh k) (hc k) hf x,
    finsum_eq_sum_of_fintype]
  have hswap : ∑ k ∈ s, b k * ((Nat.card (LevelCosets L L') : ℂ)⁻¹ *
      ∑ c' : LevelCosets L L', rightConvolution F G (h k) f (x * ofFinite F G ((c'.out : L) : Gf))) =
      (Nat.card (LevelCosets L L') : ℂ)⁻¹ * ∑ c' : LevelCosets L L',
        ∑ k ∈ s, b k * rightConvolution F G (h k) f (x * ofFinite F G ((c'.out : L) : Gf)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hswap]
  simp only [heq, hfL _ (Subtype.prop _)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  have hpos : (Nat.card (LevelCosets L L') : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  field_simp

end Langlands.Global.AdelicGroupPoints
