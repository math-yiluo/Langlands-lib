import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Langlands.GroupScheme.Rational.RelativeRootMultiples
import Langlands.GroupScheme.Rational.RelativeRootCoxeterConstruction
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.GenericCocharacter

/-! # The nonmultipliable roots of a relative root system and a base for them

For a finite crystallographic root pairing `P` over `ℚ`, `nonmultipliableRootPairing P` is the
root pairing formed by the roots whose double is not a root. It is reduced, and it is a root
system when `P` is. A functional that vanishes on no root cuts out a base of it.

For a maximal split torus `i` of a connected reductive group over a field, this gives
`exists_nonmultipliableBase`: a finite set `D` of nonmultipliable relative roots, the simple
roots of the nonmultipliable relative roots for a generic cocharacter `lam`, with the
properties used in the proof of Borel–Tits 1965, Théorème 7.2. It also gives
`nonmultipliable_eq_or_eq_neg`: the nonmultipliable relative roots are reduced. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Submodule

attribute [local instance] IsAddTorsionFree.of_module_rat

namespace Langlands.LinearAlgebra

variable {ι M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]

/-- The indices of the nonmultipliable roots of `P`: those whose double is not a root. -/
def nonmultipliableIndices (P : RootPairing ι ℚ M N) : Set ι :=
  {j | ∀ l, P.root l ≠ 2 • P.root j}

theorem mem_nonmultipliableIndices_iff (P : RootPairing ι ℚ M N) {j : ι} :
    j ∈ nonmultipliableIndices P ↔ ∀ l, P.root l ≠ 2 • P.root j :=
  Iff.rfl

private theorem reflectionPerm_notMem_nonmultipliableIndices (P : RootPairing ι ℚ M N)
    (i : ι) {j : ι} (hj : j ∉ nonmultipliableIndices P) :
    P.reflectionPerm i j ∉ nonmultipliableIndices P := by
  simp only [nonmultipliableIndices, Set.mem_ofPred_eq, not_forall, not_not] at hj ⊢
  obtain ⟨l, hl⟩ := hj
  exact ⟨P.reflectionPerm i l, by rw [P.root_reflectionPerm, P.root_reflectionPerm, hl, map_nsmul]⟩

/-- Reflections permute the nonmultipliable roots. -/
theorem reflectionPerm_mem_nonmultipliableIndices_iff (P : RootPairing ι ℚ M N) (i j : ι) :
    P.reflectionPerm i j ∈ nonmultipliableIndices P ↔ j ∈ nonmultipliableIndices P := by
  constructor
  · intro h
    by_contra hj
    exact reflectionPerm_notMem_nonmultipliableIndices P i hj h
  · intro h
    by_contra hj
    have := reflectionPerm_notMem_nonmultipliableIndices P i hj
    rw [P.reflectionPerm_self] at this
    exact this h

/-- The root pairing formed by the nonmultipliable roots of `P`, with their coroots and the
restricted reflection permutations. -/
def nonmultipliableRootPairing (P : RootPairing ι ℚ M N) :
    RootPairing (nonmultipliableIndices P) ℚ M N where
  toLinearMap := P.toLinearMap
  root := (Function.Embedding.subtype _).trans P.root
  coroot := (Function.Embedding.subtype _).trans P.coroot
  root_coroot_two j := P.root_coroot_two j
  reflectionPerm i := (P.reflectionPerm i).subtypeEquiv fun j =>
    (reflectionPerm_mem_nonmultipliableIndices_iff P i j).symm
  reflectionPerm_root i j := P.reflectionPerm_root i j
  reflectionPerm_coroot i j := P.reflectionPerm_coroot i j

variable (P : RootPairing ι ℚ M N)

@[simp] theorem nonmultipliableRootPairing_toLinearMap :
    (nonmultipliableRootPairing P).toLinearMap = P.toLinearMap := rfl

@[simp] theorem nonmultipliableRootPairing_root (j : nonmultipliableIndices P) :
    (nonmultipliableRootPairing P).root j = P.root j := rfl

@[simp] theorem nonmultipliableRootPairing_coroot (j : nonmultipliableIndices P) :
    (nonmultipliableRootPairing P).coroot j = P.coroot j := rfl

@[simp] theorem nonmultipliableRootPairing_pairing (j l : nonmultipliableIndices P) :
    (nonmultipliableRootPairing P).pairing j l = P.pairing j l := rfl

@[simp] theorem nonmultipliableRootPairing_reflection (j : nonmultipliableIndices P) :
    (nonmultipliableRootPairing P).reflection j = P.reflection j := rfl

@[simp] theorem nonmultipliableRootPairing_reflectionPerm (j l : nonmultipliableIndices P) :
    ((nonmultipliableRootPairing P).reflectionPerm j l : ι) = P.reflectionPerm j l := rfl

instance [Finite ι] : Finite (nonmultipliableIndices P) :=
  Subtype.finite

instance [P.IsCrystallographic] : (nonmultipliableRootPairing P).IsCrystallographic :=
  ⟨fun j l => P.exists_value (S := ℤ) j l⟩

/-- In a finite crystallographic root pairing, the double of a multipliable root is
nonmultipliable. -/
theorem two_smul_mem_nonmultipliableIndices [P.IsCrystallographic] {j l : ι}
    (hl : P.root l = 2 • P.root j) : l ∈ nonmultipliableIndices P := by
  intro m hm
  have h4 : P.root m = 4 • P.root j := by
    rw [hm, hl, ← mul_nsmul']
  rcases RootPairing.eq_one_or_two_of_root_eq_nsmul P h4 with h | h <;> norm_num at h

/-- Every root of `P` is a rational multiple of a nonmultipliable root. -/
theorem exists_nonmultipliable_smul [Finite ι] [P.IsCrystallographic] (j : ι) :
    ∃ l ∈ nonmultipliableIndices P, ∃ t : ℚ, t ≠ 0 ∧ P.root j = t • P.root l ∧
      P.coroot j = t⁻¹ • P.coroot l := by
  by_cases hj : j ∈ nonmultipliableIndices P
  · exact ⟨j, hj, 1, one_ne_zero, by simp, by simp⟩
  · simp only [nonmultipliableIndices, Set.mem_ofPred_eq, not_forall, not_not] at hj
    obtain ⟨l, hl⟩ := hj
    refine ⟨l, two_smul_mem_nonmultipliableIndices P hl, (1 / 2 : ℚ), by norm_num, ?_, ?_⟩
    · rw [hl, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      norm_num
    · have : P.root l = (2 : ℚ) • P.root j := by
        rw [hl, ← Nat.cast_smul_eq_nsmul ℚ]
        norm_num
      have hc := (RootPairing.coroot_eq_smul_coroot_iff (P := P) (i := j) (j := l)).mpr this
      rw [hc]
      norm_num

/-- A finite crystallographic rational root pairing without a root that is twice another is
reduced. -/
theorem isReduced_of_no_double [Finite ι] [P.IsCrystallographic]
    (hdouble : ∀ a b, P.root b ≠ (2 : ℚ) • P.root a) : P.IsReduced := by
  have hnegdouble (a b : ι) : P.root b ≠ (-2 : ℚ) • P.root a := by
    intro h
    apply hdouble (P.reflectionPerm a a) b
    simpa only [P.root_reflectionPerm, P.reflection_apply_self, smul_neg, neg_smul] using h
  constructor
  intro a b hdep
  have hprod : P.pairingIn ℤ a b * P.pairingIn ℤ b a = 4 :=
    (P.coxeterWeightIn_eq_four_iff_not_linearIndependent ℤ).mpr hdep
  have hbne : P.pairingIn ℤ b a ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    norm_num at hprod
  have habs : |P.pairingIn ℤ a b| * |P.pairingIn ℤ b a| = 4 := by
    rw [← abs_mul, hprod]
    norm_num
  have hbpos : 1 ≤ |P.pairingIn ℤ b a| := by
    have := abs_pos.mpr hbne
    omega
  have hbound : -4 ≤ P.pairingIn ℤ a b ∧ P.pairingIn ℤ a b ≤ 4 := by
    have hle : |P.pairingIn ℤ a b| ≤ 4 := by
      nlinarith [abs_nonneg (P.pairingIn ℤ a b)]
    constructor <;>
      linarith [le_abs_self (P.pairingIn ℤ a b), neg_le_abs (P.pairingIn ℤ a b)]
  obtain ⟨hlo, hhi⟩ := hbound
  interval_cases hp : P.pairingIn ℤ a b
  · have hq : P.pairingIn ℤ b a = -1 := by omega
    exact False.elim (hnegdouble b a
      ((P.pairingIn_neg_one_neg_four_iff ℤ b a).mp ⟨hq, hp⟩))
  · omega
  · have hq : P.pairingIn ℤ b a = -2 := by omega
    exact Or.inr ((P.pairingIn_neg_two_neg_two_iff ℤ a b).mp ⟨hp, hq⟩)
  · have hq : P.pairingIn ℤ b a = -4 := by omega
    exact False.elim (hnegdouble a b
      ((P.pairingIn_neg_one_neg_four_iff ℤ a b).mp ⟨hp, hq⟩))
  · omega
  · have hq : P.pairingIn ℤ b a = 4 := by omega
    exact False.elim (hdouble a b
      ((P.pairingIn_one_four_iff ℤ a b).mp ⟨hp, hq⟩))
  · have hq : P.pairingIn ℤ b a = 2 := by omega
    exact Or.inl (congrArg P.root ((P.pairingIn_two_two_iff ℤ a b).mp ⟨hp, hq⟩))
  · omega
  · have hq : P.pairingIn ℤ b a = 1 := by omega
    exact False.elim (hdouble b a
      ((P.pairingIn_one_four_iff ℤ b a).mp ⟨hq, hp⟩))

instance [Finite ι] [P.IsCrystallographic] : (nonmultipliableRootPairing P).IsReduced := by
  apply isReduced_of_no_double
  intro a b h
  apply a.2 b
  rw [nonmultipliableRootPairing_root, nonmultipliableRootPairing_root] at h
  rw [h, ← Nat.cast_smul_eq_nsmul ℚ]
  norm_num

instance [Finite ι] [P.IsCrystallographic] [P.IsRootSystem] :
    (nonmultipliableRootPairing P).IsRootSystem := by
  constructor
  · rw [eq_top_iff, ← RootPairing.IsRootSystem.span_root_eq_top (P := P), span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨l, hl, t, -, hroot, -⟩ := exists_nonmultipliable_smul P j
    rw [hroot]
    exact smul_mem _ _ (subset_span ⟨⟨l, hl⟩, rfl⟩)
  · rw [eq_top_iff, ← RootPairing.IsRootSystem.span_coroot_eq_top (P := P), span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨l, hl, t, -, -, hcoroot⟩ := exists_nonmultipliable_smul P j
    rw [hcoroot]
    exact smul_mem _ _ (subset_span ⟨⟨l, hl⟩, rfl⟩)

section Base

variable [Finite ι] [P.IsCrystallographic] [P.IsRootSystem]

/-- The base of the nonmultipliable roots of `P` cut out by an additive functional `f` that
vanishes on no root: the `f`-positive nonmultipliable roots that are not sums of two
`f`-positive nonmultipliable roots. -/
def nonmultipliableBase (f : M →+ ℚ) (hf : ∀ j, f (P.root j) ≠ 0) :
    (nonmultipliableRootPairing P).Base :=
  letI := (nonmultipliableRootPairing P).indexNeg
  RootPairing.Base.mk' _ (IsAddIndecomposable.baseOf (nonmultipliableRootPairing P).root f)
    ((nonmultipliableRootPairing P).linearIndepOn_root_baseOf f fun j => hf j)
    fun j => IsAddIndecomposable.mem_or_neg_mem_closure_baseOf _ f j (hf j) (by simp)

theorem mem_nonmultipliableBase_support_iff (f : M →+ ℚ) (hf : ∀ j, f (P.root j) ≠ 0)
    (j : nonmultipliableIndices P) :
    j ∈ (nonmultipliableBase P f hf).support ↔
      j ∈ IsAddIndecomposable.baseOf (nonmultipliableRootPairing P).root f := by
  simp [nonmultipliableBase, RootPairing.Base.mk']

/-- The simple roots of `nonmultipliableBase P f hf` are `f`-positive. -/
theorem pos_of_mem_nonmultipliableBase_support (f : M →+ ℚ) (hf : ∀ j, f (P.root j) ≠ 0)
    {j : nonmultipliableIndices P} (hj : j ∈ (nonmultipliableBase P f hf).support) :
    0 < f (P.root j) :=
  IsAddIndecomposable.baseOf_subset_pos (nonmultipliableRootPairing P).root f
    ((mem_nonmultipliableBase_support_iff P f hf j).mp hj)

end Base

/-- (A1) For two different simple roots `d ≠ e` of a base and positive integers `n, m`, the
vector `n • d - m • e` is neither zero nor a root. -/
theorem base_nsmul_sub_nsmul {κ : Type*} {Q : RootPairing κ ℚ M N} (b : Q.Base) {d e : κ}
    (hd : d ∈ b.support) (he : e ∈ b.support) (hde : d ≠ e) {n m : ℕ} (hn : 0 < n)
    (hm : 0 < m) :
    n • Q.root d - m • Q.root e ≠ 0 ∧ n • Q.root d - m • Q.root e ∉ range Q.root := by
  classical
  constructor
  · intro h
    have hli := b.linearIndependent_pair_of_ne (i := ⟨d, hd⟩) (j := ⟨e, he⟩)
      (by simpa using hde)
    rw [LinearIndependent.pair_iff] at hli
    have := (hli (n : ℚ) (-(m : ℚ)) (by
      simp only [neg_smul, ← sub_eq_add_neg, Nat.cast_smul_eq_nsmul]
      exact h)).1
    simp only [Nat.cast_eq_zero] at this
    omega
  · let g : κ → ℤ := fun k => if k = d then (n : ℤ) else if k = e then -(m : ℤ) else 0
    have hg : ∑ k ∈ b.support, g k • Q.root k = n • Q.root d - m • Q.root e := by
      have hsub : {d, e} ⊆ b.support := by
        simp [Finset.insert_subset_iff, hd, he]
      rw [← Finset.sum_subset hsub (by
        intro k _ hk
        have h1 : k ≠ d := by rintro rfl; simp at hk
        have h2 : k ≠ e := by rintro rfl; simp at hk
        simp [g, h1, h2]),
        Finset.sum_insert (by simpa using hde), Finset.sum_singleton]
      simp [g, Ne.symm hde, sub_eq_add_neg, natCast_zsmul]
    intro hmem
    have hsupp : Function.support g ⊆ b.support := by
      intro k hk
      by_cases h1 : k = d
      · subst h1; exact hd
      by_cases h2 : k = e
      · subst h2; exact he
      simp [g, h1, h2] at hk
    rcases b.pos_or_neg_of_sum_smul_root_mem g (by rwa [hg]) hsupp with hpos | hneg
    · have := le_of_lt hpos e
      simp [g, Ne.symm hde] at this
      omega
    · have := le_of_lt hneg d
      simp [g] at this
      omega

/-- (A2) In a finite reduced crystallographic root pairing over `ℚ`, no root is twice an
element of the `ℤ`-span of the roots. -/
theorem root_ne_two_smul_of_mem_span_int {κ : Type*} [Finite κ] {Q : RootPairing κ ℚ M N}
    [Q.IsCrystallographic] [Q.IsReduced] (b : Q.Base) (j : κ) {x : M}
    (hx : x ∈ span ℤ (range Q.root)) : Q.root j ≠ 2 • x := by
  suffices key : ∀ x ∈ span ℤ (range Q.root), Q.root j ≠ 2 • x from key x hx
  refine b.induction_reflect j (p := fun j => ∀ x ∈ span ℤ (range Q.root), Q.root j ≠ 2 • x)
    ?_ ?_ ?_
  · intro i hi x hx h
    rw [Q.root_reflectionPerm, Q.reflection_apply_self] at h
    apply hi (-x) (neg_mem hx)
    rw [smul_neg, ← h, neg_neg]
  · intro i hi x hx h
    have hx' : x ∈ Q.rootSpan ℤ := hx
    have key := congrArg (fun y => b.toWeightBasisInt.repr y ⟨i, hi⟩)
      (show (Q.rootSpanMem ℤ i : Q.rootSpan ℤ) = 2 • (⟨x, hx'⟩ : Q.rootSpan ℤ) from
        Subtype.ext (by simpa using h))
    have hb : b.toWeightBasisInt ⟨i, hi⟩ = Q.rootSpanMem ℤ i :=
      Subtype.ext (by simp)
    simp only [← hb, Module.Basis.repr_self, Finsupp.single_eq_same, map_nsmul,
      Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at key
    omega
  · intro i l hi hl x hx h
    rw [Q.root_reflectionPerm] at h
    apply hi (Q.reflection l x)
    · have : span ℤ (range Q.root) ≤ (span ℤ (range Q.root)).comap
          ((Q.reflection l).toLinearMap.restrictScalars ℤ) := by
        rw [span_le]
        rintro _ ⟨r, rfl⟩
        simp only [comap_coe, Set.mem_preimage, LinearMap.coe_restrictScalars,
          LinearEquiv.coe_coe, SetLike.mem_coe]
        rw [← Q.root_reflectionPerm]
        exact subset_span (mem_range_self _)
      exact this hx
    · have := congrArg (Q.reflection l) h
      rw [Q.reflection_same, map_nsmul] at this
      exact this

end Langlands.LinearAlgebra


universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.MaximalSplitSubgroup

open Langlands.LinearAlgebra.RationalSpan Langlands.LinearAlgebra
open Langlands.GroupScheme.RelativeRootSystem

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

section Pairing

variable {i : S.toGrp ⟶ G} [IsAffineHom G.X.hom] {J : Type u}
  (P : RootPairing J ℚ (relativeRootSpan i) (Module.Dual ℚ (relativeRootSpan i)))
  (hT : IsSplitTorus S.toGrp)
  (hroots : Subtype.val '' Set.range P.root = toRat '' relativeRoots i)

/-- The relative root of `i` whose rational image is the root `P.root r` of a relative root
pairing `P`. -/
def rootChar (r : J) : characterLattice S :=
  (RelativeRootCoxeter.rootIndexEquiv P hT hroots r).val

theorem rootChar_mem (r : J) : rootChar P hT hroots r ∈ relativeRoots i :=
  (RelativeRootCoxeter.rootIndexEquiv P hT hroots r).property

theorem toRat_rootChar (r : J) :
    toRat (rootChar P hT hroots r) = (P.root r : ℚ ⊗[ℤ] characterLattice S) :=
  congrArg Subtype.val (RelativeRootCoxeter.rootVector_rootIndexEquiv P hT hroots r)

theorem exists_rootChar_eq {c : characterLattice S} (hc : c ∈ relativeRoots i) :
    ∃ r, rootChar P hT hroots r = c := by
  obtain ⟨r, hr⟩ := (RelativeRootCoxeter.rootIndexEquiv P hT hroots).surjective ⟨c, hc⟩
  exact ⟨r, congrArg Subtype.val hr⟩

theorem rootChar_eq_iff {r : J} {c : characterLattice S} :
    rootChar P hT hroots r = c ↔ (P.root r : ℚ ⊗[ℤ] characterLattice S) = toRat c := by
  constructor
  · rintro rfl
    exact (toRat_rootChar P hT hroots r).symm
  · intro h
    apply hT.character_toRat_injective
    rw [toRat_rootChar, h]

/-- A root of `P` is nonmultipliable exactly when twice its character is not a relative
root. -/
theorem mem_nonmultipliableIndices_iff_rootChar (r : J) :
    r ∈ nonmultipliableIndices P ↔ (2 : ℤ) • rootChar P hT hroots r ∉ relativeRoots i := by
  rw [mem_nonmultipliableIndices_iff]
  constructor
  · intro h hmem
    obtain ⟨l, hl⟩ := exists_rootChar_eq P hT hroots hmem
    apply h l
    apply Subtype.ext
    rw [(rootChar_eq_iff P hT hroots).mp hl, map_zsmul, toRat_rootChar]
    simp [two_zsmul, two_nsmul]
  · intro h l hl
    apply h
    have : rootChar P hT hroots l = (2 : ℤ) • rootChar P hT hroots r := by
      rw [rootChar_eq_iff, map_zsmul, toRat_rootChar, hl]
      simp [two_zsmul, two_nsmul]
    rw [← this]
    exact rootChar_mem P hT hroots l

theorem rootChar_reflectionPerm_self (r : J) :
    rootChar P hT hroots (P.reflectionPerm r r) = -rootChar P hT hroots r := by
  rw [rootChar_eq_iff, map_neg, toRat_rootChar, P.root_reflectionPerm,
    P.reflection_apply_self]
  simp

section Crystallographic

variable [P.IsCrystallographic]

include hT hroots in
/-- If a relative root `c` and its double are relative roots, then the double of `2 • c` is
not a relative root. -/
theorem two_smul_two_smul_notMem {c : characterLattice S} (hc : c ∈ relativeRoots i)
    (h2 : (2 : ℤ) • c ∈ relativeRoots i) : (2 : ℤ) • (2 : ℤ) • c ∉ relativeRoots i := by
  obtain ⟨j, rfl⟩ := exists_rootChar_eq P hT hroots hc
  obtain ⟨l, hl⟩ := exists_rootChar_eq P hT hroots h2
  have hl' : P.root l = 2 • P.root j := by
    apply Subtype.ext
    rw [← toRat_rootChar P hT hroots, hl, map_zsmul, toRat_rootChar]
    simp [two_zsmul, two_nsmul]
  rw [← hl]
  exact (mem_nonmultipliableIndices_iff_rootChar P hT hroots l).mp
    (two_smul_mem_nonmultipliableIndices P hl')

include hT hroots in
/-- **Reducedness of the nonmultipliable relative roots.** Two nonmultipliable relative roots
with a nonzero integral relation `m • β = n • α` are equal or opposite. -/
theorem eq_or_eq_neg_of_nonmultipliable [Finite J] {α β : characterLattice S}
    (hα : α ∈ relativeRoots i) (hα2 : (2 : ℤ) • α ∉ relativeRoots i)
    (hβ : β ∈ relativeRoots i) (hβ2 : (2 : ℤ) • β ∉ relativeRoots i) {m n : ℤ} (hm : m ≠ 0)
    (h : m • β = n • α) : β = α ∨ β = -α := by
  obtain ⟨a, rfl⟩ := exists_rootChar_eq P hT hroots hα
  obtain ⟨b, rfl⟩ := exists_rootChar_eq P hT hroots hβ
  have ha := (mem_nonmultipliableIndices_iff_rootChar P hT hroots a).mpr hα2
  have hb := (mem_nonmultipliableIndices_iff_rootChar P hT hroots b).mpr hβ2
  have h' := congrArg toRat h
  rw [map_zsmul, map_zsmul, toRat_rootChar, toRat_rootChar] at h'
  have hdep : ¬ LinearIndependent ℚ ![(nonmultipliableRootPairing P).root ⟨b, hb⟩,
      (nonmultipliableRootPairing P).root ⟨a, ha⟩] := by
    rw [LinearIndependent.pair_iff]
    intro hli
    have key := hli (m : ℚ) (-(n : ℚ)) (by
      apply Subtype.ext
      simp only [nonmultipliableRootPairing_root, Submodule.coe_add, neg_smul,
        Int.cast_smul_eq_zsmul, Submodule.coe_neg, ZeroMemClass.coe_zero]
      rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, h', add_neg_cancel])
    exact hm (by exact_mod_cast key.1)
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := nonmultipliableRootPairing P) ⟨b, hb⟩ ⟨a, ha⟩
    hdep with hr | hr
  · left
    rw [rootChar_eq_iff, toRat_rootChar]
    exact congrArg Subtype.val hr
  · right
    rw [rootChar_eq_iff, map_neg, toRat_rootChar]
    have := congrArg Subtype.val hr
    simpa using this

end Crystallographic

variable [Mono i.hom.hom.left]

theorem corootFunctional_root (ν : cocharacterLattice S) (r : J) :
    corootFunctional i ν (P.root r) = (latticePairing S (rootChar P hT hroots r) ν : ℚ) :=
  RelativeRootCoxeter.functional_root P hT hroots ν r

/-- The reflection formula at the level of characters, for any cocharacter `ν` that pairs to
`2` with the root `rootChar j` and whose reflection formula preserves the relative roots. -/
theorem rootChar_reflectionPerm [Finite J] [P.IsRootSystem] (j : J) (ν : cocharacterLattice S)
    (hν : latticePairing S (rootChar P hT hroots j) ν = 2)
    (hrefl : ∀ c ∈ relativeRoots i,
      c - latticePairing S c ν • rootChar P hT hroots j ∈ relativeRoots i) (l : J) :
    rootChar P hT hroots (P.reflectionPerm j l) =
      rootChar P hT hroots l -
        latticePairing S (rootChar P hT hroots l) ν • rootChar P hT hroots j := by
  have hf₁ : corootFunctional i ν (P.root j) = 2 := by
    rw [corootFunctional_root P hT hroots, hν]
    norm_num
  have hf₂ : Set.MapsTo (Module.preReflection (P.root j) (corootFunctional i ν))
      (Set.range P.root) (Set.range P.root) := by
    rintro _ ⟨l, rfl⟩
    obtain ⟨l', hl'⟩ := exists_rootChar_eq P hT hroots (hrefl _ (rootChar_mem P hT hroots l))
    refine ⟨l', Subtype.ext ?_⟩
    rw [(rootChar_eq_iff P hT hroots).mp hl', Module.preReflection_apply,
      corootFunctional_root P hT hroots, map_sub, map_zsmul, toRat_rootChar, toRat_rootChar]
    simp [Int.cast_smul_eq_zsmul]
  have : Module.IsTorsionFree ℚ (relativeRootSpan i) :=
    DivisionSemiring.to_moduleIsTorsionFree
  have hfg : corootFunctional i ν = P.coroot' j :=
    Module.Dual.eq_of_preReflection_mapsTo (Set.finite_range P.root)
      (RootPairing.IsRootSystem.span_root_eq_top (P := P)) hf₁ hf₂ (P.coroot_root_two j)
      (P.mapsTo_reflection_root j)
  rw [rootChar_eq_iff, map_sub, map_zsmul, toRat_rootChar, toRat_rootChar, P.root_reflectionPerm,
    P.reflection_apply_root, ← P.root_coroot'_eq_pairing, ← hfg,
    corootFunctional_root P hT hroots]
  simp [Int.cast_smul_eq_zsmul]

section Base

variable [Finite J] [P.IsCrystallographic] [P.IsRootSystem]
  (lam : cocharacterLattice S) (hlam : IsGenericCocharacter i lam)

omit [Finite J] [P.IsCrystallographic] [P.IsRootSystem] in
include hT hroots hlam in
theorem corootFunctional_root_ne_zero (j : J) :
    (corootFunctional i lam).toAddMonoidHom (P.root j) ≠ 0 := by
  rw [LinearMap.toAddMonoidHom_coe, corootFunctional_root P hT hroots]
  exact_mod_cast hlam _ (rootChar_mem P hT hroots j)

/-- The base of the nonmultipliable roots of `P` cut out by the generic cocharacter `lam`. -/
def simpleBase : (nonmultipliableRootPairing P).Base :=
  nonmultipliableBase P (corootFunctional i lam).toAddMonoidHom
    (corootFunctional_root_ne_zero P hT hroots lam hlam)

/-- The characters of the simple nonmultipliable roots determined by `lam`. -/
def simpleChars : Finset (characterLattice S) := by
  classical
  exact (simpleBase P hT hroots lam hlam).support.image fun j => rootChar P hT hroots j.val

theorem mem_simpleChars {d : characterLattice S} :
    d ∈ simpleChars P hT hroots lam hlam ↔
      ∃ j ∈ (simpleBase P hT hroots lam hlam).support, rootChar P hT hroots j.val = d := by
  classical
  simp [simpleChars]

theorem rootChar_mem_simpleChars {j : nonmultipliableIndices P}
    (hj : j ∈ (simpleBase P hT hroots lam hlam).support) :
    rootChar P hT hroots j.val ∈ simpleChars P hT hroots lam hlam :=
  (mem_simpleChars P hT hroots lam hlam).mpr ⟨j, hj, rfl⟩

theorem simpleChars_mem {d : characterLattice S} (hd : d ∈ simpleChars P hT hroots lam hlam) :
    d ∈ relativeRoots i ∧ (2 : ℤ) • d ∉ relativeRoots i := by
  obtain ⟨j, -, rfl⟩ := (mem_simpleChars P hT hroots lam hlam).mp hd
  exact ⟨rootChar_mem P hT hroots j.val,
    (mem_nonmultipliableIndices_iff_rootChar P hT hroots j.val).mp j.property⟩

theorem simpleChars_pos {d : characterLattice S} (hd : d ∈ simpleChars P hT hroots lam hlam) :
    0 < latticePairing S d lam := by
  obtain ⟨j, hj, rfl⟩ := (mem_simpleChars P hT hroots lam hlam).mp hd
  have := pos_of_mem_nonmultipliableBase_support P _
    (corootFunctional_root_ne_zero P hT hroots lam hlam) hj
  rw [LinearMap.toAddMonoidHom_coe, corootFunctional_root P hT hroots] at this
  exact_mod_cast this

/-- For two different simple characters `d ≠ e` and positive `n, m`, the character
`n • d - m • e` is nonzero, and if it is a relative root then so is its double. -/
theorem nsmul_sub_nsmul_simpleChars {d e : characterLattice S}
    (hd : d ∈ simpleChars P hT hroots lam hlam) (he : e ∈ simpleChars P hT hroots lam hlam)
    (hde : d ≠ e) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    n • d - m • e ≠ 0 ∧
      (n • d - m • e ∈ relativeRoots i → (2 : ℤ) • (n • d - m • e) ∈ relativeRoots i) := by
  obtain ⟨j, hj, rfl⟩ := (mem_simpleChars P hT hroots lam hlam).mp hd
  obtain ⟨l, hl, rfl⟩ := (mem_simpleChars P hT hroots lam hlam).mp he
  have hjl : j ≠ l := by
    rintro rfl
    exact hde rfl
  have hA := base_nsmul_sub_nsmul (simpleBase P hT hroots lam hlam) hj hl hjl hn hm
  have hval : ((n • (nonmultipliableRootPairing P).root j -
      m • (nonmultipliableRootPairing P).root l : relativeRootSpan i) :
        ℚ ⊗[ℤ] characterLattice S) =
      toRat (n • rootChar P hT hroots j.val - m • rootChar P hT hroots l.val) := by
    rw [map_sub, map_nsmul, map_nsmul, toRat_rootChar, toRat_rootChar]
    simp
  constructor
  · intro h0
    apply hA.1
    apply Subtype.ext
    rw [hval, h0, map_zero]
    rfl
  · intro hmem
    by_contra h2
    obtain ⟨r, hr⟩ := exists_rootChar_eq P hT hroots hmem
    have hr' : r ∈ nonmultipliableIndices P :=
      (mem_nonmultipliableIndices_iff_rootChar P hT hroots r).mpr (hr ▸ h2)
    apply hA.2
    refine ⟨⟨r, hr'⟩, Subtype.ext ?_⟩
    rw [nonmultipliableRootPairing_root, hval, ← hr, toRat_rootChar]

/-- The sums of simple characters have rational images in the `ℤ`-span of the
nonmultipliable roots. -/
theorem exists_mem_span_of_mem_closure {c : characterLattice S}
    (hc : c ∈ AddSubsemigroup.closure (simpleChars P hT hroots lam hlam : Set _)) :
    ∃ x ∈ Submodule.span ℤ (Set.range (nonmultipliableRootPairing P).root),
      (x : ℚ ⊗[ℤ] characterLattice S) = toRat c := by
  induction hc using AddSubsemigroup.closure_induction with
  | mem c hc =>
    obtain ⟨j, -, rfl⟩ := (mem_simpleChars P hT hroots lam hlam).mp hc
    exact ⟨_, Submodule.subset_span ⟨j, rfl⟩, (toRat_rootChar P hT hroots j.val).symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, hxa⟩ := ha
    obtain ⟨y, hy, hyb⟩ := hb
    exact ⟨x + y, add_mem hx hy, by rw [Submodule.coe_add, hxa, hyb, map_add]⟩

/-- A relative root that is a sum of simple characters is nonmultipliable. -/
theorem two_smul_notMem_of_mem_closure {c : characterLattice S} (hc : c ∈ relativeRoots i)
    (hcl : c ∈ AddSubsemigroup.closure (simpleChars P hT hroots lam hlam : Set _)) :
    (2 : ℤ) • c ∉ relativeRoots i := by
  intro h2
  obtain ⟨x, hx, hxc⟩ := exists_mem_span_of_mem_closure P hT hroots lam hlam hcl
  obtain ⟨r, hr⟩ := exists_rootChar_eq P hT hroots h2
  have hr' : r ∈ nonmultipliableIndices P :=
    (mem_nonmultipliableIndices_iff_rootChar P hT hroots r).mpr
      (hr ▸ two_smul_two_smul_notMem P hT hroots hc h2)
  apply root_ne_two_smul_of_mem_span_int (simpleBase P hT hroots lam hlam) ⟨r, hr'⟩ hx
  apply Subtype.ext
  rw [nonmultipliableRootPairing_root, ← toRat_rootChar P hT hroots, hr, map_zsmul]
  simp [hxc, two_zsmul, two_nsmul]

/-- Every nonmultipliable relative root is a sum of simple characters or the negative of
one. -/
theorem mem_closure_or_neg_mem_closure {c : characterLattice S} (hc : c ∈ relativeRoots i)
    (hc2 : (2 : ℤ) • c ∉ relativeRoots i) :
    c ∈ AddSubmonoid.closure (simpleChars P hT hroots lam hlam : Set _) ∨
      -c ∈ AddSubmonoid.closure (simpleChars P hT hroots lam hlam : Set _) := by
  obtain ⟨r, rfl⟩ := exists_rootChar_eq P hT hroots hc
  have hr := (mem_nonmultipliableIndices_iff_rootChar P hT hroots r).mpr hc2
  have key : ∀ x ∈ AddSubmonoid.closure ((nonmultipliableRootPairing P).root ''
      ((simpleBase P hT hroots lam hlam).support : Set _)),
      ∃ y ∈ AddSubmonoid.closure (simpleChars P hT hroots lam hlam : Set _),
        toRat y = (x : ℚ ⊗[ℤ] characterLattice S) := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact ⟨rootChar P hT hroots j.val,
        AddSubmonoid.subset_closure (rootChar_mem_simpleChars P hT hroots lam hlam hj),
        toRat_rootChar P hT hroots j.val⟩
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      exact ⟨a + b, add_mem ha hb, by rw [map_add, hax, hby, Submodule.coe_add]⟩
  rcases (simpleBase P hT hroots lam hlam).root_mem_or_neg_mem ⟨r, hr⟩ with h | h
  · left
    obtain ⟨y, hy, hyx⟩ := key _ h
    convert hy
    apply hT.character_toRat_injective
    rw [hyx, toRat_rootChar]
    rfl
  · right
    obtain ⟨y, hy, hyx⟩ := key _ h
    convert hy
    apply hT.character_toRat_injective
    rw [hyx, map_neg, toRat_rootChar]
    simp

/-- For each simple character `d₀` there is a cocharacter vanishing on `d₀` and positive on
the other simple characters. -/
theorem exists_separating_cocharacter {d₀ : characterLattice S}
    (hd₀ : d₀ ∈ simpleChars P hT hroots lam hlam) :
    ∃ mu : cocharacterLattice S, latticePairing S d₀ mu = 0 ∧
      ∀ e ∈ simpleChars P hT hroots lam hlam, e ≠ d₀ → 0 < latticePairing S e mu := by
  classical
  have hli : LinearIndependent ℚ
      (fun a : ((simpleBase P hT hroots lam hlam).support : Set (nonmultipliableIndices P)) =>
        toRat (rootChar P hT hroots a.val.val)) := by
    have h := LinearIndependent.map' (simpleBase P hT hroots lam hlam).linearIndepOn_root
      (relativeRootSpan i).subtype (Submodule.ker_subtype _)
    convert h using 1
    funext a
    exact toRat_rootChar P hT hroots a.val.val
  obtain ⟨d, hd, mu, hmu⟩ := hT.exists_scaled_pairings
    (fun a : ((simpleBase P hT hroots lam hlam).support : Set (nonmultipliableIndices P)) =>
      rootChar P hT hroots a.val.val) hli
    (fun a => if rootChar P hT hroots a.val.val = d₀ then 0 else 1)
  refine ⟨mu, ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := (mem_simpleChars P hT hroots lam hlam).mp hd₀
    have := hmu ⟨j, hj⟩
    simpa using this
  · intro e he hne
    obtain ⟨l, hl, rfl⟩ := (mem_simpleChars P hT hroots lam hlam).mp he
    have := hmu ⟨l, hl⟩
    simp only [hne, ite_false, mul_one] at this
    rw [this]
    exact hd

/-- **Weyl closure.** Let `ν d` be a cocharacter for each simple character `d`, pairing to `2`
with `d` and whose reflection formula preserves the relative roots. A property of characters
that holds on the simple characters and is preserved by these reflections of nonmultipliable
relative roots holds on every nonmultipliable relative root. -/
theorem forall_nonmultipliable_of_reflect
    (ν : ∀ d ∈ simpleChars P hT hroots lam hlam, cocharacterLattice S)
    (hν : ∀ d (hd : d ∈ simpleChars P hT hroots lam hlam),
      latticePairing S d (ν d hd) = 2 ∧
        ∀ c ∈ relativeRoots i, c - latticePairing S c (ν d hd) • d ∈ relativeRoots i)
    (Q : characterLattice S → Prop) (hQ : ∀ d ∈ simpleChars P hT hroots lam hlam, Q d)
    (hQrefl : ∀ d (hd : d ∈ simpleChars P hT hroots lam hlam), ∀ c ∈ relativeRoots i,
      (2 : ℤ) • c ∉ relativeRoots i → Q c → Q (c - latticePairing S c (ν d hd) • d))
    {c : characterLattice S} (hc : c ∈ relativeRoots i) (hc2 : (2 : ℤ) • c ∉ relativeRoots i) :
    Q c := by
  obtain ⟨r, rfl⟩ := exists_rootChar_eq P hT hroots hc
  have hr := (mem_nonmultipliableIndices_iff_rootChar P hT hroots r).mpr hc2
  have hmem (t : nonmultipliableIndices P) : rootChar P hT hroots t.val ∈ relativeRoots i ∧
      (2 : ℤ) • rootChar P hT hroots t.val ∉ relativeRoots i :=
    ⟨rootChar_mem P hT hroots t.val,
      (mem_nonmultipliableIndices_iff_rootChar P hT hroots t.val).mp t.property⟩
  have hnegmem (t : nonmultipliableIndices P) : -rootChar P hT hroots t.val ∈ relativeRoots i ∧
      (2 : ℤ) • -rootChar P hT hroots t.val ∉ relativeRoots i := by
    have := hmem ⟨P.reflectionPerm t.val t.val,
      (reflectionPerm_mem_nonmultipliableIndices_iff P t.val t.val).mpr t.property⟩
    rwa [rootChar_reflectionPerm_self] at this
  suffices key : ∀ t : nonmultipliableIndices P,
      Q (rootChar P hT hroots t.val) ∧ Q (-rootChar P hT hroots t.val) from
    (key ⟨r, hr⟩).1
  intro t
  refine (simpleBase P hT hroots lam hlam).induction_reflect t
    (p := fun t => Q (rootChar P hT hroots t.val) ∧ Q (-rootChar P hT hroots t.val)) ?_ ?_ ?_
  · intro t ht
    simp only [nonmultipliableRootPairing_reflectionPerm, rootChar_reflectionPerm_self, neg_neg]
    exact ⟨ht.2, ht.1⟩
  · intro t ht
    have hd := rootChar_mem_simpleChars P hT hroots lam hlam ht
    refine ⟨hQ _ hd, ?_⟩
    have := hQrefl _ hd _ (hmem t).1 (hmem t).2 (hQ _ hd)
    rwa [(hν _ hd).1, two_zsmul, sub_add_cancel_left] at this
  · intro t l ht hl
    have hd := rootChar_mem_simpleChars P hT hroots lam hlam hl
    obtain ⟨h2, hrefl⟩ := hν _ hd
    have hform := rootChar_reflectionPerm P hT hroots l.val (ν _ hd) h2 hrefl t.val
    simp only [nonmultipliableRootPairing_reflectionPerm, hform]
    constructor
    · exact hQrefl _ hd _ (hmem t).1 (hmem t).2 ht.1
    · have := hQrefl _ hd _ (hnegmem t).1 (hnegmem t).2 ht.2
      convert this using 1
      simp only [map_neg, LinearMap.neg_apply, neg_smul]
      abel

end Base

end Pairing

/-- **A base of the nonmultipliable relative roots** (Borel–Tits 1965, §7.2, combinatorial
input). For a maximal split torus `i` of a connected reductive group `G` over a field there are
a finite set `D` of nonmultipliable relative roots and a cocharacter `lam` such that `lam` is
positive on `D` and nonzero on every relative root; no `n • d - m • e` with `d ≠ e` in `D` and
`n, m > 0` is zero or a relative root; every relative root that is a nonempty sum of elements of
`D` is nonmultipliable; every nonmultipliable relative root is a sum of elements of `D` or the
negative of one; each `d₀ ∈ D` is separated from the rest of `D` by a cocharacter; and every
property that holds on `D` and is stable under the reflections in `D` of nonmultipliable
relative roots holds on all nonmultipliable relative roots. -/
theorem exists_nonmultipliableBase (hG : IsConnectedReductive G) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) :
    haveI := hG.isAffineHom
    ∃ (D : Finset (characterLattice S)) (lam : cocharacterLattice S),
      (∀ d ∈ D, d ∈ roots i ∧ (2 : ℤ) • d ∉ roots i) ∧
      (∀ d ∈ D, 0 < latticePairing S d lam) ∧
      (∀ c ∈ roots i, latticePairing S c lam ≠ 0) ∧
      (∀ d ∈ D, ∀ e ∈ D, d ≠ e → ∀ n m : ℕ, 0 < n → 0 < m →
        n • d - m • e ≠ 0 ∧ n • d - m • e ∉ roots i) ∧
      (∀ c ∈ roots i, c ∈ AddSubsemigroup.closure (D : Set (characterLattice S)) →
        (2 : ℤ) • c ∉ roots i) ∧
      (∀ d₀ ∈ D, ∃ mu : cocharacterLattice S, latticePairing S d₀ mu = 0 ∧
        ∀ e ∈ D, e ≠ d₀ → 0 < latticePairing S e mu) ∧
      (∀ c ∈ roots i, (2 : ℤ) • c ∉ roots i →
        c ∈ AddSubmonoid.closure (D : Set (characterLattice S)) ∨
          -c ∈ AddSubmonoid.closure (D : Set (characterLattice S))) ∧
      (∀ ν : ∀ d ∈ D, cocharacterLattice S,
        (∀ d (hd : d ∈ D), latticePairing S d (ν d hd) = 2 ∧
          ∀ c ∈ roots i, c - latticePairing S c (ν d hd) • d ∈ roots i) →
        ∀ Q : characterLattice S → Prop, (∀ d ∈ D, Q d) →
          (∀ d (hd : d ∈ D), ∀ c ∈ roots i, (2 : ℤ) • c ∉ roots i → Q c →
            Q (c - latticePairing S c (ν d hd) • d)) →
          ∀ c ∈ roots i, (2 : ℤ) • c ∉ roots i → Q c) := by
  have := hG.isAffineHom
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have : Smooth G.X.hom := hG.smooth
  have hT : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  obtain ⟨J, hJ, P, hRS, hCr, -, hroots, -, -⟩ := relativeRootSystem k G hG S i hi
  obtain ⟨lam, hlam⟩ := hT.exists_genericCocharacter i
  simp only [← relativeRoots_eq_roots]
  refine ⟨simpleChars P hT hroots lam hlam, lam,
    fun d hd => simpleChars_mem P hT hroots lam hlam hd,
    fun d hd => simpleChars_pos P hT hroots lam hlam hd, hlam, ?_,
    fun c hc hcl => two_smul_notMem_of_mem_closure P hT hroots lam hlam hc hcl,
    fun d₀ hd₀ => exists_separating_cocharacter P hT hroots lam hlam hd₀,
    fun c hc hc2 => mem_closure_or_neg_mem_closure P hT hroots lam hlam hc hc2,
    fun ν hν Q hQ hQrefl c hc hc2 =>
      forall_nonmultipliable_of_reflect P hT hroots lam hlam ν hν Q hQ hQrefl hc hc2⟩
  intro d hd e he hde n m hn hm
  have h1 := nsmul_sub_nsmul_simpleChars P hT hroots lam hlam hd he hde hn hm
  refine ⟨h1.1, fun hmem => ?_⟩
  have h2 := h1.2 hmem
  have hnn : (2 : ℤ) • (n • d - m • e) = (2 * n) • d - (2 * m) • e := by
    rw [smul_sub, ← natCast_zsmul, ← natCast_zsmul, ← natCast_zsmul, ← natCast_zsmul,
      smul_smul, smul_smul]
    push_cast
    rfl
  have h3 := (nsmul_sub_nsmul_simpleChars P hT hroots lam hlam hd he hde (by omega)
    (by omega) (n := 2 * n) (m := 2 * m)).2 (hnn ▸ h2)
  rw [← hnn] at h3
  exact two_smul_two_smul_notMem P hT hroots hmem h2 h3

/-- **The nonmultipliable relative roots are reduced.** For a maximal split torus `i` of a
connected reductive group `G` over a field, two nonmultipliable relative roots `α, β` with
`m • β = n • α` for integers `m ≠ 0` and `n` satisfy `β = α` or `β = -α`. -/
theorem nonmultipliable_eq_or_eq_neg (hG : IsConnectedReductive G) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) :
    haveI := hG.isAffineHom
    ∀ α ∈ roots i, (2 : ℤ) • α ∉ roots i → ∀ β ∈ roots i, (2 : ℤ) • β ∉ roots i →
      (∃ m n : ℤ, m ≠ 0 ∧ m • β = n • α) → β = α ∨ β = -α := by
  have := hG.isAffineHom
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have hT : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  obtain ⟨J, hJ, P, -, hCr, -, hroots, -, -⟩ := relativeRootSystem k G hG S i hi
  simp only [← relativeRoots_eq_roots]
  rintro α hα hα2 β hβ hβ2 ⟨m, n, hm, h⟩
  exact eq_or_eq_neg_of_nonmultipliable P hT hroots hα hα2 hβ hβ2 hm h

end Langlands.GroupScheme.MaximalSplitSubgroup
