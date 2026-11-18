import Langlands.LinearAlgebra.GaloisSubmoduleDescent
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.SimpleRing.Matrix

/-! # Matrix algebras fixed by a twisted Galois action -/

noncomputable section

universe u

open scoped Matrix

namespace Langlands.Algebra.GaloisTwistedMatrix

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The `k`-subalgebra of matrices `X` with `P σ * X = σ(X) * P σ` for every `σ`. -/
def twistedFixed (P : (K ≃ₐ[k] K) → Matrix n n K) : Subalgebra k (Matrix n n K) where
  carrier := {X | ∀ σ, P σ * X = X.map σ * P σ}
  mul_mem' {X Y} hX hY σ := by
    change P σ * (X * Y) = (X * Y).map σ * P σ
    rw [Matrix.map_mul, ← mul_assoc, hX σ, mul_assoc, hY σ, mul_assoc]
  add_mem' {X Y} hX hY σ := by
    change P σ * (X + Y) = (X + Y).map σ * P σ
    rw [Matrix.map_add _ (map_add σ), mul_add, add_mul, hX σ, hY σ]
  algebraMap_mem' c σ := by
    rw [Matrix.map_algebraMap c σ (map_zero σ) (σ.commutes c), Algebra.commutes]

theorem mem_twistedFixed (P : (K ≃ₐ[k] K) → Matrix n n K) (X : Matrix n n K) :
    X ∈ twistedFixed P ↔ ∀ σ, P σ * X = X.map σ * P σ :=
  Iff.rfl

section Independence

variable {ι : Type*} (P : (K ≃ₐ[k] K) → Matrix n n K)

omit [Fintype n] [DecidableEq n] in
theorem map_linearCombination_conjugate (σ : K ≃ₐ[k] K) (v : ι → Matrix n n K)
    (x : ι →₀ K) :
    (Finsupp.linearCombination K v x).map σ =
      Finsupp.linearCombination K (fun i => (v i).map σ)
        (LinearAlgebra.GaloisSubmoduleDescent.conjugate σ x) := by
  induction x using Finsupp.induction_linear with
  | zero => ext i j; simp [LinearAlgebra.GaloisSubmoduleDescent.conjugate]
  | add x y hx hy =>
    rw [map_add, Matrix.map_add _ (map_add σ), hx, hy, ← map_add]
    congr 1
    ext i
    simp [LinearAlgebra.GaloisSubmoduleDescent.conjugate]
  | single i c =>
    ext a b
    simp [LinearAlgebra.GaloisSubmoduleDescent.conjugate, Finsupp.linearCombination_single]

/-- Matrices fixed by an invertible twisted Galois action that are linearly independent over
`k` stay linearly independent over `K`. -/
theorem linearIndependent_of_le_twistedFixed [IsGalois k K] (hP : ∀ σ, IsUnit (P σ))
    (v : ι → Matrix n n K) (hv : ∀ i, v i ∈ twistedFixed P) (hli : LinearIndependent k v) :
    LinearIndependent K v := by
  classical
  let W := LinearMap.ker (Finsupp.linearCombination K v)
  have hW : ∀ (σ : K ≃ₐ[k] K) (x : ι →₀ K), x ∈ W →
      LinearAlgebra.GaloisSubmoduleDescent.conjugate σ x ∈ W := by
    intro σ x hx
    have hx' : Finsupp.linearCombination K v x = 0 := hx
    change Finsupp.linearCombination K v (LinearAlgebra.GaloisSubmoduleDescent.conjugate σ x) = 0
    have key : P σ * Finsupp.linearCombination K v (LinearAlgebra.GaloisSubmoduleDescent.conjugate σ x) =
        (Finsupp.linearCombination K v x).map σ * P σ := by
      rw [map_linearCombination_conjugate, Finsupp.linearCombination_apply,
        Finsupp.linearCombination_apply, Finsupp.mul_sum, Finsupp.sum_mul]
      refine Finsupp.sum_congr fun i _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, hv i σ]
    rw [hx', Matrix.map_zero _ (map_zero σ), zero_mul] at key
    exact ((hP σ).mul_right_eq_zero).mp key
  have hspan := LinearAlgebra.GaloisSubmoduleDescent.eq_span_ground_vectors W hW
  have hbot : W = ⊥ := by
    rw [hspan, Submodule.span_eq_bot]
    rintro x ⟨y, rfl, hy⟩
    have hy' : Finsupp.linearCombination K v (LinearAlgebra.GaloisSubmoduleDescent.extend y) = 0 := hy
    have hyk : Finsupp.linearCombination k v y = 0 := by
      rw [← hy', Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
        LinearAlgebra.GaloisSubmoduleDescent.extend, Finsupp.mapRange.linearMap_apply,
        Finsupp.sum_mapRange_index (fun i => zero_smul K (v i))]
      refine Finsupp.sum_congr fun i _ => ?_
      rw [Algebra.linearMap_apply, algebraMap_smul]
    rw [linearIndependent_iff.mp hli y hyk, map_zero]
  rw [LinearIndependent, ← LinearMap.ker_eq_bot]
  exact hbot

end Independence

section Span

variable (A : Subalgebra k (Matrix n n K))
  (hspan : Submodule.span K (A : Set (Matrix n n K)) = ⊤)

include hspan

/-- A matrix commuting with every element of `A` is central. -/
theorem commute_of_forall_commute {z : Matrix n n K} (hz : ∀ a ∈ A, z * a = a * z)
    (M : Matrix n n K) : z * M = M * z := by
  have hM : M ∈ Submodule.span K (A : Set (Matrix n n K)) := by
    rw [hspan]
    exact Submodule.mem_top
  induction hM using Submodule.span_induction with
  | mem a ha => exact hz a ha
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add, add_mul, ha, hb]
  | smul c a _ ha => rw [Matrix.mul_smul, Matrix.smul_mul, ha]

/-- The `K`-span of a two-sided ideal of `A` is stable under left multiplication by all
matrices. -/
theorem mul_mem_span_left (V : Submodule k (Matrix n n K))
    (hV : ∀ a ∈ A, ∀ x ∈ V, a * x ∈ V) (M : Matrix n n K) {x : Matrix n n K}
    (hx : x ∈ Submodule.span K (V : Set (Matrix n n K))) :
    M * x ∈ Submodule.span K (V : Set (Matrix n n K)) := by
  have hM : M ∈ Submodule.span K (A : Set (Matrix n n K)) := by
    rw [hspan]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    induction hM using Submodule.span_induction with
    | mem a ha => exact Submodule.subset_span (hV a ha y hy)
    | zero => simp
    | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add y w _ _ hy hw => rw [mul_add]; exact Submodule.add_mem _ hy hw
  | smul c y _ hy => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hy

theorem mul_mem_span_right (V : Submodule k (Matrix n n K))
    (hV : ∀ a ∈ A, ∀ x ∈ V, x * a ∈ V) (M : Matrix n n K) {x : Matrix n n K}
    (hx : x ∈ Submodule.span K (V : Set (Matrix n n K))) :
    x * M ∈ Submodule.span K (V : Set (Matrix n n K)) := by
  have hM : M ∈ Submodule.span K (A : Set (Matrix n n K)) := by
    rw [hspan]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    induction hM using Submodule.span_induction with
    | mem a ha => exact Submodule.subset_span (hV a ha y hy)
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add y w _ _ hy hw => rw [add_mul]; exact Submodule.add_mem _ hy hw
  | smul c y _ hy => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ c hy

end Span

section CentralSimple

variable [IsGalois k K] (P : (K ≃ₐ[k] K) → Matrix n n K) (hP : ∀ σ, IsUnit (P σ))
  (A : Subalgebra k (Matrix n n K)) (hA : A ≤ twistedFixed P)

include hP hA

theorem linearIndepOn_of_le (s : Set (Matrix n n K)) (hs : s ⊆ A)
    (hli : LinearIndepOn k id s) : LinearIndepOn K id s :=
  linearIndependent_of_le_twistedFixed P hP (fun x : s => (x : Matrix n n K))
    (fun x => hA (hs x.2)) hli

/-- An element of `A` in the `K`-span of a `k`-subspace of `A` lies in that subspace. -/
theorem mem_of_mem_span (V : Submodule k (Matrix n n K))
    (hV : (V : Set (Matrix n n K)) ⊆ A) {x : Matrix n n K} (hx : x ∈ A)
    (hxs : x ∈ Submodule.span K (V : Set (Matrix n n K))) : x ∈ V := by
  obtain ⟨b, hbV, hbspan, hbli⟩ := exists_linearIndependent k (V : Set (Matrix n n K))
  by_contra hxV
  have hxb : x ∉ b := fun h => hxV (hbV h)
  have hx_notin : x ∉ Submodule.span k b := by
    rw [hbspan, Submodule.span_eq]
    exact hxV
  have hli' : LinearIndepOn k id (insert x b) :=
    (linearIndepOn_id_insert hxb).mpr ⟨hbli, hx_notin⟩
  have hliK := linearIndepOn_of_le P hP A hA (insert x b)
    (Set.insert_subset hx (hbV.trans hV)) hli'
  apply ((linearIndepOn_id_insert hxb).mp hliK).2
  have hle : Submodule.span K (V : Set (Matrix n n K)) ≤ Submodule.span K b := by
    rw [Submodule.span_le]
    intro y hy
    have hyb : y ∈ Submodule.span k b := by
      rw [hbspan]
      exact Submodule.subset_span hy
    exact Submodule.span_le_restrictScalars k K b hyb
  exact hle hxs

/-- `A` is finite-dimensional over `k`. -/
theorem finiteDimensional : FiniteDimensional k A := by
  have hrank : Module.rank k A ≤ (Fintype.card n * Fintype.card n : ℕ) := by
    apply rank_le
    intro s hs
    have hs' : LinearIndependent k (fun i : s => ((i : A) : Matrix n n K)) :=
      hs.map' A.val.toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have hK := linearIndependent_of_le_twistedFixed P hP
      (fun i : s => ((i : A) : Matrix n n K)) (fun i => hA (i : A).2) hs'
    have := hK.fintype_card_le_finrank
    rw [Module.finrank_matrix, Module.finrank_self, mul_one] at this
    simpa using this
  change Module.Finite k A
  rw [← Module.rank_lt_aleph0_iff]
  exact lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0

variable (hspan : Submodule.span K (A : Set (Matrix n n K)) = ⊤)

include hspan

/-- `A` is a simple ring. -/
theorem isSimpleRing [Nonempty n] : IsSimpleRing A := by
  have : Nontrivial A := ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  rw [or_iff_not_imp_left]
  intro hI
  let V : Submodule k (Matrix n n K) :=
    { carrier := {x | ∃ a : A, a ∈ I ∧ (a : Matrix n n K) = x}
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, I.add_mem ha hb, rfl⟩
      zero_mem' := ⟨0, I.zero_mem, rfl⟩
      smul_mem' := by
        rintro c _ ⟨a, ha, rfl⟩
        refine ⟨algebraMap k A c * a, I.mul_mem_left _ _ ha, ?_⟩
        rw [← Algebra.smul_def]
        rfl }
  have hVA : (V : Set (Matrix n n K)) ⊆ A := by
    rintro _ ⟨a, _, rfl⟩
    exact a.2
  let J : TwoSidedIdeal (Matrix n n K) := TwoSidedIdeal.mk'
    (Submodule.span K (V : Set (Matrix n n K)) : Set (Matrix n n K))
    (Submodule.zero_mem _) (fun hx hy => Submodule.add_mem _ hx hy)
    (fun hx => Submodule.neg_mem _ hx)
    (fun {x _} hy => mul_mem_span_left A hspan V (by
      rintro a ha _ ⟨b, hb, rfl⟩
      exact ⟨⟨a, ha⟩ * b, I.mul_mem_left _ _ hb, rfl⟩) x hy)
    (fun {_ y} hx => mul_mem_span_right A hspan V (by
      rintro a ha _ ⟨b, hb, rfl⟩
      exact ⟨b * ⟨a, ha⟩, I.mul_mem_right _ _ hb, rfl⟩) y hx)
  obtain ⟨a, haI, ha0⟩ : ∃ a ∈ I, a ≠ 0 := by
    by_contra h
    push Not at h
    apply hI
    ext x
    simp only [TwoSidedIdeal.mem_bot]
    exact ⟨h x, fun hx => hx ▸ I.zero_mem⟩
  have haJ : (a : Matrix n n K) ∈ J := by
    rw [TwoSidedIdeal.mem_mk']
    exact Submodule.subset_span ⟨a, haI, rfl⟩
  have h1J : (1 : Matrix n n K) ∈ J :=
    IsSimpleRing.one_mem_of_ne_zero_mem J (fun h => ha0 (Subtype.ext h)) haJ
  rw [TwoSidedIdeal.mem_mk'] at h1J
  obtain ⟨b, hbI, hb1⟩ := mem_of_mem_span P hP A hA V hVA A.one_mem h1J
  have hb : b = 1 := Subtype.ext hb1
  rw [← TwoSidedIdeal.one_mem_iff, ← hb]
  exact hbI

/-- `A` is central over `k`. -/
theorem isCentral [Nonempty n] : Algebra.IsCentral k A := by
  constructor
  intro z hz
  rw [Subalgebra.mem_center_iff] at hz
  have hzc : ∀ M : Matrix n n K, (z : Matrix n n K) * M = M * z :=
    commute_of_forall_commute A hspan (fun a ha => by
      have := hz ⟨a, ha⟩
      exact (congrArg Subtype.val this).symm)
  have hcen : (z : Matrix n n K) ∈ Set.center (Matrix n n K) := by
    rw [Semigroup.mem_center_iff]
    intro M
    exact (hzc M).symm
  rw [Matrix.center_eq_scalar_image] at hcen
  obtain ⟨c, -, hc⟩ := hcen
  have hfix : ∀ σ : K ≃ₐ[k] K, σ c = c := by
    intro σ
    have h1 := hA z.2 σ
    rw [← hc] at h1
    have hmap : (Matrix.scalar n c).map σ = Matrix.scalar n (σ c) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    rw [hmap, ← (Matrix.scalar_commute c (fun r => Commute.all c r) (P σ)).eq] at h1
    have h2 : (Matrix.scalar n c - Matrix.scalar n (σ c)) * P σ = 0 := by
      rw [sub_mul, h1, sub_self]
    rw [(hP σ).mul_left_eq_zero, sub_eq_zero] at h2
    obtain ⟨i⟩ := ‹Nonempty n›
    have := congrFun (congrFun h2 i) i
    simpa [Matrix.scalar_apply] using this.symm
  obtain ⟨c₀, hc₀⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed c).mpr hfix
  rw [Algebra.mem_bot]
  refine ⟨c₀, Subtype.ext ?_⟩
  rw [Subalgebra.coe_algebraMap, ← hc, ← hc₀]
  ext i j
  simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

/-- `A` has dimension `n²` over `k`. -/
theorem finrank_eq : Module.finrank k A = Fintype.card n * Fintype.card n := by
  have := finiteDimensional P hP A hA
  let b := Module.finBasis k A
  let v : Fin (Module.finrank k A) → Matrix n n K := fun i => (b i : Matrix n n K)
  have hli : LinearIndependent K v := linearIndependent_of_le_twistedFixed P hP v
    (fun i => hA (b i).2)
    (b.linearIndependent.map' A.val.toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective))
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    have hxb : (⟨x, hx⟩ : A) ∈ Submodule.span k (Set.range b) := by
      rw [b.span_eq]
      exact Submodule.mem_top
    have hxv : x ∈ Submodule.span k (Set.range v) := by
      have := Submodule.apply_mem_span_image_of_mem_span A.val.toLinearMap hxb
      rw [← Set.range_comp] at this
      exact this
    exact Submodule.span_le_restrictScalars k K (Set.range v) hxv
  have hcard := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fin] at hcard
  exact hcard.symm

/-- The fixed algebra as a central simple algebra over `k`. -/
def toCSA [Nonempty n] : CSA.{u, u} k :=
  haveI := finiteDimensional P hP A hA
  haveI := isSimpleRing P hP A hA hspan
  haveI := isCentral P hP A hA hspan
  { toAlgCat := AlgCat.of k A }

theorem toCSA_carrier [Nonempty n] : (toCSA P hP A hA hspan : Type u) = A :=
  rfl

end CentralSimple

end Langlands.Algebra.GaloisTwistedMatrix
