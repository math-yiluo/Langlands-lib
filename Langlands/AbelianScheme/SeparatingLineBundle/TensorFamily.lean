import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingProof

/-!
# Finite tensor products of line-bundle sections

A finite family of line bundles indexed by `Fin n` is multiplied into one line bundle,
starting from the trivial line bundle, and a family of sections into the product section.
A point lies in the trivialization open of the product section exactly when it lies in
every factor's trivialization open. Hence the product section vanishes at a field-valued
point exactly when some factor does. Along an arbitrary morphism whose image avoids the
zero loci of all but one factor, the product section vanishes exactly when that factor
does.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.GroupScheme.SeparatingLineBundle

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The tensor product of two line bundles, using the proved pullback comparison. -/
abbrev tensorLB (L M : LineBundle X) : LineBundle X :=
  LineBundle.tensor pullbackTensorComparisonIsIso L M

/-- The tensor product of a family of line bundles indexed by `Fin n`, starting from the
trivial line bundle. -/
def famBundle : (n : ℕ) → (Fin n → LineBundle X) → LineBundle X
  | 0, _ => LineBundle.trivial X
  | n + 1, N => tensorLB (N 0) (famBundle n (Fin.tail N))

/-- The product of a family of sections, starting from the unit section. -/
def famSection : (n : ℕ) → (N : Fin n → LineBundle X) →
    ((i : Fin n) → GlobalSections (N i).obj) → GlobalSections (famBundle n N).obj
  | 0, _, _ => (1 : Γ(X, ⊤))
  | n + 1, N, σ => tensorSection (N 0).obj (famBundle n (Fin.tail N)).obj (σ 0)
      (famSection n (Fin.tail N) (fun i ↦ σ i.succ))

/-- A point lies in the trivialization open of the product section exactly when it lies in
the trivialization open of every factor. -/
theorem mem_trivializationOpen_famSection_iff : ∀ (n : ℕ) (N : Fin n → LineBundle X)
    (σ : (i : Fin n) → GlobalSections (N i).obj) (x : X),
    x ∈ trivializationOpen (famBundle n N).obj (famSection n N σ) ↔
      ∀ i, x ∈ trivializationOpen (N i).obj (σ i)
  | 0, N, σ, x => by
    change x ∈ trivializationOpen (LineBundle.trivial X).obj (1 : Γ(X, ⊤)) ↔ _
    rw [trivializationOpen_one]
    exact ⟨fun _ i ↦ i.elim0, fun _ ↦ trivial⟩
  | n + 1, N, σ, x => by
    change x ∈ trivializationOpen (tensorObj (N 0).obj (famBundle n (Fin.tail N)).obj)
      (tensorSection (N 0).obj (famBundle n (Fin.tail N)).obj (σ 0)
        (famSection n (Fin.tail N) (fun i ↦ σ i.succ))) ↔ _
    rw [tensorSectionGenerationLocus X (N 0) (famBundle n (Fin.tail N)), Opens.mem_inf,
      mem_trivializationOpen_famSection_iff n (Fin.tail N) (fun i ↦ σ i.succ) x,
      Fin.forall_fin_succ]
    rfl

/-- At a field-valued point, the product section vanishes exactly when some factor does. -/
theorem vanishesAlong_famSection_field_iff {K : Type u} [Field K] (n : ℕ)
    (N : Fin n → LineBundle X) (σ : (i : Fin n) → GlobalSections (N i).obj)
    (x : Spec (CommRingCat.of K) ⟶ X) :
    VanishesAlong (famBundle n N) x (famSection n N σ) ↔
      ∃ i, VanishesAlong (N i) x (σ i) := by
  rw [vanishesAlong_field_iff _ x _ (IsLocalRing.closedPoint K),
    mem_trivializationOpen_famSection_iff, not_forall]
  simp only [vanishesAlong_field_iff (N _) x _ (IsLocalRing.closedPoint K)]

/-- If every factor but the `j`-th generates along the whole source of `f`, the product
section vanishes along `f` exactly when the `j`-th factor does. -/
theorem vanishesAlong_famSection_iff_of_mem : ∀ (n : ℕ) (N : Fin n → LineBundle X)
    (σ : (i : Fin n) → GlobalSections (N i).obj) (f : Y ⟶ X) (j : Fin n),
    (∀ i, i ≠ j → ∀ y, f y ∈ trivializationOpen (N i).obj (σ i)) →
      (VanishesAlong (famBundle n N) f (famSection n N σ) ↔ VanishesAlong (N j) f (σ j))
  | 0, _, _, _, j, _ => j.elim0
  | n + 1, N, σ, f, j, h => by
    change VanishesAlong (tensorLB (N 0) (famBundle n (Fin.tail N))) f
      (tensorSection (N 0).obj (famBundle n (Fin.tail N)).obj (σ 0)
        (famSection n (Fin.tail N) (fun i ↦ σ i.succ))) ↔ _
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · refine vanishesAlong_tensor_right_iff _ _ _ _ f (fun y ↦ ?_)
      rw [mem_trivializationOpen_famSection_iff]
      exact fun i ↦ h i.succ (Fin.succ_ne_zero i) y
    · rw [vanishesAlong_tensor_left_iff _ _ _ _ f (h 0 (Fin.succ_ne_zero k).symm)]
      exact vanishesAlong_famSection_iff_of_mem n (Fin.tail N) (fun i ↦ σ i.succ) f k
        (fun i hi y ↦ h i.succ (fun e ↦ hi (Fin.succ_injective _ e)) y)

end Langlands.GroupScheme.SeparatingLineBundle
