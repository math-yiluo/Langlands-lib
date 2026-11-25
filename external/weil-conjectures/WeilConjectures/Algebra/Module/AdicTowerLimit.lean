/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.CofilteredSystem
public import WeilConjectures.Mathlib.RingTheory.AdicCompletion.Functoriality
public import WeilConjectures.Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Limits of towers of finite modules with `ℓ`-adic long exact sequences

Let `(Mₙ)` and `(M'ₙ)` be towers of finite `R`-modules (think `Mₙ = Hʲ(X, Fₙ)` and
`M'ₙ = Hʲ⁺¹(X, Fₙ)` for an `ℓ`-adic tower `(Fₙ)` of sheaves) equipped, for all `n` and `m`, with
pieces of long exact sequences
`Mₙ ⟶ Mₙ₊ₘ ⟶ Mₘ ⟶ M'ₙ ⟶ M'ₙ₊ₘ`
(the cohomology sequences of `0 ⟶ Fₙ ⟶ Fₙ₊ₘ ⟶ Fₘ ⟶ 0`), natural in `n`, whose first map
composed with the transition map is multiplication by `ℓᵐ`. Let `L = lim Mₙ` and `L' = lim M'ₙ`.
Passing to the limit in `n`, which is exact on towers of finite modules by Kőnig's lemma
(`CategoryTheory.Functor.exists_mem_sections_of_finite`), gives the exact sequences
`0 ⟶ L/ℓᵐL ⟶ Mₘ ⟶ L'[ℓᵐ] ⟶ 0`:

- `ModuleCat.AdicTowerSequence.eval_eq_zero_iff`: the kernel of `L ⟶ Mₘ` is `ℓᵐL`;
- `ModuleCat.AdicTowerSequence.exists_eval_eq_iff`: the image of `L ⟶ Mₘ` is the kernel of
  `δ : Mₘ ⟶ L'`;
- `ModuleCat.AdicTowerSequence.exists_limδ_eq_iff`: the image of `δ` is the `ℓᵐ`-torsion of `L'`.

If the `ℓ`-power torsion of `L'` is killed by `ℓᶜ`, the image of `Mₘ₊꜀ ⟶ Mₘ` is contained in
the image of `L` (`ModuleCat.AdicTowerSequence.exists_eval_eq_towerMap`): the tower `(Mₘ)` is
then Artin-Rees isomorphic to `(L/ℓᵐL)`. When `R` is noetherian and `ℓ`-adically precomplete,
`L` and `L'` are finitely generated (`ModuleCat.AdicTowerSequence.module_finite`, using
`Module.Finite.of_isHausdorff_span_singleton`), so such a `c` exists
(`ModuleCat.AdicTowerSequence.exists_pow_smul_eq_zero_of_pow_smul_eq_zero`); the result is
`ModuleCat.AdicTowerSequence.exists_artinRees`.
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

namespace CategoryTheory.Functor

/-- **Kőnig's lemma for subsets of a tower of finite types.** Let `A` be a tower of finite types
and `P n ⊆ Aₙ` nonempty subsets which are preserved by the transition maps. Then there is a
compatible family `(xₙ)` with `xₙ ∈ P n` for all `n`. -/
theorem exists_mem_sections_of_finite (A : ℕᵒᵖ ⥤ Type w) [∀ n, Finite (A.obj n)]
    (P : ∀ n : ℕ, Set (A.obj (op n))) (hP : ∀ n, (P n).Nonempty)
    (hmap : ∀ {n k : ℕ} (h : n ≤ k), ∀ x ∈ P k, A.map (homOfLE h).op x ∈ P n) :
    ∃ x : ∀ n, A.obj n, x ∈ A.sections ∧ ∀ n : ℕ, x (op n) ∈ P n := by
  let B : ℕᵒᵖ ⥤ Type w :=
    { obj n := P n.unop
      map {n k} f := TypeCat.ofHom fun x ↦ ⟨A.map f x.1, by
        have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
        rw [hf]
        exact hmap _ x.1 x.2⟩
      map_id n := by
        ext x
        simp
      map_comp f g := by
        ext x
        simp }
  have (n : ℕᵒᵖ) : Nonempty (B.obj n) := (hP n.unop).to_subtype
  obtain ⟨x, hx⟩ := nonempty_sections_of_finite_inverse_system B
  refine ⟨fun n ↦ (x n).1, fun {n k} f ↦ congrArg Subtype.val (hx f), fun n ↦ (x (op n)).2⟩

end CategoryTheory.Functor

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The transition map `Mₖ ⟶ Mₙ`, `n ≤ k`, of a tower of modules, as a linear map. -/
abbrev towerMap (M : ℕᵒᵖ ⥤ ModuleCat.{v} R) {n k : ℕ} (h : n ≤ k) :
    M.obj (op k) →ₗ[R] M.obj (op n) :=
  (M.map (homOfLE h).op).hom

@[simp]
lemma towerMap_towerMap (M : ℕᵒᵖ ⥤ ModuleCat.{v} R) {n k p : ℕ} (h : n ≤ k) (h' : k ≤ p)
    (x : M.obj (op p)) :
    towerMap M h (towerMap M h' x) = towerMap M (h.trans h') x := by
  rw [towerMap, towerMap, towerMap, ← ModuleCat.comp_apply, ← M.map_comp]
  rfl

@[simp]
lemma towerMap_refl (M : ℕᵒᵖ ⥤ ModuleCat.{v} R) (n : ℕ) (x : M.obj (op n)) :
    towerMap M (le_refl n) x = x := by
  have : M.map (homOfLE (le_refl n)).op = 𝟙 _ := M.map_id _
  rw [towerMap, this]
  rfl

lemma mem_sectionsSubmodule_iff (M : ℕᵒᵖ ⥤ ModuleCat.{v} R) (x : ∀ n, M.obj n) :
    x ∈ sectionsSubmodule M ↔ ∀ {n k : ℕ} (h : n ≤ k), towerMap M h (x (op k)) = x (op n) := by
  refine ⟨fun hx n k h ↦ hx (homOfLE h).op, fun hx n k f ↦ ?_⟩
  have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
  rw [hf]
  exact hx _

/-- A compatible family of a tower is determined by its terms of large index. -/
lemma sectionsSubmodule_ext {M : ℕᵒᵖ ⥤ ModuleCat.{v} R} {x y : sectionsSubmodule M} (c : ℕ)
    (h : ∀ n, x.1 (op (n + c)) = y.1 (op (n + c))) : x = y := by
  refine Subtype.ext (funext fun n ↦ ?_)
  rw [← (mem_sectionsSubmodule_iff M _).1 x.2 (Nat.le_add_right n.unop c),
    ← (mem_sectionsSubmodule_iff M _).1 y.2 (Nat.le_add_right n.unop c), h]

end ModuleCat

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The projection `lim Mₙ ⟶ Mₘ` from the module of compatible families of a tower. -/
def sectionsEval (M : ℕᵒᵖ ⥤ ModuleCat.{v} R) (m : ℕ) :
    sectionsSubmodule M →ₗ[R] M.obj (op m) :=
  (LinearMap.proj (op m)).comp (sectionsSubmodule M).subtype

@[simp]
lemma sectionsEval_apply (M : ℕᵒᵖ ⥤ ModuleCat.{v} R) (m : ℕ) (x : sectionsSubmodule M) :
    sectionsEval M m x = x.1 (op m) :=
  rfl

/-- **`ℓ`-adic long exact sequences for a pair of towers.** For towers `M` and `M'` of
`R`-modules (`Mₙ = Hʲ(Fₙ)`, `M'ₙ = Hʲ⁺¹(Fₙ)` for an `ℓ`-adic tower `(Fₙ)`), the data of the
pieces `Mₙ ⟶ Mₙ₊ₘ ⟶ Mₘ ⟶ M'ₙ ⟶ M'ₙ₊ₘ ⟶ M'ₘ` of the long exact cohomology sequences of the short
exact sequences `0 ⟶ Fₙ ⟶ Fₙ₊ₘ ⟶ Fₘ ⟶ 0` (whose first map is induced by multiplication by
`ℓᵐ` and whose second map is the transition map), natural in `n`, and natural in `m` in the sense
of `δ_towerMap` (the morphism of short exact sequences from `(n, m + c)` to `(n + c, m)`). -/
structure AdicTowerSequence (ℓ : ℕ) (M M' : ℕᵒᵖ ⥤ ModuleCat.{v} R) where
  /-- The map `Mₙ ⟶ Mₙ₊ₘ` induced by `Fₙ ⟶ Fₙ₊ₘ`. -/
  a (n m : ℕ) : M.obj (op n) →ₗ[R] M.obj (op (n + m))
  /-- The map `M'ₙ ⟶ M'ₙ₊ₘ` induced by `Fₙ ⟶ Fₙ₊ₘ`. -/
  a' (n m : ℕ) : M'.obj (op n) →ₗ[R] M'.obj (op (n + m))
  /-- The connecting map `Mₘ ⟶ M'ₙ`. -/
  δ (n m : ℕ) : M.obj (op m) →ₗ[R] M'.obj (op n)
  towerMap_a (n m : ℕ) (x : M.obj (op n)) :
    towerMap M (Nat.le_add_right n m) (a n m x) = ℓ ^ m • x
  a_towerMap {n k : ℕ} (m : ℕ) (h : n ≤ k) (x : M.obj (op k)) :
    a n m (towerMap M h x) = towerMap M (Nat.add_le_add_right h m) (a k m x)
  towerMap_a' (n m : ℕ) (x : M'.obj (op n)) :
    towerMap M' (Nat.le_add_right n m) (a' n m x) = ℓ ^ m • x
  a'_towerMap_self (n m : ℕ) (x : M'.obj (op (n + m))) :
    a' n m (towerMap M' (Nat.le_add_right n m) x) = ℓ ^ m • x
  a'_towerMap {n k : ℕ} (m : ℕ) (h : n ≤ k) (x : M'.obj (op k)) :
    a' n m (towerMap M' h x) = towerMap M' (Nat.add_le_add_right h m) (a' k m x)
  towerMap_δ {n k : ℕ} (m : ℕ) (h : n ≤ k) (z : M.obj (op m)) :
    towerMap M' h (δ k m z) = δ n m z
  δ_towerMap (n m c : ℕ) (z : M.obj (op (m + c))) :
    δ (n + c) m (towerMap M (Nat.le_add_right m c) z) = a' n c (δ n (m + c) z)
  exact_a (n m : ℕ) (y : M.obj (op (n + m))) :
    towerMap M (Nat.le_add_left m n) y = 0 ↔ ∃ x, a n m x = y
  exact_δ (n m : ℕ) (z : M.obj (op m)) :
    δ n m z = 0 ↔ ∃ y, towerMap M (Nat.le_add_left m n) y = z
  exact_a' (n m : ℕ) (y : M'.obj (op n)) :
    a' n m y = 0 ↔ ∃ z, δ n m z = y
  exact_a'_towerMap (n m : ℕ) (y : M'.obj (op (n + m))) :
    towerMap M' (Nat.le_add_left m n) y = 0 ↔ ∃ x, a' n m x = y

namespace AdicTowerSequence

variable {ℓ : ℕ} {M M' : ℕᵒᵖ ⥤ ModuleCat.{v} R}

/-- The connecting map `Mₘ ⟶ lim M'ₙ` of the limit sequence. -/
def limδ (S : AdicTowerSequence ℓ M M') (m : ℕ) : M.obj (op m) →ₗ[R] sectionsSubmodule M' :=
  LinearMap.codRestrict _ (LinearMap.pi fun n : ℕᵒᵖ ↦ S.δ n.unop m) fun z ↦
    (mem_sectionsSubmodule_iff M' _).2 fun h ↦ S.towerMap_δ _ h z

@[simp]
lemma limδ_apply_coe (S : AdicTowerSequence ℓ M M') (m : ℕ) (z : M.obj (op m)) (n : ℕ) :
    (S.limδ m z).1 (op n) = S.δ n m z :=
  rfl

end AdicTowerSequence

section

variable {ℓ : ℕ} {M : ℕᵒᵖ ⥤ ModuleCat.{v} R}

/-- A tower `M` with maps `aₙₘ : Mₙ ⟶ Mₙ₊ₘ` such that `Mₙ ⟶ Mₙ₊ₘ ⟶ Mₘ` is exact and `aₙₘ`
followed by the transition map is `ℓᵐ` has `ℓᵐ Mₘ = 0`. -/
lemma pow_smul_eq_zero_of_exact (a : ∀ n m, M.obj (op n) →ₗ[R] M.obj (op (n + m)))
    (towerMap_a : ∀ n m x, towerMap M (Nat.le_add_right n m) (a n m x) = ℓ ^ m • x)
    (exact_a : ∀ n m (y : M.obj (op (n + m))),
      towerMap M (Nat.le_add_left m n) y = 0 ↔ ∃ x, a n m x = y)
    (m : ℕ) (x : M.obj (op m)) :
    ℓ ^ m • x = 0 := by
  rw [← towerMap_a m m x]
  exact (exact_a m m _).2 ⟨x, rfl⟩

/-- **The kernel of `lim Mₙ ⟶ Mₘ` is `ℓᵐ lim Mₙ`** for a tower of finite modules `M` with maps
`aₙₘ : Mₙ ⟶ Mₙ₊ₘ`, natural in `n`, such that `Mₙ ⟶ Mₙ₊ₘ ⟶ Mₘ` is exact and `aₙₘ` followed by the
transition map is `ℓᵐ`. -/
theorem sectionsEval_eq_zero_iff [∀ n, Finite (M.obj n)]
    (a : ∀ n m, M.obj (op n) →ₗ[R] M.obj (op (n + m)))
    (towerMap_a : ∀ n m x, towerMap M (Nat.le_add_right n m) (a n m x) = ℓ ^ m • x)
    (a_towerMap : ∀ {n k : ℕ} (m : ℕ) (h : n ≤ k) (x : M.obj (op k)),
      a n m (towerMap M h x) = towerMap M (Nat.add_le_add_right h m) (a k m x))
    (exact_a : ∀ n m (y : M.obj (op (n + m))),
      towerMap M (Nat.le_add_left m n) y = 0 ↔ ∃ x, a n m x = y)
    (m : ℕ) (x : sectionsSubmodule M) :
    x.1 (op m) = 0 ↔ ∃ y : sectionsSubmodule M, ℓ ^ m • y = x := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have (n : ℕᵒᵖ) : Finite ((M ⋙ forget (ModuleCat R)).obj n) :=
      inferInstanceAs (Finite (M.obj n))
    obtain ⟨y, hy, hyP⟩ := Functor.exists_mem_sections_of_finite (M ⋙ forget (ModuleCat R))
      (fun n ↦ {y | a n m y = x.1 (op (n + m))}) (fun n ↦ (exact_a n m _).1 (by
        rw [(mem_sectionsSubmodule_iff M _).1 x.2, hx])) (fun {n k} h y hy ↦ by
        dsimp at hy ⊢
        rw [a_towerMap m h, hy, (mem_sectionsSubmodule_iff M _).1 x.2])
    refine ⟨⟨y, hy⟩, Subtype.ext (funext fun n ↦ ?_)⟩
    dsimp
    rw [← towerMap_a n.unop m, hyP n.unop, (mem_sectionsSubmodule_iff M _).1 x.2]
  · rintro ⟨y, rfl⟩
    exact pow_smul_eq_zero_of_exact a towerMap_a exact_a m _


/-- In the situation of `ModuleCat.sectionsEval_eq_zero_iff`, an element of `lim Mₙ` lies in
`(ℓ)ᵐ lim Mₙ` if and only if its component in `Mₘ` vanishes. -/
lemma mem_pow_smul_top_iff_of_exact [∀ n, Finite (M.obj n)]
    (a : ∀ n m, M.obj (op n) →ₗ[R] M.obj (op (n + m)))
    (towerMap_a : ∀ n m x, towerMap M (Nat.le_add_right n m) (a n m x) = ℓ ^ m • x)
    (a_towerMap : ∀ {n k : ℕ} (m : ℕ) (h : n ≤ k) (x : M.obj (op k)),
      a n m (towerMap M h x) = towerMap M (Nat.add_le_add_right h m) (a k m x))
    (exact_a : ∀ n m (y : M.obj (op (n + m))),
      towerMap M (Nat.le_add_left m n) y = 0 ↔ ∃ x, a n m x = y)
    (m : ℕ) (x : sectionsSubmodule M) :
    x ∈ (Ideal.span {(ℓ : R)}) ^ m • (⊤ : Submodule R (sectionsSubmodule M)) ↔
      x.1 (op m) = 0 := by
  simp_rw [Submodule.mem_span_singleton_pow_smul_top_iff,
    sectionsEval_eq_zero_iff a towerMap_a a_towerMap exact_a, ← Nat.cast_pow,
    Nat.cast_smul_eq_nsmul]

/-- **`lim Mₙ` is finitely generated** in the situation of `ModuleCat.sectionsEval_eq_zero_iff`,
when `R` is `ℓ`-adically precomplete: `lim Mₙ` is `ℓ`-adically separated with
`lim Mₙ / ℓ ⊆ M₁` finite (`Module.Finite.of_isHausdorff_span_singleton`). -/
theorem module_finite_sectionsSubmodule_of_exact [∀ n, Finite (M.obj n)]
    [IsPrecomplete (Ideal.span {(ℓ : R)}) R]
    (a : ∀ n m, M.obj (op n) →ₗ[R] M.obj (op (n + m)))
    (towerMap_a : ∀ n m x, towerMap M (Nat.le_add_right n m) (a n m x) = ℓ ^ m • x)
    (a_towerMap : ∀ {n k : ℕ} (m : ℕ) (h : n ≤ k) (x : M.obj (op k)),
      a n m (towerMap M h x) = towerMap M (Nat.add_le_add_right h m) (a k m x))
    (exact_a : ∀ n m (y : M.obj (op (n + m))),
      towerMap M (Nat.le_add_left m n) y = 0 ↔ ∃ x, a n m x = y) :
    Module.Finite R (sectionsSubmodule M) := by
  have hmem := mem_pow_smul_top_iff_of_exact a towerMap_a a_towerMap exact_a
  have : IsHausdorff (Ideal.span {(ℓ : R)}) (sectionsSubmodule M) := ⟨fun x hx ↦
    Subtype.ext (funext fun ⟨n⟩ ↦ (hmem n x).1 (by simpa using SModEq.sub_mem.1 (hx n)))⟩
  have : Finite (sectionsSubmodule M ⧸
      (Ideal.span {(ℓ : R)} • ⊤ : Submodule R (sectionsSubmodule M))) := by
    have hle : (Ideal.span {(ℓ : R)} • ⊤ : Submodule R (sectionsSubmodule M)) ≤
        LinearMap.ker (sectionsEval M 1) := fun x hx ↦ (hmem 1 x).1 (by rwa [pow_one])
    refine Finite.of_injective _ (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ hle
      fun x hx ↦ ?_))
    rw [← pow_one (Ideal.span {(ℓ : R)}), hmem]
    exact hx
  exact Module.Finite.of_isHausdorff_span_singleton (ℓ : R)
end

namespace AdicTowerSequence

variable {ℓ : ℕ} {M M' : ℕᵒᵖ ⥤ ModuleCat.{v} R}

/-- `ℓᵐ` kills `Mₘ`. -/
lemma pow_smul_eq_zero (S : AdicTowerSequence ℓ M M') (m : ℕ) (x : M.obj (op m)) :
    ℓ ^ m • x = 0 :=
  pow_smul_eq_zero_of_exact S.a S.towerMap_a S.exact_a m x

/-- **The kernel of `lim Mₙ ⟶ Mₘ` is `ℓᵐ lim Mₙ`** for a tower of finite modules. -/
theorem eval_eq_zero_iff (S : AdicTowerSequence ℓ M M') [∀ n, Finite (M.obj n)] (m : ℕ)
    (x : sectionsSubmodule M) :
    x.1 (op m) = 0 ↔ ∃ y : sectionsSubmodule M, ℓ ^ m • y = x :=
  sectionsEval_eq_zero_iff S.a S.towerMap_a S.a_towerMap S.exact_a m x

/-- **The kernel of `lim M'ₙ ⟶ M'ₘ` is `ℓᵐ lim M'ₙ`** for a tower of finite modules. -/
theorem eval'_eq_zero_iff (S : AdicTowerSequence ℓ M M') [∀ n, Finite (M'.obj n)] (m : ℕ)
    (x : sectionsSubmodule M') :
    x.1 (op m) = 0 ↔ ∃ y : sectionsSubmodule M', ℓ ^ m • y = x :=
  sectionsEval_eq_zero_iff S.a' S.towerMap_a' S.a'_towerMap S.exact_a'_towerMap m x

/-- **The image of `lim Mₙ ⟶ Mₘ` is the kernel of the connecting map `Mₘ ⟶ lim M'ₙ`** for a
tower of finite modules. -/
theorem exists_eval_eq_iff (S : AdicTowerSequence ℓ M M') [∀ n, Finite (M.obj n)] (m : ℕ)
    (z : M.obj (op m)) :
    (∃ x : sectionsSubmodule M, x.1 (op m) = z) ↔ S.limδ m z = 0 := by
  refine ⟨?_, fun hz ↦ ?_⟩
  · rintro ⟨x, rfl⟩
    refine Subtype.ext (funext fun n ↦ (S.exact_δ n.unop m _).2 ⟨x.1 (op (n.unop + m)), ?_⟩)
    exact (mem_sectionsSubmodule_iff M _).1 x.2 _
  · have (n : ℕᵒᵖ) : Finite ((M ⋙ forget (ModuleCat R)).obj n) :=
      inferInstanceAs (Finite (M.obj n))
    obtain ⟨x, hx, hxP⟩ := Functor.exists_mem_sections_of_finite (M ⋙ forget (ModuleCat R))
      (fun n ↦ {w | ∃ v : M.obj (op (n + m)), towerMap M (Nat.le_add_left m n) v = z ∧
        towerMap M (Nat.le_add_right n m) v = w})
      (fun n ↦ by
        obtain ⟨v, hv⟩ := (S.exact_δ n m z).1 (congrArg (fun y ↦ y.1 (op n)) hz)
        exact ⟨_, v, hv, rfl⟩)
      (fun {n k} h w ⟨v, hv, hvw⟩ ↦ ⟨towerMap M (Nat.add_le_add_right h m) v, by
        rw [towerMap_towerMap]
        exact hv, by
        dsimp
        rw [← hvw, towerMap_towerMap, towerMap_towerMap]⟩)
    obtain ⟨v, hv, hvx⟩ := hxP m
    exact ⟨⟨x, hx⟩, hvx.symm.trans hv⟩

/-- **The image of the connecting map `Mₘ ⟶ lim M'ₙ` is the `ℓᵐ`-torsion of `lim M'ₙ`** for a
tower of finite modules. -/
theorem exists_limδ_eq_iff (S : AdicTowerSequence ℓ M M') [∀ n, Finite (M.obj n)] (m : ℕ)
    (y : sectionsSubmodule M') :
    (∃ z, S.limδ m z = y) ↔ ℓ ^ m • y = 0 := by
  refine ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨z, rfl⟩
    refine Subtype.ext (funext fun ⟨n⟩ ↦ ?_)
    rw [AddSubmonoidClass.coe_nsmul, Pi.smul_apply, limδ_apply_coe, ← S.towerMap_a' n m,
      (S.exact_a' n m _).2 ⟨z, rfl⟩, map_zero]
    rfl
  · let A := (Functor.const ℕᵒᵖ).obj (M.obj (op m) : Type v)
    have (n : ℕᵒᵖ) : Finite (A.obj n) := inferInstanceAs (Finite (M.obj (op m)))
    obtain ⟨x, hx, hxP⟩ := Functor.exists_mem_sections_of_finite A
      (fun n ↦ {z | S.δ n m z = y.1 (op n)})
      (fun n ↦ (S.exact_a' n m _).1 (by
        rw [← (mem_sectionsSubmodule_iff M' _).1 y.2 (Nat.le_add_right n m), S.a'_towerMap_self]
        exact congrArg (fun w : sectionsSubmodule M' ↦ w.1 (op (n + m))) hy))
      (fun {n k} h z hz ↦ by
        refine (S.towerMap_δ m h z).symm.trans ?_
        rw [hz]
        exact (mem_sectionsSubmodule_iff M' _).1 y.2 h)
    refine ⟨x (op 0), Subtype.ext (funext fun n ↦ ?_)⟩
    have hxn : x n = x (op 0) := hx (homOfLE (Nat.zero_le n.unop)).op
    rw [← hxn]
    exact hxP n.unop

/-- **Naturality of the limit connecting maps in `m`**: `δₘ ∘ (Mₘ₊꜀ ⟶ Mₘ) = ℓᶜ δₘ₊꜀`. -/
lemma limδ_towerMap (S : AdicTowerSequence ℓ M M') (m c : ℕ) (z : M.obj (op (m + c))) :
    S.limδ m (towerMap M (Nat.le_add_right m c) z) = ℓ ^ c • S.limδ (m + c) z := by
  refine sectionsSubmodule_ext c fun n ↦ ?_
  rw [limδ_apply_coe, S.δ_towerMap, ← S.towerMap_δ (m + c) (Nat.le_add_right n c),
    S.a'_towerMap_self]
  rfl

/-- **Uniform Mittag-Leffler property.** If the `ℓ`-power torsion of `lim M'ₙ` is killed by `ℓᶜ`,
then the image of `Mₘ₊꜀ ⟶ Mₘ` is contained in the image of `lim Mₙ ⟶ Mₘ`. Together with
`ModuleCat.AdicTowerSequence.eval_eq_zero_iff`, this says that `(Mₘ)ₘ` is Artin-Rees isomorphic
to `(lim Mₙ / ℓᵐ)ₘ`. -/
theorem exists_eval_eq_towerMap (S : AdicTowerSequence ℓ M M') [∀ n, Finite (M.obj n)] (c : ℕ)
    (hc : ∀ (y : sectionsSubmodule M') (k : ℕ), ℓ ^ k • y = 0 → ℓ ^ c • y = 0) (m : ℕ)
    (z : M.obj (op (m + c))) :
    ∃ x : sectionsSubmodule M, x.1 (op m) = towerMap M (Nat.le_add_right m c) z := by
  rw [S.exists_eval_eq_iff, S.limδ_towerMap]
  exact hc _ (m + c) ((S.exists_limδ_eq_iff (m + c) _).1 ⟨z, rfl⟩)

/-- `ℓᵐ` kills `M'ₘ`. -/
lemma pow_smul_eq_zero' (S : AdicTowerSequence ℓ M M') (m : ℕ) (x : M'.obj (op m)) :
    ℓ ^ m • x = 0 :=
  pow_smul_eq_zero_of_exact S.a' S.towerMap_a' S.exact_a'_towerMap m x

/-- **`lim Mₙ` is finitely generated** when `R` is `ℓ`-adically precomplete. -/
theorem module_finite (S : AdicTowerSequence ℓ M M') [∀ n, Finite (M.obj n)]
    [IsPrecomplete (Ideal.span {(ℓ : R)}) R] :
    Module.Finite R (sectionsSubmodule M) :=
  module_finite_sectionsSubmodule_of_exact S.a S.towerMap_a S.a_towerMap S.exact_a

/-- **`lim M'ₙ` is finitely generated** when `R` is `ℓ`-adically precomplete. -/
theorem module_finite' (S : AdicTowerSequence ℓ M M') [∀ n, Finite (M'.obj n)]
    [IsPrecomplete (Ideal.span {(ℓ : R)}) R] :
    Module.Finite R (sectionsSubmodule M') :=
  module_finite_sectionsSubmodule_of_exact S.a' S.towerMap_a' S.a'_towerMap S.exact_a'_towerMap

/-- **The `ℓ`-power torsion of `lim M'ₙ` is bounded** when `R` is noetherian and
`ℓ`-adically precomplete: `lim M'ₙ` is finitely generated
(`ModuleCat.AdicTowerSequence.module_finite'`), hence noetherian. -/
theorem exists_pow_smul_eq_zero_of_pow_smul_eq_zero (S : AdicTowerSequence ℓ M M')
    [∀ n, Finite (M'.obj n)] [IsNoetherianRing R] [IsPrecomplete (Ideal.span {(ℓ : R)}) R] :
    ∃ c : ℕ, ∀ (y : sectionsSubmodule M') (k : ℕ), ℓ ^ k • y = 0 → ℓ ^ c • y = 0 := by
  have := S.module_finite'
  obtain ⟨c, hc⟩ := IsNoetherian.exists_pow_smul_eq_zero_of_pow_smul_eq_zero
    (R := R) (N := sectionsSubmodule M') (ℓ : R)
  refine ⟨c, fun y k hk ↦ ?_⟩
  have := hc y k
  simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this
  exact this hk

/-- **`(Mₘ)ₘ` is Artin-Rees isomorphic to `(lim Mₙ / ℓᵐ)ₘ`** when `R` is noetherian and
`ℓ`-adically precomplete: `lim Mₙ` is finitely generated, and there is `c` such that for every
`m` the kernel of `lim Mₙ ⟶ Mₘ` is `ℓᵐ lim Mₙ` and the image of `Mₘ₊꜀ ⟶ Mₘ` is contained in the
image of `lim Mₙ ⟶ Mₘ`. In other words, `lim Mₙ / ℓᵐ ⟶ Mₘ` is injective and `Mₘ₊꜀ ⟶ Mₘ`
factors through it. -/
theorem exists_artinRees (S : AdicTowerSequence ℓ M M') [∀ n, Finite (M.obj n)]
    [∀ n, Finite (M'.obj n)] [IsNoetherianRing R] [IsPrecomplete (Ideal.span {(ℓ : R)}) R] :
    Module.Finite R (sectionsSubmodule M) ∧ ∃ c : ℕ, ∀ m : ℕ,
      (∀ x : sectionsSubmodule M, x.1 (op m) = 0 ↔ ∃ y : sectionsSubmodule M, ℓ ^ m • y = x) ∧
      ∀ z : M.obj (op (m + c)),
        ∃ x : sectionsSubmodule M, x.1 (op m) = towerMap M (Nat.le_add_right m c) z := by
  obtain ⟨c, hc⟩ := S.exists_pow_smul_eq_zero_of_pow_smul_eq_zero
  exact ⟨S.module_finite, c, fun m ↦ ⟨S.eval_eq_zero_iff m, S.exists_eval_eq_towerMap c hc m⟩⟩

end AdicTowerSequence

end ModuleCat
