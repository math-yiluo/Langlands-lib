import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

/-!
# The type `A` root system over `ℚ`, transported along an injective linear map

Let `V` be a `ℚ`-vector space with an injective linear map `Φ : V → (n → ℚ)` and vectors
`r p ∈ V`, for ordered pairs `p = (i, j)` of distinct indices, with `Φ (r p) = eᵢ - eⱼ`.
If the `r p` span `V`, they are the roots of a root system of type `A` (Milne, *Algebraic
Groups*, Example C.16) for the evaluation pairing of `V` with its dual. Its reflections act
on `Φ`-coordinates by transpositions, and the image of its Weyl group in `GL(V)` is the group
of automorphisms of `V` acting on `Φ`-coordinates by a permutation (Milne, C.25).
-/

noncomputable section

open Module Set Function

namespace Langlands.LinearAlgebra.RootSystemTypeA

variable {n : Type*} [DecidableEq n]

/-- The vector `eᵢ - eⱼ` of `n → ℚ`. -/
def rootVec (i j : n) : n → ℚ := Pi.single i 1 - Pi.single j 1

theorem rootVec_apply (i j m : n) :
    rootVec i j m = (if m = i then 1 else 0) - (if m = j then 1 else 0) := by
  simp [rootVec, Pi.single_apply]

/-- Swapping two coordinates is the reflection in `eᵢ - eⱼ`. -/
theorem comp_swap_eq (v : n → ℚ) (i j : n) :
    v ∘ Equiv.swap i j = v - (v i - v j) • rootVec i j := by
  ext m
  simp only [comp_apply, Pi.sub_apply, Pi.smul_apply, rootVec_apply, smul_eq_mul]
  by_cases hi : m = i
  · subst hi
    by_cases hij : m = j
    · subst hij
      simp
    · simp [hij, Equiv.swap_apply_left]
  · by_cases hj : m = j
    · subst hj
      simp [hi, Equiv.swap_apply_right]
    · simp [hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj]

theorem rootVec_comp_perm (σ : Equiv.Perm n) (i j : n) :
    rootVec i j ∘ σ = rootVec (σ.symm i) (σ.symm j) := by
  ext m
  simp only [comp_apply, rootVec_apply, Equiv.eq_symm_apply]

theorem rootVec_injective {i j k l : n} (hij : i ≠ j) (h : rootVec i j = rootVec k l) :
    i = k ∧ j = l := by
  have hi := congrFun h i
  have hj := congrFun h j
  simp only [rootVec_apply, hij, Ne.symm hij, ↓reduceIte] at hi hj
  by_cases hik : i = k
  · subst hik
    refine ⟨rfl, ?_⟩
    by_contra hjl
    norm_num [Ne.symm hij, hjl] at hj
  · exfalso
    by_cases hil : i = l
    · subst hil
      norm_num [hik] at hi
    · norm_num [hik, hil] at hi

/-- A permutation fixing every vector `eᵢ - eⱼ` is the identity. -/
theorem perm_eq_one_of_rootVec_comp (σ : Equiv.Perm n)
    (h : ∀ i j : n, i ≠ j → rootVec i j ∘ σ = rootVec i j) : σ = 1 := by
  ext i
  change σ i = i
  by_cases hj : ∃ j, j ≠ i
  · obtain ⟨j, hji⟩ := hj
    have h' := h (σ i) (σ j) (σ.injective.ne (Ne.symm hji))
    rw [rootVec_comp_perm, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h'
    exact ((rootVec_injective (Ne.symm hji) h').1).symm
  · push Not at hj
    exact hj (σ i)

/-- The integer vector `eᵢ - eⱼ` of `n → ℤ`. -/
def rootVecInt (i j : n) : n → ℤ := Pi.single i 1 - Pi.single j 1

theorem rootVec_eq_cast (i j m : n) : rootVec i j m = (rootVecInt i j m : ℚ) := by
  simp only [rootVec_apply, rootVecInt, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> simp

/-- The roots of type `A`, indexed by ordered pairs of distinct indices. -/
abbrev Index (n : Type*) := {p : n × n // p.1 ≠ p.2}

/-- The reflection in `e_{p.1} - e_{p.2}` permutes the roots by swapping indices. -/
def reflIdx (p q : Index n) : Index n :=
  ⟨(Equiv.swap p.1.1 p.1.2 q.1.1, Equiv.swap p.1.1 p.1.2 q.1.2),
    fun h => q.2 ((Equiv.swap p.1.1 p.1.2).injective h)⟩

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (Φ : V →ₗ[ℚ] n → ℚ)

/-- The coroot of `e_{p.1} - e_{p.2}`, read through `Φ`. -/
def corootFun (p : Index n) : Dual ℚ V :=
  (LinearMap.proj (R := ℚ) (φ := fun _ : n => ℚ) p.1.1 - LinearMap.proj p.1.2) ∘ₗ Φ

omit [DecidableEq n] in
theorem corootFun_apply (p : Index n) (x : V) :
    corootFun Φ p x = Φ x p.1.1 - Φ x p.1.2 := rfl

/-- The linear automorphisms of `V` that act on `Φ`-coordinates by a permutation. -/
def permSubgroup : Subgroup (V ≃ₗ[ℚ] V) where
  carrier := {g | ∃ σ : Equiv.Perm n, ∀ x, Φ (g x) = Φ x ∘ σ}
  one_mem' := ⟨1, fun x => rfl⟩
  mul_mem' := by
    rintro g h ⟨σ, hσ⟩ ⟨τ, hτ⟩
    refine ⟨τ * σ, fun x => ?_⟩
    change Φ (g (h x)) = _
    rw [hσ, hτ]
    rfl
  inv_mem' := by
    rintro g ⟨σ, hσ⟩
    refine ⟨σ⁻¹, fun x => ?_⟩
    have h := hσ (g⁻¹ x)
    change Φ (g (g.symm x)) = _ at h
    rw [LinearEquiv.apply_symm_apply] at h
    change Φ (g.symm x) = _
    rw [h]
    ext m
    simp

variable {Φ}

omit [DecidableEq n] in
theorem mem_permSubgroup {g : V ≃ₗ[ℚ] V} :
    g ∈ permSubgroup Φ ↔ ∃ σ : Equiv.Perm n, ∀ x, Φ (g x) = Φ x ∘ σ :=
  Iff.rfl

variable (hΦ : Injective Φ) {r : Index n → V}
  (hr : ∀ p, Φ (r p) = rootVec p.1.1 p.1.2)
include hr

theorem r_injective : Injective r := by
  intro p q h
  have h' := congrArg Φ h
  rw [hr, hr] at h'
  obtain ⟨h1, h2⟩ := rootVec_injective p.2 h'
  exact Subtype.ext (Prod.ext h1 h2)

theorem corootFun_r (p q : Index n) :
    corootFun Φ p (r q) = rootVec q.1.1 q.1.2 p.1.1 - rootVec q.1.1 q.1.2 p.1.2 := by
  rw [corootFun_apply, hr]

theorem corootFun_r_self (p : Index n) : corootFun Φ p (r p) = 2 := by
  rw [corootFun_r hr]
  simp [rootVec_apply, p.2, Ne.symm p.2]
  norm_num

theorem corootFun_injective : Injective (corootFun Φ) := by
  intro p q h
  have h2 := corootFun_r_self hr p
  rw [h, corootFun_r hr] at h2
  simp only [rootVec_apply] at h2
  have e1 : q.1.1 = p.1.1 := by
    by_contra hne
    simp only [hne, ↓reduceIte] at h2
    split_ifs at h2 <;> norm_num at h2
  have e2 : q.1.2 = p.1.2 := by
    by_contra hne
    simp only [hne, ↓reduceIte] at h2
    split_ifs at h2 <;> norm_num at h2
  exact Subtype.ext (Prod.ext e1.symm e2.symm)

/-- The reflection in a root, read through `Φ`, swaps two coordinates. -/
theorem map_preReflection (p : Index n) (x : V) :
    Φ (x - corootFun Φ p x • r p) = Φ x ∘ Equiv.swap p.1.1 p.1.2 := by
  rw [comp_swap_eq, map_sub, map_smul, hr, corootFun_apply]

include hΦ in
theorem preReflection_r (p q : Index n) :
    r q - corootFun Φ p (r q) • r p = r (reflIdx p q) := by
  apply hΦ
  rw [map_preReflection hr, hr, hr, rootVec_comp_perm, Equiv.symm_swap]
  rfl


section RootPairing

variable [Finite n] [FiniteDimensional ℚ V] (hsp : Submodule.span ℚ (range r) = ⊤)

/-- The root pairing of type `A`: roots `r p` with `Φ (r p) = e_{p.1} - e_{p.2}`, coroots
`corootFun Φ p`, and the evaluation pairing of `V` with its dual. -/
def rootPairing : RootPairing (Index n) ℚ V (Dual ℚ V) :=
  RootPairing.mk'' (Dual.eval ℚ V) ⟨r, r_injective hr⟩ ⟨corootFun Φ, corootFun_injective hr⟩
    (fun p => corootFun_r_self hr p)
    (by
      rintro p - ⟨q, rfl⟩
      exact ⟨reflIdx p q, (preReflection_r hΦ hr p q).symm⟩)
    hsp

theorem rootPairing_toLinearMap :
    (rootPairing hΦ hr hsp).toLinearMap = Dual.eval ℚ V := rfl

theorem rootPairing_root (p : Index n) : (rootPairing hΦ hr hsp).root p = r p := rfl

theorem rootPairing_coroot (p : Index n) :
    (rootPairing hΦ hr hsp).coroot p = corootFun Φ p := rfl

theorem range_rootPairing_root : range (rootPairing hΦ hr hsp).root = range r := rfl

theorem isRootSystem_rootPairing : (rootPairing hΦ hr hsp).IsRootSystem := by
  refine RootPairing.isRootSystem_mk'' fun p q =>
    ⟨rootVecInt p.1.1 p.1.2 q.1.1 - rootVecInt p.1.1 p.1.2 q.1.2, ?_⟩
  change _ = corootFun Φ q (r p)
  rw [corootFun_r hr, rootVec_eq_cast, rootVec_eq_cast]
  push_cast
  rfl

/-- The reflection in the root `r p` swaps the coordinates `p.1` and `p.2`. -/
theorem map_rootPairing_reflection (p : Index n) (x : V) :
    Φ ((rootPairing hΦ hr hsp).reflection p x) = Φ x ∘ Equiv.swap p.1.1 p.1.2 :=
  map_preReflection hr p x

theorem rootPairing_reflection_mem (p : Index n) :
    (rootPairing hΦ hr hsp).reflection p ∈ permSubgroup Φ :=
  ⟨Equiv.swap p.1.1 p.1.2, map_rootPairing_reflection hΦ hr hsp p⟩

/-- Every permutation of the coordinates is realized by a product of reflections. -/
theorem exists_mem_closure_reflection (σ : Equiv.Perm n) :
    ∃ g ∈ Subgroup.closure (range (rootPairing hΦ hr hsp).reflection),
      ∀ x, Φ (g x) = Φ x ∘ σ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, one_mem _, fun x => rfl⟩
  | swap_mul f i j hij ih =>
    obtain ⟨g, hg, hgf⟩ := ih
    refine ⟨g * (rootPairing hΦ hr hsp).reflection ⟨(i, j), hij⟩,
      mul_mem hg (Subgroup.subset_closure (mem_range_self _)), fun x => ?_⟩
    change Φ (g ((rootPairing hΦ hr hsp).reflection ⟨(i, j), hij⟩ x)) = _
    rw [hgf, map_rootPairing_reflection]
    rfl

theorem closure_range_reflection :
    Subgroup.closure (range (rootPairing hΦ hr hsp).reflection) = permSubgroup Φ := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro - ⟨p, rfl⟩
    exact rootPairing_reflection_mem hΦ hr hsp p
  · rintro g ⟨σ, hσ⟩
    obtain ⟨h, hh, hhσ⟩ := exists_mem_closure_reflection hΦ hr hsp σ
    have : g = h := LinearEquiv.ext fun x => hΦ (by rw [hσ, hhσ])
    exact this ▸ hh

/-- The Weyl group of the type `A` root pairing acts on `V` exactly through the coordinate
permutations. -/
theorem weylGroup_map_weightHom :
    (rootPairing hΦ hr hsp).weylGroup.map (RootPairing.Equiv.weightHom _) = permSubgroup Φ := by
  rw [← MonoidHom.domRestrict_range, RootPairing.range_weylGroup_weightHom,
    closure_range_reflection]

end RootPairing

end Langlands.LinearAlgebra.RootSystemTypeA
