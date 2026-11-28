import Langlands.Algebra.HarishChandra.ParabolicIndependenceStatement
import Mathlib.LinearAlgebra.Pi

/-! # Split Cartan subalgebras of finite products -/

noncomputable section

set_option autoImplicit false

namespace LieAlgebra.Pi

variable {I R : Type*} (L : I → Type*) [CommRing R]
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]

/-- The coordinatewise Lie bracket on a product of Lie rings. -/
scoped instance instLieRing : LieRing (∀ i, L i) where
  bracket x y i := ⁅x i, y i⁆
  add_lie x y z := funext fun i => add_lie (x i) (y i) (z i)
  lie_add x y z := funext fun i => lie_add (x i) (y i) (z i)
  lie_self x := funext fun i => lie_self (x i)
  leibniz_lie x y z := funext fun i => leibniz_lie (x i) (y i) (z i)

/-- The scalar action on the product is compatible with its coordinatewise bracket. -/
scoped instance instLieAlgebra : LieAlgebra R (∀ i, L i) where
  lie_smul c x y := funext fun i => lie_smul c (x i) (y i)

@[simp]
theorem lie_apply (x y : ∀ i, L i) (i : I) : ⁅x, y⁆ i = ⁅x i, y i⁆ :=
  rfl

end LieAlgebra.Pi

open scoped LieAlgebra.Pi

namespace LieSubalgebra

variable {I R : Type*} {L : I → Type*} [CommRing R]
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]

/-- The product of Lie subalgebras, with coordinatewise membership and bracket. -/
def pi (H : ∀ i, LieSubalgebra R (L i)) : LieSubalgebra R (∀ i, L i) where
  toSubmodule := Submodule.pi Set.univ fun i => (H i).toSubmodule
  lie_mem' hx hy i hi := (H i).lie_mem (hx i hi) (hy i hi)

@[simp]
theorem mem_pi {H : ∀ i, LieSubalgebra R (L i)} {x : ∀ i, L i} :
    x ∈ pi H ↔ ∀ i, x i ∈ H i :=
  ⟨fun h i => h i (Set.mem_univ i), fun h i _ => h i⟩

end LieSubalgebra

namespace Langlands.Algebra.HarishChandra

open LieModule

variable {I : Type*} {L : I → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℂ (L i)]
  (H : ∀ i, LieSubalgebra ℂ (L i))

private def cartanComponent (i : I) (h : LieSubalgebra.pi H) : H i :=
  ⟨(h : ∀ j, L j) i, LieSubalgebra.mem_pi.mp h.property i⟩

private theorem weightSpace_pi_apply {χ : LieSubalgebra.pi H → ℂ}
    {x : ∀ j, L j} (hx : x ∈ weightSpace _ χ) (h : LieSubalgebra.pi H) (i : I) :
    ⁅(cartanComponent H i h : L i), x i⁆ = χ h • x i :=
  congrFun ((mem_weightSpace _ _).mp hx h) i

section Coordinate

variable [DecidableEq I]

private def cartanSingle (i : I) (h : H i) : LieSubalgebra.pi H :=
  ⟨fun j => ↑(Pi.single (M := fun k => ↥(H k)) i h j),
    LieSubalgebra.mem_pi.mpr fun j => (Pi.single (M := fun k => ↥(H k)) i h j).property⟩

@[simp]
private theorem cartanComponent_single (i : I) (h : H i) :
    cartanComponent H i (cartanSingle H i h) = h :=
  Pi.single_eq_same (M := fun k => ↥(H k)) i h

@[simp]
private theorem cartanComponent_single_of_ne {i j : I} (hij : j ≠ i) (h : H i) :
    cartanComponent H j (cartanSingle H i h) = 0 :=
  Pi.single_eq_of_ne (M := fun k => ↥(H k)) hij h

private theorem single_mem_weightSpace_pi (i : I) {χ : H i → ℂ} {x : L i}
    (hx : x ∈ weightSpace _ χ) :
    Pi.single i x ∈ weightSpace (∀ j, L j) (χ ∘ cartanComponent H i) := by
  refine (mem_weightSpace _ _).mpr fun h => funext fun j => ?_
  change ⁅(cartanComponent H j h : L j), Pi.single i x j⁆ =
    χ (cartanComponent H i h) • Pi.single i x j
  rcases eq_or_ne j i with rfl | hji
  · rw [Pi.single_eq_same]
    exact (mem_weightSpace _ _).mp hx _
  · rw [Pi.single_eq_of_ne hji, lie_zero, smul_zero]

private theorem weightSpace_pi_eq_map_single (i : I) {χ : H i → ℂ} (hχ : χ ≠ 0) :
    (weightSpace (∀ j, L j) (χ ∘ cartanComponent H i) : Submodule ℂ (∀ j, L j)) =
      (weightSpace (L i) χ : Submodule ℂ (L i)).map (LinearMap.single ℂ L i) := by
  have ⟨h, hh⟩ : ∃ h, χ h ≠ 0 := by
    by_contra! hzero
    exact hχ (funext hzero)
  ext x
  constructor
  · intro hx
    refine ⟨x i, (mem_weightSpace _ _).mpr fun h' => ?_, funext fun j => ?_⟩
    · change ⁅(h' : L i), x i⁆ = χ h' • x i
      simpa only [Function.comp_apply, cartanComponent_single] using
        weightSpace_pi_apply H hx (cartanSingle H i h') i
    · change Pi.single i (x i) j = x j
      rcases eq_or_ne j i with hji | hji
      · subst j
        exact Pi.single_eq_same i (x i)
      · have hzero := weightSpace_pi_apply H hx (cartanSingle H i h) j
        rw [Function.comp_apply, cartanComponent_single, cartanComponent_single_of_ne H hji]
          at hzero
        change ⁅(0 : L j), x j⁆ = χ h • x j at hzero
        rw [zero_lie] at hzero
        rw [Pi.single_eq_of_ne hji, (smul_eq_zero.mp hzero.symm).resolve_left hh]
  · rintro ⟨y, hy, rfl⟩
    exact single_mem_weightSpace_pi H i hy

private theorem exists_component_weight {χ : LieSubalgebra.pi H → ℂ}
    (hχ : χ ≠ 0) (hroot : weightSpace (∀ i, L i) χ ≠ ⊥) :
    ∃ (i : I) (ψ : H i → ℂ), ψ ≠ 0 ∧ weightSpace (L i) ψ ≠ ⊥ ∧
      χ = ψ ∘ cartanComponent H i := by
  have hroot' : (weightSpace (∀ i, L i) χ).toSubmodule ≠ ⊥ := fun h =>
    hroot (LieSubmodule.toSubmodule_injective (h.trans LieSubmodule.bot_toSubmodule.symm))
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hroot'
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! hzero
    exact hx0 (funext hzero)
  let ψ : H i → ℂ := χ ∘ cartanSingle H i
  have hfactor : χ = ψ ∘ cartanComponent H i := by
    funext h
    apply smul_left_injective ℂ hi
    change χ h • x i = ψ (cartanComponent H i h) • x i
    rw [← weightSpace_pi_apply H hx h i]
    simpa only [ψ, Function.comp_apply, cartanComponent_single] using
      weightSpace_pi_apply H hx (cartanSingle H i (cartanComponent H i h)) i
  have hmem : x i ∈ weightSpace (L i) ψ :=
    (mem_weightSpace _ _).mpr fun h => by
      change ⁅(h : L i), x i⁆ = ψ h • x i
      simpa only [ψ, Function.comp_apply, cartanComponent_single] using
        weightSpace_pi_apply H hx (cartanSingle H i h) i
  exact ⟨i, ψ, fun h => hχ (by rw [hfactor, h]; rfl),
    fun h => hi (LieSubmodule.mem_bot _ |>.mp (h ▸ hmem)), hfactor⟩

end Coordinate

variable [Finite I]

/-- The product of split Cartan subalgebras in a finite product of complex Lie algebras
is split Cartan. Each nonzero weight is supported in a single factor. -/
theorem IsSplitCartan.pi (h : ∀ i, IsSplitCartan (H i)) :
    IsSplitCartan (LieSubalgebra.pi H) := by
  classical
  refine ⟨⟨?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    apply Subtype.ext
    exact funext fun i => congrArg Subtype.val
      ((h i).isLieAbelian.trivial (cartanComponent H i x) (cartanComponent H i y))
  · rw [← LieSubmodule.iSup_toSubmodule_eq_top]
    apply top_unique
    rw [← LinearMap.iSup_range_single ℂ L]
    refine iSup_le fun i => ?_
    rw [LinearMap.range_eq_map, ← LieSubmodule.iSup_toSubmodule_eq_top.mpr
      (h i).iSup_weightSpace_eq_top, Submodule.map_iSup]
    refine iSup_le fun χ => le_iSup_of_le (χ ∘ cartanComponent H i) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact single_mem_weightSpace_pi H i hy
  · ext x
    change x ∈ weightSpace _ (0 : LieSubalgebra.pi H → ℂ) ↔ x ∈ LieSubalgebra.pi H
    rw [LieSubalgebra.mem_pi]
    simp_rw [← LieSubalgebra.mem_toSubmodule, ← (h _).weightSpace_zero]
    constructor
    · intro hx i
      exact (mem_weightSpace _ _).mpr fun y => by
        change ⁅(y : L i), x i⁆ = (0 : ℂ) • x i
        simpa only [cartanComponent_single, Pi.zero_apply] using
          weightSpace_pi_apply H hx (cartanSingle H i y) i
    · intro hx
      exact (mem_weightSpace _ _).mpr fun y => funext fun i =>
        (mem_weightSpace _ _).mp (hx i) (cartanComponent H i y)
  · intro χ hχ hroot
    obtain ⟨i, ψ, hψ, hrootψ, rfl⟩ := exists_component_weight H hχ hroot
    change Module.finrank ℂ
      (weightSpace (∀ j, L j) (ψ ∘ cartanComponent H i)).toSubmodule = 1
    rw [weightSpace_pi_eq_map_single H i hψ]
    exact (Submodule.equivMapOfInjective (LinearMap.single ℂ L i)
      (Pi.single_injective i) (weightSpace (L i) ψ).toSubmodule).finrank_eq.symm.trans
      ((h i).finrank_weightSpace ψ hψ hrootψ)
  · intro χ hχ hroot
    obtain ⟨i, ψ, hψ, hrootψ, rfl⟩ := exists_component_weight H hχ hroot
    obtain ⟨e, he, f, hf, y, hey, hψy⟩ := (h i).exists_sl2 ψ hψ hrootψ
    refine ⟨Pi.single (M := L) i e, single_mem_weightSpace_pi H i he,
      Pi.single (M := L) i f, ?_, cartanSingle H i y, ?_, ?_⟩
    · change Pi.single (M := L) i f ∈ weightSpace _ ((-ψ) ∘ cartanComponent H i)
      exact single_mem_weightSpace_pi H i hf
    · funext j
      change ⁅Pi.single i e j, Pi.single i f j⁆ =
        (cartanComponent H j (cartanSingle H i y) : L j)
      rcases eq_or_ne j i with hji | hji
      · subst j
        simpa only [Pi.single_eq_same, cartanComponent_single] using hey
      · simp only [Pi.single_eq_of_ne hji, cartanComponent_single_of_ne H hji]
        change ⁅(0 : L j), 0⁆ = 0
        exact lie_zero _
    · simpa only [Function.comp_apply, cartanComponent_single] using hψy
  · intro χ hχ hroot c hc hscaled
    obtain ⟨i, ψ, hψ, hrootψ, rfl⟩ := exists_component_weight H hχ hroot
    have hψc : c • ψ ≠ 0 := fun hzero => hψ ((smul_eq_zero.mp hzero).resolve_left hc)
    refine (h i).reduced ψ hψ hrootψ c hc fun heq => hscaled ?_
    apply LieSubmodule.toSubmodule_injective
    change (weightSpace (∀ j, L j) ((c • ψ) ∘ cartanComponent H i) :
      Submodule ℂ (∀ j, L j)) = ⊥
    rw [weightSpace_pi_eq_map_single H i hψc, heq, LieSubmodule.bot_toSubmodule,
      Submodule.map_bot]

end Langlands.Algebra.HarishChandra
