import Langlands.Geometry.Building.GaloisTranslationAction
import Langlands.GroupScheme.Rational.RootSubgroupGaloisTransport

/-! # Actual coefficient transport of root-function families and filtrations -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))
  (G : GroupScheme (Spec (CommRingCat.of k)))

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G

namespace RootFunctionFamily

/-- Simultaneous coefficient transport on the actual character and point arguments.
The real value of the function is unchanged. -/
def galoisAction : (K ≃ₐ[k] K) →* Equiv.Perm (RootFunctionFamily T_K G_K) where
  toFun σ :=
    { toFun φ := ⟨fun a g => φ (characterLattice.galoisRepresentation k K T σ⁻¹ a)
        (rationalConjugate k K G σ⁻¹ g)⟩
      invFun φ := ⟨fun a g => φ (characterLattice.galoisRepresentation k K T σ a)
        (rationalConjugate k K G σ g)⟩
      left_inv φ := by
        apply RootFunctionFamily.ext
        intro a g
        change φ (characterLattice.galoisRepresentation k K T σ⁻¹
            (characterLattice.galoisRepresentation k K T σ a))
          (rationalConjugate k K G σ⁻¹ (rationalConjugate k K G σ g)) = φ a g
        rw [Representation.inv_self_apply, ← rationalConjugate_mul,
          inv_mul_cancel, rationalConjugate_one]
      right_inv φ := by
        apply RootFunctionFamily.ext
        intro a g
        change φ (characterLattice.galoisRepresentation k K T σ
            (characterLattice.galoisRepresentation k K T σ⁻¹ a))
          (rationalConjugate k K G σ (rationalConjugate k K G σ⁻¹ g)) = φ a g
        rw [Representation.self_inv_apply, ← rationalConjugate_mul,
          mul_inv_cancel, rationalConjugate_one] }
  map_one' := by
    apply Equiv.ext
    intro φ
    apply RootFunctionFamily.ext
    intro a g
    change φ (characterLattice.galoisRepresentation k K T (1 : K ≃ₐ[k] K)⁻¹ a)
      (rationalConjugate k K G (1 : K ≃ₐ[k] K)⁻¹ g) = φ a g
    rw [inv_one, map_one, rationalConjugate_one]
    rfl
  map_mul' σ τ := by
    apply Equiv.ext
    intro φ
    apply RootFunctionFamily.ext
    intro a g
    change φ (characterLattice.galoisRepresentation k K T (σ * τ)⁻¹ a)
      (rationalConjugate k K G (σ * τ)⁻¹ g) =
      φ (characterLattice.galoisRepresentation k K T τ⁻¹
        (characterLattice.galoisRepresentation k K T σ⁻¹ a))
        (rationalConjugate k K G τ⁻¹ (rationalConjugate k K G σ⁻¹ g))
    rw [mul_inv_rev, map_mul, Module.End.mul_apply, rationalConjugate_mul]

@[simp] theorem galoisAction_apply (σ : K ≃ₐ[k] K)
    (φ : RootFunctionFamily T_K G_K) (a : characterLattice T_K)
    (g : rationalPoints G_K) :
    galoisAction k K T G σ φ a g =
      φ (characterLattice.galoisRepresentation k K T σ⁻¹ a)
        (rationalConjugate k K G σ⁻¹ g) := rfl

/-- Simultaneous transport of the family, character and point preserves values. -/
@[simp] theorem galoisAction_apply_conjugate (σ : K ≃ₐ[k] K)
    (φ : RootFunctionFamily T_K G_K) (a : characterLattice T_K)
    (g : rationalPoints G_K) :
    galoisAction k K T G σ φ (characterLattice.galoisRepresentation k K T σ a)
      (rationalConjugate k K G σ g) = φ a g := by
  rw [galoisAction_apply, Representation.inv_self_apply, ← rationalConjugate_mul,
    inv_mul_cancel, rationalConjugate_one]

/-- The actual actions on real cocharacters and root functions intertwine translation. -/
theorem galoisAction_vadd (σ : K ≃ₐ[k] K) (v : V T_K)
    (φ : RootFunctionFamily T_K G_K) :
    galoisAction k K T G σ (v +ᵥ φ) =
      galoisCocharacterAction k K T σ v +ᵥ galoisAction k K T G σ φ := by
  apply RootFunctionFamily.ext
  intro a g
  rw [galoisAction_apply, vadd_apply, vadd_apply, galoisAction_apply,
    eval_galoisCocharacterAction_right]

/-- Coefficient transport preserves equipollence of arbitrary actual families. -/
theorem galoisAction_equipollent (σ : K ≃ₐ[k] K)
    {φ ψ : RootFunctionFamily T_K G_K} (h : Equipollent φ ψ) :
    Equipollent (galoisAction k K T G σ φ) (galoisAction k K T G σ ψ) := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨galoisCocharacterAction k K T σ v, galoisAction_vadd k K T G σ v φ⟩

end RootFunctionFamily

variable {T G} (i : T.toGrp ⟶ G)

local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

/-- The existing coefficient conjugation exactly transports root filtration
membership at every real depth, for every character. -/
theorem rationalConjugate_mem_rootFiltration_iff (σ : K ≃ₐ[k] K)
    (φ : RootFunctionFamily T_K G_K) (a : characterLattice T_K)
    (r : ℝ) (g : rationalPoints G_K) :
    rationalConjugate k K G σ g ∈ rootFiltration (S := T_K) i_K
      (RootFunctionFamily.galoisAction k K T G σ φ)
      (characterLattice.galoisRepresentation k K T σ a) r ↔
      g ∈ rootFiltration (S := T_K) i_K φ a r := by
  rw [mem_rootFiltration, mem_rootFiltration, RootFunctionFamily.galoisAction_apply_conjugate]
  exact and_congr (RelativeRoot.rationalConjugate_mem_subgroup_iff k K i σ a g) Iff.rfl

/-- The full filtration set is the image under the existing coefficient map. -/
theorem image_rootFiltration_galoisAction (σ : K ≃ₐ[k] K)
    (φ : RootFunctionFamily T_K G_K) (a : characterLattice T_K) (r : ℝ) :
    rationalConjugate k K G σ '' rootFiltration (S := T_K) i_K φ a r =
      rootFiltration (S := T_K) i_K (RootFunctionFamily.galoisAction k K T G σ φ)
        (characterLattice.galoisRepresentation k K T σ a) r := by
  apply Set.ext
  intro g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (rationalConjugate_mem_rootFiltration_iff k K i σ φ a r h).2 hh
  · intro hg
    refine ⟨rationalConjugate k K G σ⁻¹ g, ?_, ?_⟩
    · apply (rationalConjugate_mem_rootFiltration_iff k K i σ φ a r
        (rationalConjugate k K G σ⁻¹ g)).1
      simpa only [← rationalConjugate_mul, mul_inv_cancel, rationalConjugate_one] using hg
    · rw [← rationalConjugate_mul, mul_inv_cancel, rationalConjugate_one]

end Langlands.Geometry.Building
