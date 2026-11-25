/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Passing an upper bound through a finite-cohomology derived inverse limit

Source: latest blueprint, `sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/`
`lem-zl-affine-curve-range.proof.md`, final lattice paragraph.
Finiteness one degree earlier handles the possible extra top cohomology group.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.AffineCurveRange

private theorem roosMap_epi_of_finite (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hA : ∀ n : ℕᵒᵖ, Finite (A.obj n)) : Epi (roosMap A) := by
  classical
  let (n : ℕᵒᵖ) : Finite (A.obj n) := hA n
  have hsurj : Function.Surjective (roosMap A) := by
    intro y
    let Y (n : ℕ) := Pi.π (fun n : ℕ ↦ A.obj (op n)) n y
    let f (n : ℕ) := A.map (homOfLE (Nat.le_succ n)).op
    let E (n : ℕ) := {x : ∀ j : Fin (n + 1), A.obj (op j.val) //
      ∀ j : Fin n, x ⟨j.val, by omega⟩ -
        f j.val (x ⟨j.val + 1, by omega⟩) = Y j.val}
    let r (n : ℕ) : E (n + 1) → E n := fun x ↦
      ⟨fun j ↦ x.val ⟨j.val, by omega⟩,
        fun j ↦ x.prop ⟨j.val, by omega⟩⟩
    let F : ℕᵒᵖ ⥤ Type u := Functor.ofOpSequence (fun n ↦ ↾(r n))
    have hnonempty (n : ℕ) : Nonempty (E n) := by
      let x : ∀ j : Fin (n + 1), A.obj (op j.val) :=
        Fin.reverseInduction 0 (fun j z ↦ Y j.val + f j.val z)
      refine ⟨⟨x, fun j ↦ ?_⟩⟩
      have h := @Fin.reverseInduction_castSucc n
        (fun j ↦ A.obj (op j.val)) 0 (fun j z ↦ Y j.val + f j.val z) j
      simp only [Fin.val_castSucc, Fin.val_succ] at h
      change x ⟨j.val, _⟩ = Y j.val + f j.val (x ⟨j.val + 1, _⟩) at h
      rw [h]
      exact add_sub_cancel_right _ _
    have : ∀ n : ℕᵒᵖ, Nonempty (F.obj n) := fun n ↦ hnonempty n.unop
    have : ∀ n : ℕᵒᵖ, Finite (F.obj n) := fun n ↦ by
      change Finite (E n.unop)
      dsimp only [E]
      infer_instance
    obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system F
    let x (n : ℕ) := (s (op n)).val ⟨n, Nat.lt_succ_self n⟩
    have hx (n : ℕ) : x n - f n (x (n + 1)) = Y n := by
      have he := congrArg (fun z : E n ↦ z.val ⟨n, Nat.lt_succ_self n⟩)
        (hs (homOfLE (Nat.le_succ n)).op)
      simp only [F, Functor.ofOpSequence_map_homOfLE_succ] at he
      change (s (op (n + 1))).val ⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩ = x n at he
      have heq := (s (op (n + 1))).prop ⟨n, Nat.lt_succ_self n⟩
      change (s (op (n + 1))).val ⟨n, Nat.lt_succ_of_lt (Nat.lt_succ_self n)⟩ -
        f n (x (n + 1)) = Y n at heq
      rwa [he] at heq
    refine ⟨(Concrete.productEquiv (fun n : ℕ ↦ A.obj (op n))).symm x, ?_⟩
    apply (Concrete.productEquiv (fun n : ℕ ↦ A.obj (op n))).injective
    funext n
    simp only [Concrete.productEquiv_apply_apply]
    change ((roosMap A ≫ Pi.π (fun n : ℕ ↦ A.obj (op n)) n)
      ((Concrete.productEquiv (fun n : ℕ ↦ A.obj (op n))).symm x)) = _
    simpa [roosMap, towerTransitionEndomorphism, towerProductShift, Y, f] using hx n
  exact ConcreteCategory.epi_of_surjective _ hsurj

/-- A specified derived inverse limit has zero cohomology in degree i if every
level does and the level cohomology in degree i-1 is finite.

Source: latest blueprint, `lem-zl-affine-curve-range.proof.md`, Mittag--Leffler
passage in the lattice paragraph (blueprint: lem-zl-finite-tower-upper-bound).

Proof: use the Milnor short exact sequence. Finiteness in degree i-1 kills its
first term by the finite Mittag--Leffler theorem. The last term, the limit of
the level-i cohomology, is zero because each object of that diagram is zero.
Exactness between two zero objects makes the middle term zero. This includes
the degree immediately above the finite-level upper bound; no surjectivity of
the cohomology transition maps is assumed.
-/
theorem finiteTower_homology_isZero [HasDerivedCategory.{v} AddCommGrpCat.{u}]
    (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
    [HasProduct (fun n : ℕ ↦ K.obj (op n))]
    (L : DerivedCategory AddCommGrpCat.{u})
    (hL : IsDerivedLimit (K := fun n : ℕ ↦ K.obj (op n))
      (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op) L)
    (i : ℤ)
    (hfinite : ∀ n : ℕᵒᵖ,
      Finite ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)).obj (K.obj n)))
    (hzero : ∀ n : ℕᵒᵖ,
      IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj (K.obj n))) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj L) := by
  obtain ⟨p, δ, hT⟩ := hL
  obtain ⟨a, b, h, _⟩ := milnor_shortExact.{u, v} i
  obtain ⟨⟨hz, hS⟩, _⟩ := h K L p δ hT
  let A := K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)
  have : Epi (roosMap A) := roosMap_epi_of_finite A hfinite
  obtain ⟨_, e₁, _⟩ := derivedLimitRoosAbelianGroups.{u}.2
  have hleft := (isZero_cokernel_of_epi (roosMap A)).of_iso (e₁ A)
  have hright : IsZero (limit (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i)) :=
    (limit.isLimit _).isZero_pt ((Functor.isZero_iff _).mpr hzero)
  exact hS.exact.isZero_of_both_isZero hleft hright

end WeilConjectures.AffineCurveRange
