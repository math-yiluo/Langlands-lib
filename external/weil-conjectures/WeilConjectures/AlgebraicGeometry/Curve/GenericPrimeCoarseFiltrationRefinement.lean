/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions

/-!
# Refinement of constant-vector-space quotient filtrations

Source: blueprint `theorem-cohomology-curves--2`, proof paragraphs 1--2.
(blueprint: lem-sc-generic-prime-coarse-filtration-refinement)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace AlgebraicGeometry.IsConnectedCurve

/-- A coarse finite filtration with finite direct sums of prime constant sheaves as
quotients admits a refinement with rank-one prime constant quotients and unchanged endpoint.

Source: blueprint `theorem-cohomology-curves--2`, proof paragraphs 1--2 (refine a basis flag).
Proof: prime constant objects generate an isomorphism-closed object property P. Its finite
filtration closure is closed under extensions. Every finite iterated binary direct sum of
one prime constant object belongs to that closure, by induction and split exact sequences.
Induct along the given coarse filtration to put its endpoint in the closure. The explicit
chain characterization of the closure gives the required refined chain, extended constantly
past its last index. Zero-dimensional quotients contribute no steps, and a length-zero input
chain is handled by the zero-object constructor.
(blueprint: lem-sc-generic-prime-coarse-filtration-refinement) -/
theorem exists_prime_filtration_of_coarse
    (X : Scheme.{u}) (n : ℕ)
    (F : ℕ → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hzero : IsZero (F 0))
    (hstep : ∀ a : ℕ, a < n →
      ∃ (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (ℓ d : ℕ),
        ℓ.Prime ∧ S.ShortExact ∧ Nonempty (S.X₁ ≅ F a) ∧
          Nonempty (S.X₂ ≅ F (a + 1)) ∧
          Nonempty (S.X₃ ≅ Nat.rec (0 : _)
            (fun _ A ↦ A ⊞ X.constantZMod ℓ) d)) :
    ∃ (m : ℕ) (G : ℕ → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsZero (G 0) ∧
      (∀ a : ℕ, a < m →
        ∃ (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (ℓ : ℕ),
          ℓ.Prime ∧ S.ShortExact ∧ Nonempty (S.X₁ ≅ G a) ∧
            Nonempty (S.X₂ ≅ G (a + 1)) ∧ Nonempty (S.X₃ ≅ X.constantZMod ℓ)) ∧
      Nonempty (F n ≅ G m) := by
  let P : ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    fun A ↦ ∃ ℓ : ℕ, ℓ.Prime ∧ Nonempty (A ≅ X.constantZMod ℓ)
  let : P.IsClosedUnderIsomorphisms := ⟨by
    intro A B e h
    obtain ⟨ℓ, hp, ⟨e'⟩⟩ := h
    exact ⟨ℓ, hp, ⟨e.symm ≪≫ e'⟩⟩⟩
  have hsum (ℓ : ℕ) (hp : ℓ.Prime) (d : ℕ) :
      P.filtrationClosure (Nat.rec (0 : _) (fun _ A ↦ A ⊞ X.constantZMod ℓ) d) := by
    induction d with
    | zero => exact .of_isZero (isZero_zero _)
    | succ d ih =>
      exact P.filtrationClosure.prop_biprod ih
        (P.le_filtrationClosure _ ⟨ℓ, hp, ⟨Iso.refl _⟩⟩)
  have hF : ∀ a : ℕ, a ≤ n → P.filtrationClosure (F a) := by
    intro a
    induction a with
    | zero => exact fun _ ↦ .of_isZero hzero
    | succ a ih =>
      intro ha
      obtain ⟨S, ℓ, d, hp, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := hstep a (by omega)
      exact P.filtrationClosure.prop_of_iso e₂
        (P.filtrationClosure.prop_X₂_of_shortExact hS
          (P.filtrationClosure.prop_of_iso e₁.symm (ih (by omega)))
          (P.filtrationClosure.prop_of_iso e₃.symm (hsum ℓ hp d)))
  obtain ⟨m, G, φ, h0, ⟨e⟩, hm, hP⟩ := P.filtrationClosure_iff.mp (hF n le_rfl)
  let G' : ℕ → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    fun a ↦ G ⟨min a m, by omega⟩
  refine ⟨m, G', ?_, ?_, ⟨?_⟩⟩
  · simpa [G'] using h0
  · intro a ha
    let i : Fin m := ⟨a, ha⟩
    let := hm i
    obtain ⟨ℓ, hp, he⟩ := hP i
    refine ⟨ShortComplex.mk (φ i) (cokernel.π (φ i)) (cokernel.condition _), ℓ, hp,
      ?_, ?_, ?_, he⟩
    · exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
    · exact ⟨eqToIso (by dsimp [G', i]; congr 1; apply Fin.ext; simp; omega)⟩
    · exact ⟨eqToIso (by dsimp [G', i]; congr 1; apply Fin.ext; simp; omega)⟩
  · exact e.symm ≪≫ eqToIso (by dsimp [G']; congr 1; apply Fin.ext; simp)

end AlgebraicGeometry.IsConnectedCurve
