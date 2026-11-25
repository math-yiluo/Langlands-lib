/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.Algebra.Central.ReducedNorm
import Mathlib.Topology.Algebra.MulAction

/-!
# Locally constant matrix lifts

Source: Stacks Project, Lemma 03R6, construction before Theorem 03R7, and Section 0DVG.
(blueprint: lem-sc-brauer-scalar-defect-lifts).
-/

@[expose] public section
universe u
namespace Field

open scoped TensorProduct
private theorem locallyConstant_galois_eval (K : Type u) [Field K]
    (x : SeparableClosure K) :
    IsLocallyConstant (fun g : SeparableClosure K ≃ₐ[K] SeparableClosure K ↦ g x) := by
  let : TopologicalSpace (SeparableClosure K) := ⊥
  let : DiscreteTopology (SeparableClosure K) := ⟨rfl⟩
  let : ContinuousSMul (SeparableClosure K ≃ₐ[K] SeparableClosure K)
      (SeparableClosure K) :=
    continuousSMul_iff_stabilizer_isOpen.mpr (fun y ↦ stabilizer_isOpen_of_isIntegral y)
  exact (IsLocallyConstant.iff_continuous _).mpr (continuous_id.smul continuous_const)

/-- Finite Galois descent supplies locally constant matrix lifts satisfying conjugation.
Proof: fix a finite K-basis of A and collect the matrix entries of the images of its
basis vectors under e. For each entry x, its Galois stabilizer is open in the Krull
topology because x is integral over K. Equip the separable closure with the discrete
topology temporarily; the open-stabilizer criterion makes its Galois action continuous,
so evaluation at x is locally constant. The finite tuple q of all the transformed
entries is therefore locally constant. Equality of two such tuples implies equality
of the K-linear maps a ↦ g(e(1 ⊗ a)), by equality on the chosen basis.
For each tuple in the range of q choose a representative automorphism. The proved
Skolem--Noether lemma `Algebra.IsCentral.exists_unit_map_eq_conj` supplies a conjugating
unit for this representative; invert it to obtain the orientation required here.
Choose a unit for each tuple using that proved existence statement. Composing this
choice with q gives a locally constant function b. The equality of K-linear maps just
proved transports the conjugation identity from the representative to every g in its
fiber. This proves the identity for all a. No finite Galois extension or choice from
an unproved theorem is needed.

Source: Stacks Project, Lemma 03R6 and the construction preceding Theorem 03R7.
(blueprint: lem-sc-brauer-scalar-defect-lifts). -/
theorem exists_locallyConstant_brauer_lift (K : Type u) [Field K] (A : CSA.{u, u} K)
    (n : ℕ) (_hn : n ≠ 0)
    (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K)) :
    ∃ b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
        Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K),
      IsLocallyConstant b ∧
      (∀ (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : A),
        (e (1 ⊗ₜ[K] a)).map g =
          ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) := by
  classical
  let v := Module.finBasis K A
  let d (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
      A →ₗ[K] Matrix (Fin n) (Fin n) (SeparableClosure K) :=
    (g.mapMatrix.toLinearMap).comp
      ((e.toLinearMap.restrictScalars K).comp
        (Algebra.TensorProduct.includeRight.toLinearMap))
  let q (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) :=
    fun (i : Fin (Module.finrank K A)) (j k : Fin n) ↦ d g (v i) j k
  have hq : IsLocallyConstant q := by
    exact (LocallyConstant.unflip (fun i ↦ LocallyConstant.unflip (fun j ↦
      LocallyConstant.unflip (fun k ↦
        ⟨fun (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) ↦ g (e (1 ⊗ₜ[K] v i) j k),
          locallyConstant_galois_eval K _⟩)))).isLocallyConstant
  let r (t : Set.range q) := Classical.choose t.property
  have hr (t : Set.range q) : q (r t) = t.val := Classical.choose_spec t.property
  have hd (g h : SeparableClosure K ≃ₐ[K] SeparableClosure K)
      (heq : q g = q h) : d g = d h := by
    apply v.ext
    intro i
    apply Matrix.ext
    intro j k
    exact congrFun (congrFun (congrFun heq i) j) k
  have lifts (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
      ∃ b : Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K),
        ∀ a : A, (e (1 ⊗ₜ[K] a)).map g =
          (b⁻¹).val * e (1 ⊗ₜ[K] a) * b.val := by
    obtain ⟨b, hb⟩ := Algebra.IsCentral.exists_unit_map_eq_conj e g
    exact ⟨b⁻¹, by simpa using hb⟩
  let B (t : Set.range q) := Classical.choose (lifts (r t))
  let b (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) := B ⟨q g, ⟨g, rfl⟩⟩
  refine ⟨b, ?_, ?_⟩
  · have hsub : IsLocallyConstant (fun g ↦ (⟨q g, ⟨g, rfl⟩⟩ : Set.range q)) :=
      IsLocallyConstant.desc _ Subtype.val hq Subtype.val_injective
    exact hsub.comp B
  · intro g a
    have hsame := hd g (r ⟨q g, ⟨g, rfl⟩⟩) (hr ⟨q g, ⟨g, rfl⟩⟩).symm
    have ha := congrArg (fun f : A →ₗ[K] Matrix (Fin n) (Fin n)
      (SeparableClosure K) ↦ f a) hsame
    change (e (1 ⊗ₜ[K] a)).map g = _ at ha
    rw [ha]
    exact Classical.choose_spec (lifts (r ⟨q g, ⟨g, rfl⟩⟩)) a
end Field
