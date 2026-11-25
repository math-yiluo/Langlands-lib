/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import WeilConjectures.FieldTheory.FinitelyGeneratedFieldCompleteIntersectionModel
import WeilConjectures.RingTheory.FractionFieldCompleteIntersectionCotangent

/-!
# Cartier equality

Source: Stacks Project, More on Algebra, Lemma Tag 07E1 (blueprint:
lem-weil-pbc-cartier-equality).
-/

@[expose] public section

universe u v

open Algebra

/-! The theorem below is the Cartier dimension formula for a finitely generated
field extension. -/
/--
For a finitely generated field extension, the Kähler differentials and the first
homology of the naive cotangent complex are finite-dimensional, and their
dimensions differ by the transcendence degree (stated without truncated
subtraction, as `trdeg + dim H₁ = dim Ω` in `Cardinal`).  If the extension is finite,
the transcendence degree is zero, so the dimensions are equal.  More on
Algebra, Lemma 07E1 proves this as follows: choose a finite transcendence basis
and the complete-intersection presentation supplied by the cited model lemmas;
the naive cotangent complex is the Jacobian map between free modules by the
regular-sequence conormal and polynomial Kähler-basis lemmas.  Jacobi--Zariski
identifies its cokernel with Kähler differentials, while presentation
functoriality identifies its kernel with `Algebra.H1Cotangent`.  Localization
and exactness carry these identifications from the model to `K`.  Rank--nullity
then gives the dimension difference as `n - c`, which is the cardinality of the
chosen transcendence basis and hence `Algebra.trdeg`; for a finite extension the
empty basis gives zero and the two finite dimensions are equal.  These are the
steps recorded in the node proof (blueprint: lem-weil-pbc-cartier-equality).
(blueprint: lem-weil-pbc-cartier-equality)
-/
theorem cartier_equality
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    (hfg : IntermediateField.FG (⊤ : IntermediateField k K)) :
    Module.Finite K (KaehlerDifferential k K) ∧
      Module.Finite K (Algebra.H1Cotangent k K) ∧
      Algebra.trdeg k K + Module.finrank K (Algebra.H1Cotangent k K) =
        Module.finrank K (KaehlerDifferential k K) ∧
      (FiniteDimensional k K →
        Module.finrank K (KaehlerDifferential k K) =
          Module.finrank K (Algebra.H1Cotangent k K)) := by
  classical
  -- The finite basis and complete-intersection model provide the required coordinates.
  have : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis k K
  let x : Fin s.card → K := fun i ↦ (s.equivFin.symm i : K)
  have hx : IsTranscendenceBasis k x := hs.comp_equiv s.equivFin.symm
  have hgens : ∃ (m : ℕ) (b : Fin m → K),
      IntermediateField.adjoin k (Set.range b) = ⊤ := by
    obtain ⟨t, ht⟩ := hfg
    refine ⟨t.card, fun i ↦ (t.equivFin.symm i : K), ?_⟩
    have hr : Set.range (fun i ↦ (t.equivFin.symm i : K)) = (t : Set K) := by
      change Set.range (Subtype.val ∘ t.equivFin.symm) = _
      rw [EquivLike.range_comp, Subtype.range_coe]
    rwa [hr]
  obtain ⟨n, c, f, hcn, hnc, hlen, hreg, _, _, _, hA, e, _⟩ :=
    FieldTheory.exists_completeIntersection_fractionField_model k K hgens s.card x hx
  obtain ⟨δ, ⟨eH⟩, ⟨eΩ⟩⟩ :=
    exists_fractionField_completeIntersection_cotangent_model k K n f hreg e
  have hH : Module.Finite K (H1Cotangent k K) := Module.Finite.equiv eH.symm
  have hΩ : Module.Finite K (KaehlerDifferential k K) := Module.Finite.equiv eΩ.symm
  have hker := δ.finrank_range_add_finrank_ker
  have hcoker := (LinearMap.range δ).finrank_quotient_add_finrank
  simp only [Module.finrank_fin_fun] at hker
  have hker := hker.trans hlen
  rw [Module.finrank_fin_fun] at hcoker
  have hdim : s.card + Module.finrank K (H1Cotangent k K) =
      Module.finrank K (KaehlerDifferential k K) := by
    rw [eH.finrank_eq, eΩ.finrank_eq]
    omega
  have htrdeg : Algebra.trdeg k K = (s.card : Cardinal) := by
    simpa using hs.cardinalMk_eq_trdeg.symm
  have heq : Algebra.trdeg k K + Module.finrank K (H1Cotangent k K) =
      Module.finrank K (KaehlerDifferential k K) := by
    rw [htrdeg, ← Nat.cast_add, hdim]
  refine ⟨hΩ, hH, heq, ?_⟩
  intro hfinite
  -- Substitute zero transcendence degree, then cancel the natural-number casts.
  let _ : FiniteDimensional k K := hfinite
  have hzero : Algebra.trdeg k K = 0 := by
    exact trdeg_eq_zero
  rw [hzero, zero_add] at heq
  -- The cardinal equality specializes to the finite-dimensional equality.
  exact_mod_cast heq.symm
