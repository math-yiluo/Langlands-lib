/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.FunctionField

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- The affine-section criterion for a nonzero ideal sheaf on an integral scheme.
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01YL.
Proof: The closed support contains the generic point exactly when it is the whole scheme,
by density of that point. On a reduced scheme full support is equivalent to the zero ideal.
On any nonempty affine open the generic point corresponds to the zero prime, so the
zero-locus description of support says membership there is equivalent to the section ideal
being zero. Negating gives the forward direction on every nonempty affine open. For the
reverse direction choose an affine neighborhood of the generic point; its nonzero section
ideal excludes the generic point from the support and hence excludes the zero ideal.
(blueprint: lem-weil-pbc-integral-scheme-ideal-generic-stalk-affine)
-/
theorem integral_ideal_nonzero_iff_affine_sections (X : Scheme.{u}) [IsIntegral X]
    (J : X.IdealSheafData) :
    J ≠ ⊥ ↔ ∀ U : X.affineOpens, Nonempty U.1 → J.ideal U ≠ ⊥ := by
  have hsupport : genericPoint X ∈ J.support ↔ J = ⊥ := by
    rw [← IdealSheafData.support_eq_top_iff]
    constructor
    · intro h
      apply top_le_iff.mp
      intro x _
      have hc := closure_minimal (Set.singleton_subset_iff.mpr h) J.support.isClosed
      rw [genericPoint_closure X] at hc
      exact hc (Set.mem_univ x)
    · intro h
      rw [h]
      trivial
  have hlocal (U : X.affineOpens) (hU : Nonempty U.1) :
      genericPoint X ∉ J.support ↔ J.ideal U ≠ ⊥ := by
    let _ := hU
    have hx : genericPoint X ∈ U.1 :=
      ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr (by simpa using hU)
    rw [J.mem_support_iff_of_mem hx]
    have hz := Set.ext_iff.mp (U.2.fromSpec_preimage_zeroLocus (J.ideal U))
      (U.2.primeIdealOf ⟨genericPoint X, hx⟩)
    change (U.2.fromSpec (U.2.primeIdealOf ⟨genericPoint X, hx⟩) ∈
      X.zeroLocus (U := U.1) (J.ideal U)) ↔
      J.ideal U ≤ (U.2.primeIdealOf ⟨genericPoint X, hx⟩).asIdeal at hz
    rw [U.2.fromSpec_primeIdealOf] at hz
    change (genericPoint X ∈ X.zeroLocus (U := U.1) (J.ideal U)) ↔
      J.ideal U ≤ (U.2.primeIdealOf ⟨genericPoint X, hx⟩).asIdeal at hz
    rw [hz]
    have hp : (U.2.primeIdealOf ⟨genericPoint X, hx⟩).asIdeal = ⊥ := by
      rw [U.2.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
      rfl
    rw [hp, le_bot_iff]
  constructor
  · intro h U hU
    exact (hlocal U hU).mp (fun hs ↦ h (hsupport.mp hs))
  · intro h hb
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show genericPoint X ∈ (⊤ : X.Opens) from trivial) isOpen_univ
    exact ((hlocal ⟨U, hU⟩ ⟨⟨genericPoint X, hxU⟩⟩).mpr
      (h ⟨U, hU⟩ ⟨⟨genericPoint X, hxU⟩⟩)) (hsupport.mpr hb)

end AlgebraicGeometry.Scheme
