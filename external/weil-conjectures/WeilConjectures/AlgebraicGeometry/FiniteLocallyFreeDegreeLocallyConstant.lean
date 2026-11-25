/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Locally constant fibre degree of a finite locally free morphism

Source: literature/stacks-project/morphisms.tex, Section 02K9, Definition 02KA
and Lemma 04MH (blueprint: lem-weil-pbc-finite-locally-free-degree-locally-constant).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- For a finite locally free morphism, the fibre dimension is finite and locally constant;
the clopen fibres give the equivalent decomposition into constant-degree restrictions.
Source: Stacks Morphisms, Definition 02KA and Lemma 04MH
(blueprint: lem-weil-pbc-finite-locally-free-degree-locally-constant).
Step 1 applies the finite-flat rank statement `lem-weil-pbc-finite-flat-rank-iso` to identify
this dimension with the finite rank and obtain local constancy. Step 2 takes the clopen fibres
of the locally constant function and restricts `f` to each one, preserving finite, flat, and
locally finitely presented. Step 3 identifies these fibres and restricted degrees with the
asserted equivalent formulation.
-/
theorem finiteLocallyFree_fiberDimension_isLocallyConstant
    {X S : Scheme.{u}} (f : X ⟶ S) [f.IsFiniteLocallyFree] :
    let δ : S → ℕ := fun s => (f.fiberToSpecResidueField s).finrankΓ
    (∀ s : S, Module.Finite (S.residueField s) Γ(f.fiber s, ⊤)) ∧
      IsLocallyConstant δ ∧
      (∀ d : ℕ, IsClopen (δ ⁻¹' {d})) ∧
      (∃ U : ℕ → S.Opens,
        (∀ d : ℕ, ∀ s : S, s ∈ U d ↔ δ s = d) ∧
          (∀ d : ℕ, (f ∣_ U d).IsFiniteLocallyFreeOfDegree d)) := by
  dsimp
  let r : S → ℕ := f.finrank
  have hr : IsLocallyConstant r := f.isLocallyConstant_finrank
  have hEq (s : S) : r s = (f.fiberToSpecResidueField s).finrankΓ :=
    by
      have hAffine {Z : Scheme.{u}} {R : CommRingCat.{u}}
          (h : Z ⟶ Spec R) [IsAffine Z] [IsFinite h] [Flat h] (y : Spec R) :
          h.finrank y = h.fiberDegree y := by
        wlog hZ : ∃ S, Z = Spec S generalizing Z
        · have := this (Z.isoSpec.inv ≫ h) ⟨_, rfl⟩
          rwa [Scheme.Hom.finrank_comp_left_of_isIso,
            Scheme.Hom.fiberDegree_comp_left_of_isIso] at this
        obtain ⟨S, rfl⟩ := hZ
        obtain ⟨φ, rfl⟩ := Spec.map_surjective h
        have h₁ : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
        have h₂ : φ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
        rw [Scheme.Hom.finrank_SpecMap_eq_finrank h₁ h₂]
        algebraize [φ.hom]
        have e : φ = CommRingCat.ofHom (algebraMap R S) := rfl
        conv_rhs => rw [e, Scheme.Hom.fiberDegree_SpecMap]
        rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap,
          Module.rankAtStalk_eq]
        rfl
      change f.finrank s = f.fiberDegree s
      obtain ⟨R, i, _, y, rfl⟩ := S.exists_Spec_apply_eq s
      have : IsAffine (CategoryTheory.Limits.pullback f i) :=
        isAffine_of_isAffineHom (CategoryTheory.Limits.pullback.snd f i)
      rw [← Scheme.Hom.finrank_pullback_snd,
        ← f.fiberDegree_of_isPullback (.of_hasPullback f i), hAffine]
  have hEq' : r = fun s : S => (f.fiberToSpecResidueField s).finrankΓ := by
    funext s; exact hEq s
  have hFinite (s : S) : Module.Finite (S.residueField s) Γ(f.fiber s, ⊤) := by
    apply RingHom.finite_algebraMap.mp
    rw [Scheme.Hom.algebraMap_fiber, CommRingCat.hom_comp,
      RingHom.finite_respectsIso.cancel_left_isIso]
    exact (f.fiberToSpecResidueField s).finite_appTop
  refine ⟨hFinite, ?_, ?_, ?_⟩
  · simpa [hEq'] using hr
  · intro d
    rw [← hEq']
    exact ⟨hr.isClosed_fiber d, hr.isOpen_fiber d⟩
  · let U : ℕ → S.Opens := fun d => ⟨r ⁻¹' {d}, hr.isOpen_fiber d⟩
    refine ⟨U, ?_, ?_⟩
    · intro d s
      change r s = d ↔ _
      rw [hEq s]
    · intro d
      have : (f ∣_ U d).IsFiniteLocallyFree := ⟨⟩
      refine ⟨fun s => ?_⟩
      rw [Scheme.Hom.fiberDegree_morphismRestrict]
      let s' : S := s.1
      change (f.fiberToSpecResidueField s').finrankΓ = d
      rw [← hEq s']
      exact s.2

end AlgebraicGeometry
