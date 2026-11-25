/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Local regular generators for a smooth diagonal

Source: Stacks Project, Tags 067U and 067R, applied to the diagonal as a section of the
smooth first projection (blueprint: lem-sc-smooth-diagonal-regular-immersion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The diagonal of a smooth morphism of pure relative dimension `d`, when it is closed,
has on an affine neighbourhood of every point either the unit ideal or an ideal generated
by a regular sequence of length `d`. The ideal is the kernel of the map on sections.
Source: Stacks Project, Tags 067U and 067R
(blueprint: lem-sc-smooth-diagonal-regular-immersion).

Proof: outside the closed diagonal image choose an affine neighbourhood in its complement;
the inverse image is empty, so the kernel is the unit ideal. At an image point, if `d = 0`,
the morphism is etale (def-sbc-smooth-morphisms), hence unramified (def-weil-etale-morphism),
and its diagonal is open (def-weil-unramified-morphism). Choose the affine neighbourhood
inside the open and closed image. The diagonal there is an isomorphism, its ideal is zero,
and the empty sequence is regular. If `d > 0`, choose standard smooth affine charts around
the source point (lem-sc-standard-smooth-local-relative-dimension). Their fibre product is
an open neighbourhood of the diagonal point, and the diagonal restricts to the affine
diagonal on that product. The standard smooth affine calculation supplies regular generators
of length `d` on an affine neighbourhood (lem-sc-standard-smooth-affine-diagonal-generators).
This neighbourhood and its ideal also give the required neighbourhood in the original
fibre product. -/
theorem exists_isRegular_smooth_diagonal_generators {X S : Scheme.{u}} (d : ℕ)
    (f : X ⟶ S) [SmoothOfRelativeDimension d f] [IsClosedImmersion (pullback.diagonal f)] :
    ∀ w : (pullback f f : Scheme.{u}), ∃ U : (pullback f f).affineOpens, w ∈ U.1 ∧
      (RingHom.ker ((pullback.diagonal f).app U.1).hom = ⊤ ∨
        ∃ r : List Γ(pullback f f, U.1), r.length = d ∧
          RingTheory.Sequence.IsRegular Γ(pullback f f, U.1) r ∧
          Ideal.ofList r = RingHom.ker ((pullback.diagonal f).app U.1).hom) := by
  classical
  intro w
  let Δ := pullback.diagonal f
  by_cases hw : w ∈ Set.range Δ
  · by_cases hzero : d = 0
    · subst d
      have : Etale f := (Etale.iff_smoothOfRelativeDimension_zero f).mpr inferInstance
      have : IsOpenImmersion Δ := inferInstance
      obtain ⟨_, ⟨U, hU, rfl⟩, hwU, hle⟩ :=
        (pullback f f).isBasis_affineOpens.exists_subset_of_mem_open
          hw Δ.isOpenEmbedding.isOpen_range
      have happ : IsIso (Δ.app U) := Scheme.Hom.isIso_app Δ U hle
      have hker : RingHom.ker (Δ.app U).hom = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).mp
          (ConcreteCategory.bijective_of_isIso (Δ.app U)).1
      have : Nontrivial Γ(pullback f f, U) :=
        ((pullback f f).presheaf.germ U w hwU).hom.domain_nontrivial
      refine ⟨⟨U, hU⟩, hwU, Or.inr ⟨[], rfl, ?_, ?_⟩⟩
      · exact ⟨by simp, by simp⟩
      · simpa using hker.symm
    · let : NeZero d := ⟨hzero⟩
      let : IsSeparated f := ⟨inferInstance⟩
      obtain ⟨U, hwU, r, hr, hreg, hI⟩ :=
        IsRegularImmersion.exists_isWeaklyRegular_generators
          (c := d) (i := Δ) w
      have hker : Ideal.ofList r = RingHom.ker (Δ.app U.1).hom := by
        simpa only [Scheme.Hom.ker_apply] using hI
      refine ⟨U, hwU, Or.inr ⟨r, hr, ⟨hreg, ?_⟩, hker⟩⟩
      rw [Ideal.smul_eq_mul, Ideal.mul_top, hker]
      intro heq
      have hone : (Δ.app U.1).hom 1 = 0 := by
        exact RingHom.mem_ker.mp (heq ▸ (show (1 : Γ(pullback f f, U.1)) ∈ ⊤ from trivial))
      obtain ⟨x, rfl⟩ := hw
      have : Nontrivial Γ(X, Δ ⁻¹ᵁ U.1) :=
        (X.presheaf.germ (Δ ⁻¹ᵁ U.1) x hwU).hom.domain_nontrivial
      simp at hone
  · obtain ⟨_, ⟨U, hU, rfl⟩, hwU, hle⟩ :=
      (pullback f f).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_compl hw) Δ.isClosedEmbedding.isClosed_range.isOpen_compl
    have hempty : Δ ⁻¹ᵁ U = ⊥ := by
      ext x
      simpa using fun hx : Δ x ∈ U ↦ hle hx ⟨x, rfl⟩
    have : Subsingleton Γ(X, Δ ⁻¹ᵁ U) := hempty ▸ inferInstance
    refine ⟨⟨U, hU⟩, hwU, Or.inl ?_⟩
    rw [Ideal.eq_top_iff_one, RingHom.mem_ker]
    exact Subsingleton.elim _ _

end AlgebraicGeometry
