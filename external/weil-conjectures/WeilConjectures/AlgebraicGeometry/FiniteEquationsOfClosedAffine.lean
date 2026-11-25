/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeQuotientApproximation

/-! Finite principal equations for a degree sublevel locus on an affine open. -/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

set_option backward.isDefEq.respectTransparency.types false in
private theorem range_affine_quotient
    {S : Scheme.{u}} {W : S.Opens} (hW : IsAffineOpen W) (I : Ideal Γ(S, W)) :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hW.fromSpec) =
      S.zeroLocus (U := W) I ∩ W := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  change hW.fromSpec '' Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  exact hW.fromSpec_image_zeroLocus I

/-- The degree sublevel locus restricted to an affine open is the zero locus of a finitely
    generated ideal.

Source: Stacks Project, More on Morphisms, Tag 07RZ, proof, second paragraph
(blueprint: lem-weil-pbc-finite-equations-of-isClosed-inter-affine).

Proof: identify the affine open with the spectrum of its coordinate ring. The closed sublevel
locus is represented by an ideal. Express that ideal as a filtered union of finitely generated
subideals and descend the finite locally free degree-r morphism to one such subideal. The
universal degree criterion then shows that this subideal has the same vanishing locus.
-/
theorem exists_finitely_generated_zeroLocus_ideal_degree_sublevel_inter_affine
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] (hf : f.IsQuasiFinite)
    (r : ℕ) (W : S.Opens) (hW : IsAffineOpen W)
    (hclosed : IsClosed {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r})
    (hdegree : ∀ (T : Scheme.{u}) (g : T ⟶ S),
      (pullback.snd f g).IsFiniteLocallyFreeOfDegree r ↔
        Set.range g ⊆ {s : S | (f.fiberToSpecResidueField s).finrankΓ = r})
    (hWge : ∀ s : S, s ∈ W → r ≤ (f.fiberToSpecResidueField s).finrankΓ) :
    ∃ I : Ideal Γ(S, W), I.FG ∧ ∀ s : S, s ∈ W →
      (s ∈ {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r} ↔
        s ∈ S.zeroLocus (U := W) I) := by
  classical
  let Z : Set S := {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r}
  let I : Ideal Γ(S, W) := PrimeSpectrum.vanishingIdeal (hW.fromSpec ⁻¹' Z)
  have hZI : PrimeSpectrum.zeroLocus (I : Set Γ(S, W)) = hW.fromSpec ⁻¹' Z := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact (hclosed.preimage hW.fromSpec.continuous).closure_eq
  have hIZ : S.zeroLocus (U := W) I ∩ W = Z ∩ W := by
    rw [← hW.fromSpec_image_zeroLocus, hZI, Set.image_preimage_eq_inter_range,
      hW.range_fromSpec]
  let g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hW.fromSpec
  have hg : Set.range g = Z ∩ W := (range_affine_quotient hW I).trans hIZ
  have hfree : (pullback.snd f g).IsFiniteLocallyFreeOfDegree r := by
    apply (hdegree _ g).2
    intro s hs
    obtain ⟨hz, hw⟩ := hg ▸ hs
    exact Nat.le_antisymm hz (hWge s hw)
  have : QuasiCompact f := hf.2.1
  obtain ⟨J, hJI, hJ, hfreeJ⟩ :=
    exists_fg_subideal_isFiniteLocallyFreeOfDegree f Γ(S, W) hW.fromSpec I r hfree
  refine ⟨J, hJ, ?_⟩
  intro s hs
  constructor
  · intro hz
    have hi : s ∈ S.zeroLocus (U := W) I := by
      have hm : s ∈ Z ∩ W := ⟨hz, hs⟩
      exact (hIZ.symm ▸ hm).1
    exact S.zeroLocus_mono hJI hi
  · intro hj
    have hrange : s ∈ Set.range
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hW.fromSpec) := by
      rw [range_affine_quotient hW J]
      exact ⟨hj, hs⟩
    have heq := (hdegree _ _).1 hfreeJ hrange
    exact Nat.le_of_eq heq

/-- A finitely generated ideal on an affine open has finitely many principal equations.

Source: Stacks Project, More on Morphisms, Tag 07RZ, proof, second paragraph
(blueprint: lem-weil-pbc-finite-equations-of-finitely-generated-zeroLocus).

Proof: choose a finite generating set for the ideal; membership in its zero locus is equivalent
to avoiding every corresponding basic open.
-/
theorem exists_finite_equations_of_finitely_generated_zeroLocus
    {S : Scheme.{u}} {W : S.Opens} {I : Ideal Γ(S, W)} (hI : I.FG) :
    ∃ t : Finset Γ(S, W), ∀ s : S, s ∈ W →
      (s ∈ S.zeroLocus (U := W) I ↔ ∀ a ∈ t, s ∉ S.basicOpen a) := by
  obtain ⟨t, ht⟩ := hI
  refine ⟨t, ?_⟩
  intro s hs
  rw [← ht, Scheme.zeroLocus_span]
  simp only [Scheme.mem_zeroLocus_iff, Finset.mem_coe]

end AlgebraicGeometry.Scheme.Hom
