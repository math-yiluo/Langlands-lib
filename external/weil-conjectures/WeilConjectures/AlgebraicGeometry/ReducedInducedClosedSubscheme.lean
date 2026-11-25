/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# The reduced induced closed subscheme

Source: Stacks Project, Schemes, Lemma 26.12.4 (Tag 01J3) and Definition 26.12.5
(Tag 01J4) (blueprint: lem-weil-pbc-reduced-induced-closed-subscheme).

Quasi-coherent ideal sheaves are represented by `Scheme.IdealSheafData`: their affine
ideals localize on basic opens. `idealOfOpens` gives their sections on arbitrary opens.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Stacks Project, Tags 01J3 and 01J4.
(blueprint: lem-weil-pbc-reduced-induced-closed-subscheme)

The vanishing ideal is the quasi-coherent sheaf of sections vanishing at the points of `T`.
On each affine open its ideal is the unique radical ideal with the specified zero locus;
localization on basic opens expresses equality with the associated ideal sheaf. Its closed
subscheme is reduced, has image `T`, and is unique up to a unique isomorphism over `X`.

Proof, following the nine steps of the node:
1. Evaluation is germ followed by the residue map (def-weil-residue-field); its kernels
   form ideals compatible with restriction. Pointwise vanishing is local, hence a sheaf.
2. On an affine open the closed set is the zero locus of a unique radical ideal, by
   lem-weil-pbc-affine-open-spec-points and lem-weil-pbc-zero-locus-eq-iff-radical-eq.
3. Evaluation vanishes exactly at the corresponding prime
   (lem-weil-pbc-affine-open-section-vanishing-prime), so the ideal is the intersection
   of those primes, hence the radical ideal of step 2.
4. On a basic open the same condition gives the localization of this ideal
   (lem-weil-pbc-basic-open-function and lem-weil-pbc-affine-open-section-vanishing-prime).
5. The ideal sheaf and the associated module agree on the basis of basic opens, hence
   agree as subsheaves; thus the ideal sheaf is quasi-coherent (pqf-def-coherent,
   lem-weil-pbc-spec-tilde-free-module, lem-weil-pbc-spec-module-tilde-sections and
   lem-weil-pbc-affine-tilde-gamma-adjunction).
6. The quasi-coherent ideal cuts out a closed immersion, locally the quotient spectrum,
   whose image is the given zero locus (lem-weil-pbc-quasi-coherent-ideal-closed-subscheme).
7. Quotients by radical ideals are reduced; reducedness is affine-local
   (lem-weil-pbc-affine-scheme-reduced-iff and def-pc-reduced-scheme).
8. For another reduced closed immersion, its affine kernel ideals are radical with the
   same zero loci, hence equal. Equality on the affine basis gives equality of ideal sheaves
   (def-sbc-closed-immersion-ideal-sheaf and lem-weil-pbc-zero-locus-eq-iff-radical-eq).
9. Equal ideal sheaves give a unique isomorphism over the ambient scheme
   (lem-weil-pbc-closed-immersions-equal-ideal-isomorphic). -/
theorem reduced_induced_closed_subscheme (X : Scheme.{u}) (T : TopologicalSpace.Closeds X) :
    (∀ (U : X.Opens) (f : Γ(X, U)),
      f ∈ (vanishingIdeal T).idealOfOpens U ↔
        ∀ (t : X) (ht : t ∈ U), t ∈ T → X.evaluation U t ht f = 0) ∧
    (∀ U : X.affineOpens,
      (∃! I : Ideal Γ(X, U), I.IsRadical ∧
        PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) = U.2.fromSpec ⁻¹' (T : Set X)) ∧
      (vanishingIdeal T).ideal U = PrimeSpectrum.vanishingIdeal
        (U.2.fromSpec ⁻¹' (T : Set X)) ∧
      (∀ g : Γ(X, U),
        ((vanishingIdeal T).ideal U).map
          (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom =
            (vanishingIdeal T).ideal (X.affineBasicOpen g))) ∧
    IsClosedImmersion (vanishingIdeal T).subschemeι ∧
    IsReduced (vanishingIdeal T).subscheme ∧
    (vanishingIdeal T).subschemeι.ker = vanishingIdeal T ∧
    Set.range (vanishingIdeal T).subschemeι = (T : Set X) ∧
    (∀ U : X.affineOpens,
      IsPullback ((vanishingIdeal T).subschemeCover.f U)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((vanishingIdeal T).ideal U))))
        (vanishingIdeal T).subschemeι U.2.fromSpec) ∧
    (∀ (Z' : Scheme.{u}) (i' : Z' ⟶ X) [IsClosedImmersion i'] [IsReduced Z'],
      Set.range i' = (T : Set X) →
        i'.ker = vanishingIdeal T ∧
          ∃! φ : Z' ≅ (vanishingIdeal T).subscheme,
            φ.hom ≫ (vanishingIdeal T).subschemeι = i') := by
  classical
  have hrange : Set.range (vanishingIdeal T).subschemeι = (T : Set X) := by
    simp
  refine ⟨?_, ?_, inferInstance, inferInstance, ker_subschemeι _, hrange,
    fun U ↦ isPullback_subschemeCover_map _ U, ?_⟩
  · intro U f
    rw [mem_idealOfOpens_iff, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
    constructor
    · intro h t ht hT
      rw [X.evaluation_eq_zero_iff_notMem_basicOpen]
      have hT' : t ∈ Set.range (vanishingIdeal T).subschemeι := by
        change t ∈ (T : Set X) at hT
        rwa [hrange]
      obtain ⟨z, rfl⟩ := hT'
      intro hz
      have : z ∈ (vanishingIdeal T).subschemeι ⁻¹ᵁ X.basicOpen f := hz
      rw [h] at this
      exact this
    · intro h
      apply le_antisymm _ bot_le
      intro z hz
      exact (X.evaluation_eq_zero_iff_notMem_basicOpen _
        (X.basicOpen_le f hz) f).mp
          (h _ (X.basicOpen_le f hz) (by
            change (vanishingIdeal T).subschemeι z ∈ (T : Set X)
            rw [← hrange]
            exact Set.mem_range_self z)) hz
  · intro U
    refine ⟨?_, rfl, fun g ↦ (vanishingIdeal T).map_ideal_basicOpen U g⟩
    let S := U.2.fromSpec ⁻¹' (T : Set X)
    have hc : IsClosed S := T.isClosed.preimage U.2.fromSpec.continuous
    have hv : PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal S :
        Set Γ(X, U)) = S := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hc.closure_eq]
    refine ⟨PrimeSpectrum.vanishingIdeal S,
      ⟨PrimeSpectrum.isRadical_vanishingIdeal _, hv⟩, ?_⟩
    intro I hI
    calc
      I = I.radical := hI.1.radical.symm
      _ = PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (I : Set Γ(X, U))) :=
        (PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical I).symm
      _ = PrimeSpectrum.vanishingIdeal S := congrArg _ hI.2
  · intro Z' i' _ _ hi
    have hk : i'.ker = vanishingIdeal T := by
      rw [i'.ker_eq_vanishingIdeal]
      congr 1
      apply TopologicalSpace.Closeds.ext
      change closure (Set.range i') = (T : Set X)
      rw [hi, T.isClosed.closure_eq]
    refine ⟨hk, ?_⟩
    let l := IsClosedImmersion.lift (vanishingIdeal T).subschemeι i'
      (by rw [ker_subschemeι, hk])
    have hl : l ≫ (vanishingIdeal T).subschemeι = i' :=
      IsClosedImmersion.lift_fac _ _ _
    have : IsIso l := IsClosedImmersion.isIso_of_ker_eq i' _ l hl
      (by rw [ker_subschemeι, hk])
    refine ⟨asIso l, hl, ?_⟩
    intro φ hφ
    apply Iso.ext
    apply (cancel_mono (vanishingIdeal T).subschemeι).mp
    exact hφ.trans hl.symm

end AlgebraicGeometry.Scheme.IdealSheafData
