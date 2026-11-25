/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import WeilConjectures.AlgebraicGeometry.FlatQuasiFiniteStratification
import WeilConjectures.AlgebraicGeometry.FlatFpLqfBoundedStratification
import WeilConjectures.AlgebraicGeometry.HasUniversallyBoundedFibersOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite

/-!
# Constructible finite stratifications of flat quasi-finite morphisms

Source: Stacks Project, More on Morphisms, Tags 07RY and 07RZ, using the bounded
closed degree filtration and quasi-compactness of its successive differences
(blueprint: lem-weil-pbc-etale-separated-stratified-finite-intermediate).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Realize a locally closed set by the vanishing-ideal closed subscheme of an open
subscheme. Source: Stacks Project, Schemes, Tag 01J3; Mathlib's `vanishingIdeal` and
`range_subschemeι`. -/
private theorem exists_immersion_of_locallyClosed {X : Scheme.{u}} {s : Set X}
    (hs : IsLocallyClosed s) :
    ∃ (T : Scheme.{u}) (g : T ⟶ X), IsImmersion g ∧ Set.range g = s := by
  obtain ⟨O, C, hO, hC, rfl⟩ := hs
  let V : X.Opens := ⟨O, hO⟩
  let D : TopologicalSpace.Closeds V.toScheme :=
    ⟨V.ι ⁻¹' C, hC.preimage V.ι.continuous⟩
  let I := IdealSheafData.vanishingIdeal D
  refine ⟨I.subscheme, I.subschemeι ≫ V.ι, inferInstance, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  simp only [I, IdealSheafData.range_subschemeι,
    IdealSheafData.coe_support_vanishingIdeal]
  change V.ι '' (V.ι ⁻¹' C) = O ∩ C
  rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm]
  rfl

/-- A flat locally finitely presented separated quasi-finite morphism over a qcqs scheme
admits a finite constructible locally closed stratification on whose strata it is finite.
This packages the construction from the closed degree filtration, including the induced
subscheme structures. Source: More on Morphisms, Lemma Tag 07RZ.
(blueprint: lem-weil-pbc-etale-separated-stratified-finite-intermediate)
-/
theorem exists_constructible_stratified_finite
    {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [Flat j] [LocallyOfFinitePresentation j] [IsSeparated j]
    (hj : j.IsQuasiFinite) :
    ∃ S : Stratification X,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      (∀ i : Fin S.n, IsFinite (pullback.snd j (S.immersion i))) := by
  classical
  have : QuasiCompact j := hj.2.1
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  have hloc := (Hom.isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact j).mp hj
  obtain ⟨N, hN⟩ := Hom.hasUniversallyBoundedFibers_of_isLocallyQuasiFinite j hloc.1
  obtain ⟨Z, hZ0, hZclosed, hZmono, hZdisj, hZcover, hZuniv, hZqc⟩ :=
    Hom.exists_closed_stratification_of_flat_quasiFinite j hj
  obtain ⟨B, hB0, hBclosed, hBmono, hBN, hBdisj, hBcover, hBuniv⟩ :=
    Hom.exists_flat_fp_lqf_bounded_stratification j hloc.1 N hN
  -- Testing both universal properties on residue-field points identifies their strata.
  have heq (r : ℕ) : Z (r + 1) \ Z r = B (r + 1) \ B r := by
    ext x
    have hz := hZuniv _ (X.fromSpecResidueField x) r
    have hb := hBuniv _ (X.fromSpecResidueField x) r
    simpa only [X.range_fromSpecResidueField, Set.singleton_subset_iff] using
      hz.symm.trans hb
  have hempty (r : ℕ) (hr : N + 1 ≤ r) : Z (r + 1) \ Z r = ∅ := by
    rw [heq]
    have hBr : B r = Set.univ := Set.eq_univ_of_univ_subset (hBN ▸ hBmono hr)
    simp [hBr]
  let A : Fin (N + 1) → Set X := fun i ↦ Z (i.val + 1) \ Z i.val
  have hcover : ⋃ i, A i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ r, Z (r + 1) \ Z r := by rw [hZcover]; trivial
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
    have hlt : r < N + 1 := by
      by_contra h
      rw [hempty r (Nat.le_of_not_gt h)] at hr
      exact hr
    exact Set.mem_iUnion.mpr ⟨⟨r, hlt⟩, hr⟩
  have hcompact (i : Fin (N + 1)) : IsCompact (A i) := by
    simpa using hZqc i.val ⊤ isCompact_univ
  -- A filtration complement is a finite union of the compact higher-degree strata.
  have hcompl (k : ℕ) : (Z k)ᶜ = ⋃ i : Fin (N + 1),
      if k ≤ i.val then A i else ∅ := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ ⋃ i, A i := by rw [hcover]; trivial
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
      have hk : k ≤ i.val := by
        by_contra h
        exact hx (hZmono (by omega) hi.1)
      exact Set.mem_iUnion.mpr ⟨i, by simpa [hk] using hi⟩
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      split_ifs at hi with hk
      · exact fun hxk ↦ hi.2 (hZmono hk hxk)
      · exact hi.elim
  have hcon (k : ℕ) : Topology.IsConstructible (Z k) := by
    have hc : IsCompact (Z k)ᶜ := by
      rw [hcompl]
      apply isCompact_iUnion
      intro i
      split_ifs
      · exact hcompact i
      · exact isCompact_empty
    simpa using (hc.isConstructible (hZclosed k).isOpen_compl).compl
  have hlc (i : Fin (N + 1)) : IsLocallyClosed (A i) := by
    refine ⟨(Z i.val)ᶜ, Z (i.val + 1), (hZclosed _).isOpen_compl, hZclosed _, ?_⟩
    ext x
    simp [A, and_comm]
  have hac (i : Fin (N + 1)) : Topology.IsConstructible (A i) :=
    (hcon (i.val + 1)).sdiff (hcon i.val)
  -- Realize each locally closed difference as an immersed subscheme.
  choose T g hg hrange using fun i ↦ exists_immersion_of_locallyClosed (hlc i)
  let S : Stratification X :=
    { n := N + 1
      stratum := A
      isLocallyClosed_stratum := hlc
      isConstructible_stratum := hac
      iUnion_stratum_eq_univ := hcover
      pairwise_disjoint_stratum := fun i k hik ↦ hZdisj (by
        intro h
        exact hik (Fin.ext h))
      domain := T
      immersion := g
      isImmersion := hg
      range_immersion := hrange }
  refine ⟨S, hac, fun i ↦ ?_⟩
  have hf := (hZuniv (T i) (g i) i.val).mpr (by rw [hrange])
  exact hf.toIsFiniteLocallyFree.toIsFinite

end AlgebraicGeometry.Scheme
