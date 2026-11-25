/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Induction along open-closed decompositions

A property of quasi-compact schemes over a base `S` that holds for affine schemes and that
holds for `X` as soon as it holds for an open subscheme `U` and the complementary closed
subscheme `Z` holds for every quasi-compact scheme over `S`. This is the localization step
(Step 5) of the proof of blueprint `theorem-trace-formula-frobenius-correspondence--1`: covering `X`
by affine opens `U_1, …, U_N`, the closed complement of `U_1 ∪ ⋯ ∪ U_{i-1}` in
`U_1 ∪ ⋯ ∪ U_i` is closed in the affine `U_i`, hence affine.

## Main results

- `AlgebraicGeometry.Scheme.induction_on_isCompl`: the induction principle.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A closed subscheme of `Y` that is set-theoretically contained in an affine open `W` of `Y`
is affine. -/
lemma isAffine_of_isClosedImmersion_of_range_subset {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] {W : Y.Opens} (hW : IsAffineOpen W) (h : Set.range i ⊆ W) :
    IsAffine Z := by
  have : IsAffine W := hW
  have h' : Set.range i ⊆ Set.range W.ι := by simpa using h
  have : IsClosedImmersion (IsOpenImmersion.lift W.ι i h' ≫ W.ι) := by
    rwa [IsOpenImmersion.lift_fac]
  have := IsClosedImmersion.of_comp (IsOpenImmersion.lift W.ι i h') W.ι
  exact isAffine_of_isAffineHom (IsOpenImmersion.lift W.ι i h')

/-- The range of the inclusion `V ⟶ V'` of opens `V ≤ V'` is the preimage of `V` in `V'`. -/
lemma range_homOfLE {X : Scheme.{u}} {V V' : X.Opens} (e : V ≤ V') :
    Set.range (X.homOfLE e) = (V'.ι ⁻¹ᵁ V : Set V'.toScheme) := by
  rw [← Set.preimage_image_eq (Set.range (X.homOfLE e)) V'.ι.isOpenEmbedding.injective,
    ← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, Scheme.homOfLE_ι]
  simp

/-- An open subscheme whose underlying set is compact is a compact space. -/
lemma Opens.compactSpace_of_isCompact {X : Scheme.{u}} {V : X.Opens}
    (hV : IsCompact (V : Set X)) : CompactSpace V.toScheme :=
  isCompact_iff_compactSpace.mp hV

/-- The inductive step of `induction_on_isCompl`: if `P` holds for a quasi-compact open `V` of
`X`, then it holds for `V ⊔ U` for any affine open `U`. -/
lemma induction_on_isCompl_sup {S : Scheme.{u}} (P : ∀ {X : Scheme.{u}}, (X ⟶ S) → Prop)
    (affine : ∀ {X : Scheme.{u}} (f : X ⟶ S), IsAffine X → P f)
    (isCompl : ∀ {X U Z : Scheme.{u}} (f : X ⟶ S) (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j]
      [IsClosedImmersion i], CompactSpace X → CompactSpace U →
      IsCompl (Set.range j.base) (Set.range i.base) → P (j ≫ f) → P (i ≫ f) → P f)
    {X : Scheme.{u}} (f : X ⟶ S) {V U : X.Opens} (hV : IsCompact (V : Set X))
    (hU : IsAffineOpen U) (hP : P (V.ι ≫ f)) : P ((V ⊔ U).ι ≫ f) := by
  refine isCompl ((V ⊔ U).ι ≫ f) (X.homOfLE le_sup_left) ((V ⊔ U).ι ⁻¹ᵁ V).closedComplement
    (Opens.compactSpace_of_isCompact (hV.union hU.isCompact))
    (Opens.compactSpace_of_isCompact hV) ?_ ?_ ?_
  · rw [range_homOfLE, Opens.range_closedComplement]
    exact isCompl_compl
  · rwa [← Category.assoc, Scheme.homOfLE_ι]
  · refine affine _ (isAffine_of_isClosedImmersion_of_range_subset
      ((V ⊔ U).ι ⁻¹ᵁ V).closedComplement
      (hU.preimage_of_isOpenImmersion (V ⊔ U).ι (by simp)) ?_)
    rw [Opens.range_closedComplement]
    intro y hy
    have hy' : (V ⊔ U).ι y ∈ V ⊔ U := by
      rw [← SetLike.mem_coe, ← Opens.range_ι]
      exact Set.mem_range_self y
    exact (TopologicalSpace.Opens.mem_sup.mp hy').resolve_left hy

/-- Induction along open-closed decompositions: let `P` be a property of schemes `X` over `S`
that holds for affine `X`, and that holds for `X` whenever it holds for a quasi-compact open
subscheme `j : U ⟶ X` and the complementary closed subscheme `i : Z ⟶ X`. Then `P` holds for
every quasi-compact scheme over `S`. -/
theorem induction_on_isCompl {S : Scheme.{u}} (P : ∀ {X : Scheme.{u}}, (X ⟶ S) → Prop)
    (affine : ∀ {X : Scheme.{u}} (f : X ⟶ S), IsAffine X → P f)
    (isCompl : ∀ {X U Z : Scheme.{u}} (f : X ⟶ S) (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j]
      [IsClosedImmersion i], CompactSpace X → CompactSpace U →
      IsCompl (Set.range j.base) (Set.range i.base) → P (j ≫ f) → P (i ≫ f) → P f)
    {X : Scheme.{u}} (f : X ⟶ S) [CompactSpace X] : P f := by
  obtain ⟨s, hs, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
    (by simpa using isCompact_univ)
  have key (t : Set X.affineOpens) (ht : t.Finite) : P ((⨆ i ∈ t, (i : X.Opens)).ι ≫ f) := by
    induction t, ht using Set.Finite.induction_on with
    | empty =>
      rw [iSup_emptyset]
      exact affine _ (isAffineOpen_bot X)
    | @insert a t _ ht hP =>
      rw [iSup_insert, sup_comm]
      exact induction_on_isCompl_sup P affine isCompl f
        (isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr ⟨t, ht, rfl⟩) a.2 hP
  have key := key s hs
  rw [← e] at key
  refine isCompl f (⊤ : X.Opens).ι (⊤ : X.Opens).closedComplement ‹_›
    (Opens.compactSpace_of_isCompact (by simpa using isCompact_univ)) ?_ key ?_
  · rw [Opens.range_ι, Opens.range_closedComplement]
    exact isCompl_compl
  · refine affine _ (isAffine_of_isClosedImmersion_of_range_subset
      (⊤ : X.Opens).closedComplement (isAffineOpen_bot X) ?_)
    rw [Opens.range_closedComplement]
    simp

end AlgebraicGeometry.Scheme
