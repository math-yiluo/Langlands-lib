/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import WeilConjectures.Compactification.FiniteTypeExtension

/-!

# Quasi-coherent ideal sheaves as directed suprema of their finite-type subsheaves

This file proves the colimit form of Stacks Project Tag 01PF: on a quasi-compact
quasi-separated scheme, every quasi-coherent ideal sheaf is the supremum of the directed
family of its finite-type quasi-coherent subsheaves, and a finite-type ideal sheaf is a
compact element of the lattice of ideal sheaves.

Together these are the "for large `α`" engine of Conrad's proof of Nagata's compactification
theorem: an ideal sheaf which is not of finite type is written as a filtered union of
finite-type subsheaves, and a finite-type containment then already holds at one member.

## Main results

- `Scheme.IdealSheafData.exists_le_of_ofFiniteType_le_iSup` and
  `Scheme.IdealSheafData.exists_mem_le_of_ofFiniteType_le_sSup`: a finite-type ideal sheaf
  on a quasi-compact scheme is a compact element of the lattice of ideal sheaves
  (blueprint: `lemma:nagata-finite-type-ideal-compact`);
- `Scheme.IdealSheafData.sSup_ofFiniteType_le_eq` and
  `Scheme.IdealSheafData.directedOn_ofFiniteType_le`: a quasi-coherent ideal sheaf on a
  qcqs scheme is the directed supremum of its finite-type subsheaves
  (blueprint: `lemma:nagata-ideal-directed-union-finite-type`);
- `Scheme.IdealSheafData.sSup_ofFiniteType_le_comap_eq_top_eq` and
  `Scheme.IdealSheafData.directedOn_ofFiniteType_le_comap_eq_top`: the same for the cofinal
  subfamily of those subsheaves which restrict to the unit ideal on a prescribed
  quasi-compact open;
- `Scheme.IdealSheafData.exists_ofFiniteType_le_comap_eq_top_of_le` and
  `Scheme.IdealSheafData.exists_ofFiniteType_le_comap_eq_comap_of_comap_eq_top`: the
  "for large `α`" step in the two forms the applications use.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

section Directedness

/-- The finite-type quasi-coherent subsheaves of a quasi-coherent ideal sheaf are directed:
the family is closed under `⊔`. -/
theorem directedOn_ofFiniteType_le (H : X.IdealSheafData) :
    DirectedOn (· ≤ ·) {K : X.IdealSheafData | K ≤ H ∧ K.ofFiniteType} := by
  rintro K₁ ⟨h₁, hf₁⟩ K₂ ⟨h₂, hf₂⟩
  exact ⟨K₁ ⊔ K₂, ⟨sup_le h₁ h₂, hf₁.sup hf₂⟩, le_sup_left, le_sup_right⟩

/-- The finite-type quasi-coherent subsheaves of `H` restricting to the unit ideal on an
open `U` are directed: the family is closed under `⊔`. -/
theorem directedOn_ofFiniteType_le_comap_eq_top (H : X.IdealSheafData) (U : X.Opens) :
    DirectedOn (· ≤ ·)
      {K : X.IdealSheafData | K ≤ H ∧ K.ofFiniteType ∧ K.comap U.ι = ⊤} := by
  rintro K₁ ⟨h₁, hf₁, ht₁⟩ K₂ ⟨h₂, hf₂, -⟩
  refine ⟨K₁ ⊔ K₂, ⟨sup_le h₁ h₂, hf₁.sup hf₂, top_le_iff.mp ?_⟩, le_sup_left, le_sup_right⟩
  rw [← ht₁]
  exact comap_mono U.ι le_sup_left

end Directedness

section Compact

/-- **A finite-type ideal sheaf on a quasi-compact scheme is a compact element**
(blueprint: `lemma:nagata-finite-type-ideal-compact`).

Affine-locally this is the compactness of a finitely generated ideal in a directed supremum
of ideals; quasi-compactness of `X` provides a finite affine cover, and directedness picks
a common index above the finitely many local ones. -/
theorem exists_le_of_ofFiniteType_le_iSup [CompactSpace X] {A : X.IdealSheafData}
    (hA : A.ofFiniteType) {ι : Type*} [Nonempty ι] {B : ι → X.IdealSheafData}
    (hdir : Directed (· ≤ ·) B) (hle : A ≤ ⨆ i, B i) :
    ∃ i, A ≤ B i := by
  classical
  -- on a single affine open the finitely generated ideal `A.ideal U` is a compact element
  have hloc : ∀ U : X.affineOpens, ∃ i, A.ideal U ≤ (B i).ideal U := by
    intro U
    have hcpt : IsCompactElement (A.ideal U) :=
      (Submodule.fg_iff_compact _).mp (hA U le_top)
    have hle' : A.ideal U ≤ ⨆ i, (B i).ideal U := by
      have h := hle U
      rwa [ideal_iSup, iSup_apply] at h
    obtain ⟨s, hs⟩ := hcpt.exists_finset_of_le_iSup
      (fun i ↦ (B i).ideal U) hle'
    have hdir' : Directed (· ≤ ·) fun i ↦ (B i).ideal U := fun i j ↦ by
      obtain ⟨k, hik, hjk⟩ := hdir i j
      exact ⟨k, hik U, hjk U⟩
    obtain ⟨z, hz⟩ := hdir'.finset_le s
    exact ⟨z, hs.trans (iSup₂_le hz)⟩
  choose i hi using hloc
  -- a finite affine cover of `X`, and a common index above the finitely many local ones
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, (U.1 : Set X) := by
    intro x _
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X] at hx
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨U, hU⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ (U.1 : Set X)) (fun U ↦ U.1.isOpen) hcov
  obtain ⟨z, hz⟩ := hdir.finset_le (t.image i)
  refine ⟨z, le_of_iSup_eq_top (fun U : t ↦ (U : X.affineOpens)) ?_ fun U ↦ ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hUt⟩, hxU⟩
  · exact (hi _).trans (hz _ (Finset.mem_image_of_mem i U.2) _)

/-- **A finite-type ideal sheaf on a quasi-compact scheme is a compact element**, in the
form of a supremum over a directed set of ideal sheaves.
(Blueprint: `lemma:nagata-finite-type-ideal-compact`.) -/
theorem exists_mem_le_of_ofFiniteType_le_sSup [CompactSpace X] {A : X.IdealSheafData}
    (hA : A.ofFiniteType) {S : Set X.IdealSheafData} (hS : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) (hle : A ≤ sSup S) :
    ∃ B ∈ S, A ≤ B := by
  have : Nonempty S := hS.to_subtype
  rw [sSup_eq_iSup'] at hle
  obtain ⟨B, hB⟩ := exists_le_of_ofFiniteType_le_iSup hA hdir.directed_val hle
  exact ⟨B, B.2, hB⟩

end Compact

section Directed

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- Every section of a quasi-coherent ideal sheaf over an affine open of a qcqs scheme is a
section of a finite-type quasi-coherent subsheaf.

The finite-type ideal sheaf cut out by the section on the affine open extends to a
finite-type ideal sheaf inside the ambient one by Tag 01PF. -/
theorem exists_ofFiniteType_le_mem_ideal (H : X.IdealSheafData) (V : X.affineOpens)
    {a : Γ(X, V.1)} (ha : a ∈ H.ideal V) :
    ∃ K : X.IdealSheafData, K ≤ H ∧ K.ofFiniteType ∧ a ∈ K.ideal V := by
  have : IsAffine V.1.toScheme := V.2
  set N : Ideal Γ(X, V.1) := Ideal.span {a} with hN
  have hNfg : N.FG := ⟨{a}, by simp [hN]⟩
  have hNle : N ≤ H.ideal V := by rw [hN, Ideal.span_le, Set.singleton_subset_iff]; exact ha
  -- the ideal sheaf on `V` cut out by `a`
  set J : V.1.toScheme.IdealSheafData := ofIdealTop (N.map V.1.topIso.inv.hom) with hJ
  have hJideal : J.ideal ⟨⊤, isAffineOpen_top _⟩ = N.map V.1.topIso.inv.hom :=
    ideal_top_ofIdealTop _
  have hHideal : (H.comap V.1.ι).ideal ⟨⊤, isAffineOpen_top V.1.toScheme⟩ =
      (H.ideal V).map V.1.topIso.inv.hom := by
    rw [← map_topIso_ideal_top_comap_ι H V, Ideal.map_map, ← CommRingCat.hom_comp,
      Iso.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]
  have hJle : J ≤ H.comap V.1.ι :=
    le_of_isAffine (by rw [hJideal, hHideal]; exact Ideal.map_mono hNle)
  -- its maximal quasi-coherent extension, cut down to `H`
  have hcomap : (J.map V.1.ι ⊓ H).comap V.1.ι = J := by
    rw [comap_inf_of_isOpenImmersion, comap_map, inf_eq_left.mpr hJle]
  have hft : (J.map V.1.ι ⊓ H).ofFiniteTypeOn V.1 := by
    rw [ofFiniteTypeOn_iff_comap, hcomap]
    intro U'' _
    rw [hJ, ofIdealTop_ideal]
    exact ((hNfg.map _).map _)
  obtain ⟨K, hKle, hKft, hKcomap⟩ :=
    exists_finiteType_le_comap_eq_of_le (inf_le_right : J.map V.1.ι ⊓ H ≤ H) V.1
      V.2.isCompact hft
  refine ⟨K, hKle, hKft, ?_⟩
  have hKV : K.ideal V = N := by
    rw [← map_topIso_ideal_top_comap_ι K V, hKcomap, hcomap, hJideal, Ideal.map_map,
      ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]
  rw [hKV, hN]
  exact Ideal.subset_span rfl

/-- **A quasi-coherent ideal sheaf on a qcqs scheme is the directed supremum of its
finite-type quasi-coherent subsheaves** (Stacks Project Tag 01PF, colimit form).
(Blueprint: `lemma:nagata-ideal-directed-union-finite-type`.) -/
theorem sSup_ofFiniteType_le_eq (H : X.IdealSheafData) :
    sSup {K : X.IdealSheafData | K ≤ H ∧ K.ofFiniteType} = H := by
  refine le_antisymm (sSup_le fun K hK ↦ hK.1) ?_
  rw [le_def]
  intro V a ha
  obtain ⟨K, hKle, hKft, haK⟩ := exists_ofFiniteType_le_mem_ideal H V ha
  exact le_sSup (show K ∈ {K : X.IdealSheafData | K ≤ H ∧ K.ofFiniteType} from
    ⟨hKle, hKft⟩) V haK

end Directed

section UnitOnOpen

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- A quasi-coherent ideal sheaf restricting to the unit ideal on a quasi-compact open `U`
has a finite-type quasi-coherent subsheaf which still restricts to the unit ideal on `U`. -/
theorem exists_ofFiniteType_le_comap_eq_top (H : X.IdealSheafData) {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hHU : H.comap U.ι = ⊤) :
    ∃ K : X.IdealSheafData, K ≤ H ∧ K.ofFiniteType ∧ K.comap U.ι = ⊤ := by
  have hft : H.ofFiniteTypeOn U := by
    rw [ofFiniteTypeOn_iff_comap, hHU]
    exact ofFiniteType_top
  obtain ⟨K, hKle, hKft, hKcomap⟩ := exists_finiteType_le_comap_eq H U hU hft
  exact ⟨K, hKle, hKft, by rw [hKcomap, hHU]⟩

/-- **The finite-type subsheaves restricting to the unit ideal on `U` are cofinal**
(blueprint: `lemma:nagata-ideal-directed-union-finite-type`). -/
theorem sSup_ofFiniteType_le_comap_eq_top_eq (H : X.IdealSheafData) {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hHU : H.comap U.ι = ⊤) :
    sSup {K : X.IdealSheafData | K ≤ H ∧ K.ofFiniteType ∧ K.comap U.ι = ⊤} = H := by
  refine le_antisymm (sSup_le fun K hK ↦ hK.1) ?_
  obtain ⟨K', hK'le, hK'ft, hK'top⟩ := exists_ofFiniteType_le_comap_eq_top H hU hHU
  -- the smaller family is cofinal in the family of all finite-type subsheaves
  have hcof : sSup {K : X.IdealSheafData | K ≤ H ∧ K.ofFiniteType} ≤
      sSup {K : X.IdealSheafData | K ≤ H ∧ K.ofFiniteType ∧ K.comap U.ι = ⊤} := by
    refine sSup_le fun K hK ↦ le_sup_left.trans (le_sSup (a := K ⊔ K')
      ⟨sup_le hK.1 hK'le, hK.2.sup hK'ft, top_le_iff.mp ?_⟩)
    rw [← hK'top]
    exact comap_mono U.ι le_sup_right
  exact (sSup_ofFiniteType_le_eq H).ge.trans hcof

/-- **The "for large `α`" step**: on a qcqs scheme, a finite-type quasi-coherent subsheaf of
an ideal sheaf `H` restricting to the unit ideal on a quasi-compact open `U` is contained in
a finite-type quasi-coherent subsheaf of `H` which still restricts to the unit ideal on `U`.
(Blueprint: `lemma:nagata-ideal-directed-union-finite-type`.) -/
theorem exists_ofFiniteType_le_comap_eq_top_of_le {A H : X.IdealSheafData}
    (hA : A.ofFiniteType) (hAH : A ≤ H) {U : X.Opens} (hU : IsCompact (U : Set X))
    (hHU : H.comap U.ι = ⊤) :
    ∃ K : X.IdealSheafData, A ≤ K ∧ K ≤ H ∧ K.ofFiniteType ∧ K.comap U.ι = ⊤ := by
  obtain ⟨K', hK'le, hK'ft, hK'top⟩ := exists_ofFiniteType_le_comap_eq_top H hU hHU
  refine ⟨A ⊔ K', le_sup_left, sup_le hAH hK'le, hA.sup hK'ft, top_le_iff.mp ?_⟩
  rw [← hK'top]
  exact comap_mono U.ι le_sup_right

/-- **The "for large `α`" step with a prescribed restriction**: on a qcqs scheme, an ideal
sheaf `H` restricting to the unit ideal on a quasi-compact open `U` and of finite type on a
quasi-compact open `W` has a finite-type quasi-coherent subsheaf with the same restriction
to `W` which still restricts to the unit ideal on `U`.
(Blueprint: `lemma:nagata-ideal-directed-union-finite-type`.) -/
theorem exists_ofFiniteType_le_comap_eq_comap_of_comap_eq_top {H : X.IdealSheafData}
    {U W : X.Opens} (hU : IsCompact (U : Set X)) (hW : IsCompact (W : Set X))
    (hHU : H.comap U.ι = ⊤) (hHW : H.ofFiniteTypeOn W) :
    ∃ K : X.IdealSheafData, K ≤ H ∧ K.ofFiniteType ∧ K.comap W.ι = H.comap W.ι ∧
      K.comap U.ι = ⊤ := by
  obtain ⟨L, hLle, hLft, hLcomap⟩ := exists_finiteType_le_comap_eq H W hW hHW
  obtain ⟨K, hLK, hKle, hKft, hKtop⟩ :=
    exists_ofFiniteType_le_comap_eq_top_of_le hLft hLle hU hHU
  refine ⟨K, hKle, hKft, le_antisymm (comap_mono W.ι hKle) ?_, hKtop⟩
  rw [← hLcomap]
  exact comap_mono W.ι hLK

end UnitOnOpen

end AlgebraicGeometry.Scheme.IdealSheafData
