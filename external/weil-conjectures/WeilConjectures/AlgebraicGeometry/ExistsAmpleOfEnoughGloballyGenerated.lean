/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import all WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.AlgebraicGeometry.FiniteSectionsCover
import WeilConjectures.AlgebraicGeometry.TensorSectionAffineOpen
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Enough globally generated invertible modules give an ample module

Source: Stacks Project, Varieties, Lemma 09NC
(blueprint: lem-sc-enough-globally-generated-ample).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules


open CategoryTheory MonoidalCategory Opposite in
private noncomputable def sectionFromTop {X : Scheme.{u}} (L : X.Modules)
    (s : L.val.presheaf.obj (op ⊤)) : L.sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ L.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op s)
    (by
      intro U V f
      rw [← L.val.map_comp_apply]
      rfl)

open CategoryTheory MonoidalCategory Opposite in
private theorem sectionFromTop_top {X : Scheme.{u}} (L : X.Modules)
    (s : L.val.presheaf.obj (op ⊤)) : (sectionFromTop L s).val (op ⊤) = s := by
  change L.val.map (𝟙 (op ⊤)) s = s
  rw [L.val.map_id]
  rfl

open CategoryTheory MonoidalCategory Opposite in
private theorem positiveTensorFamily_invertible {X : Scheme.{u}} (n : ℕ)
    (L : Fin (n + 1) → X.Modules) (hL : ∀ i, (L i).IsInvertible) :
    (positiveTensorFamily n L).IsInvertible := by
  induction n with
  | zero => exact hL 0
  | succ n ih =>
    have := ih (fun i ↦ L i.castSucc) (fun i ↦ hL i.castSucc)
    have := hL (Fin.last (n + 1))
    change (positiveTensorFamily n (fun i ↦ L i.castSucc) ⊗ L (Fin.last (n + 1))).IsInvertible
    infer_instance

/-- A quasi-compact scheme with an affine nonvanishing neighbourhood of each point supplied
by a section of a globally generated invertible module has an ample invertible module.
Source: Stacks Project, Varieties, Lemma 09NC
(blueprint: lem-sc-enough-globally-generated-ample).

Proof: quasi-compactness gives finitely many pairs `(Lᵢ, sᵢ)` whose affine loci cover
(`def-weil-pbc-quasi-compact-scheme`). For each `Lᵢ`, choose finitely many sections whose
nonvanishing loci cover, using `lem-sc-finite-sections-cover-qc`, and add `sᵢ` as index zero.
Form the tensor product of the `Lᵢ` (`def-sc-positive-tensor-family`); it is invertible
by induction using the proved `IsInvertible.tensorObj` instance (the tensor clause of
`lem-pc-tensor-dual-invertible`). Tensor the chosen sections for every multi-index.
If one index is zero, the tensor section has affine nonvanishing locus by
`lem-sc-tensor-section-affine-open`. These loci cover: at any point choose nonvanishing
sections in all factors, choosing index zero in a factor whose original affine locus
contains the point. These degree-one sections witness `def-weil-pbc-ample-invertible-module`.
Transport the sections to tensor power one with the inverse right unitor, which preserves
nonvanishing loci. For the empty scheme use the structure sheaf (the empty tensor product).
For nonempty `X`, append one input factor to the finite subcover to use the positive-family API.
-/
theorem exists_isAmple_of_enough_globallyGenerated (X : Scheme.{u}) [CompactSpace X]
    (h : ∀ x : X, ∃ L : X.Modules, L.IsInvertible ∧
      Nonempty (SheafOfModules.GeneratingSections L) ∧
      ∃ s : L.val.presheaf.obj (Opposite.op ⊤), ∃ U : X.Opens,
        (U : Set X) = nonvanishingLocus L s ∧ x ∈ U ∧ IsAffineOpen U) :
    ∃ (L : X.Modules) (hL : L.IsInvertible), @IsAmple X L hL := by
  classical
  by_cases hempty : IsEmpty X
  · let := hempty
    refine ⟨CategoryTheory.MonoidalCategory.tensorUnit X.Modules, inferInstance, inferInstance, ?_⟩
    intro x
    exact isEmptyElim x
  have : Nonempty X := not_isEmpty_iff.mp hempty
  choose L hL hG s U hU hx hA using h
  obtain ⟨f, hf⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (U x : Set X)) (fun x ↦ (U x).isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let e := f.equivFin
  let a : Fin (f.card + 1) → X :=
    Fin.lastCases (Classical.arbitrary X) (fun i ↦ (e.symm i).val)
  let M : Fin (f.card + 1) → X.Modules := fun i ↦ L (a i)
  have : ∀ i, (M i).IsInvertible := fun i ↦ hL (a i)
  have hMG : ∀ i, Nonempty (SheafOfModules.GeneratingSections (M i)) :=
    fun i ↦ hG (a i)
  let N := positiveTensorFamily f.card M
  have : N.IsInvertible :=
    positiveTensorFamily_invertible f.card M (fun i ↦ hL (a i))
  obtain ⟨m, t, ht⟩ : ∃ (m : Fin (f.card + 1) → ℕ)
      (t : (i : Fin (f.card + 1)) → Fin (m i) → (M i).val.presheaf.obj (Opposite.op ⊤)),
      ∀ i, ⋃ j, nonvanishingLocus (M i) (t i j) = Set.univ := by
    have hc := fun i ↦ finite_sections_cover_of_globally_generated X (M i) (hMG i)
    choose m t ht using hc
    exact ⟨m, t, ht⟩
  refine ⟨N, inferInstance, inferInstance, ?_⟩
  intro x
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (hf (Set.mem_univ x))
  let j : Fin (f.card + 1) := (e ⟨z, hz⟩).castSucc
  have haj : a j = z := by simp [a, j, e]
  have hxs : x ∈ nonvanishingLocus (M j) (s (a j)) := by
    rw [← hU (a j)]
    simpa [haj] using hxz
  have hc : ∀ i, ∃ k, x ∈ nonvanishingLocus (M i) (t i k) := by
    intro i
    apply Set.mem_iUnion.mp
    rw [ht i]
    exact Set.mem_univ x
  choose k hk using hc
  let v : (i : Fin (f.card + 1)) → (M i).val.presheaf.obj (Opposite.op ⊤) :=
    fun i ↦ if i = j then s (a i) else t i (k i)
  let w : (i : Fin (f.card + 1)) → (M i).sections :=
    fun i ↦ sectionFromTop (M i) (v i)
  have hw : ∀ i, x ∈ nonvanishingLocus (M i) ((w i).val (Opposite.op ⊤)) := by
    intro i
    rw [sectionFromTop_top]
    by_cases hij : i = j
    · subst i
      simpa [v] using hxs
    · simpa [v, hij] using hk i
  obtain ⟨heq, haff⟩ := tensor_section_affine_open f.card M w
  obtain ⟨V, hV, hVN⟩ := haff (by
    refine ⟨j, U (a j), hA (a j), ?_⟩
    simpa [w, sectionFromTop_top, v] using hU (a j))
  let q := (positiveTensorFamilySection f.card M w).val (Opposite.op ⊤)
  have hxV : x ∈ V := by
    change x ∈ (V : Set X)
    rw [hVN, heq]
    exact Set.mem_iInter.mpr hw
  let b : CategoryTheory.Iso N (N.tensorPow 1) :=
    (CategoryTheory.MonoidalCategory.rightUnitor N).symm
  refine ⟨1, Nat.zero_lt_one, b.hom.app ⊤ q, V, hxV, hV, ?_⟩
  intro y
  change y ∈ V ↔ y ∈ nonvanishingLocus (N.tensorPow 1) (b.hom.app ⊤ q)
  rw [nonvanishingLocus_iso b q, ← hVN]
  rfl

end AlgebraicGeometry.Scheme.Modules
