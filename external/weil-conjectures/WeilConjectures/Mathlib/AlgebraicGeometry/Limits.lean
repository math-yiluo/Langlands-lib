/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Dense affine covers of schemes with finitely many irreducible components

A quasi-compact scheme with finitely many irreducible components admits a finite
affine open cover whose total intersection contains every generic point, and is
therefore dense (Stacks Project Tag 01ZX, simplified for the finite-components case;
blueprint `lemma:nagata-dense-affine-cover-exists`):

- `AlgebraicGeometry.exists_isAffineOpen_mem_and_genericPoints_subset`: every point
  has an affine open neighbourhood containing all generic points, obtained as the
  disjoint union of an affine neighbourhood of the point avoiding the components the
  point does not lie on with one small affine neighbourhood of each remaining generic
  point;
- `AlgebraicGeometry.exists_isAffineOpen_iSup_eq_top_and_genericPoints_subset_iInter`:
  the finite affine open cover with dense total intersection, extracted from the
  previous lemma by quasi-compactness.

We also record `AlgebraicGeometry.sigmaSpec_comp_Spec_map_algebraMap`: under
`∐_ι Spec k ≅ Spec (ι → k)` the fold map to `Spec k` is `Spec` of the diagonal, and
`AlgebraicGeometry.Scheme.isEmpty_of_subsingleton_Γ`: a scheme whose ring of global sections is
zero is empty, and `AlgebraicGeometry.exists_comp_sigmaι_eq_of_subsingleton`: a morphism from a
one-point scheme into a coproduct factors through one of the summands.
-/

@[expose] public section

universe u

open TopologicalSpace Set

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **Affine neighbourhoods containing all generic points**: every point `x` of a
scheme with finitely many irreducible components has an affine open neighbourhood
containing every generic point. The neighbourhood is the disjoint union of an affine
open `W ∋ x` avoiding the components not through `x` — which automatically contains
the generic points of the components through `x` — with, for each remaining generic
point, a small affine open around it avoiding `closure W` and all other components.
(Stacks Project Tag 01ZX, simplified for the finite-components case; blueprint
`lemma:nagata-dense-affine-cover-exists`.) -/
theorem exists_isAffineOpen_mem_and_genericPoints_subset
    (hX : (irreducibleComponents X).Finite) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ genericPoints X ⊆ ↑U := by
  classical
  have hcl : ∀ Z ∈ irreducibleComponents X, IsClosed Z := fun Z hZ =>
    isClosed_of_mem_irreducibleComponents Z hZ
  -- distinct irreducible components are incomparable
  have hmax : ∀ Z ∈ irreducibleComponents X, ∀ Z' ∈ irreducibleComponents X,
      Z ⊆ Z' → Z = Z' := fun Z hZ Z' hZ' h => le_antisymm h (hZ.2 hZ'.1 h)
  -- a generic point lies in no irreducible component other than its own
  have hgen_not_mem : ∀ η ∈ genericPoints X, ∀ Z ∈ irreducibleComponents X,
      Z ≠ closure {η} → η ∉ Z := by
    intro η hη Z hZ hne hmem
    exact hne ((hmax _ hη Z hZ
      (closure_minimal (Set.singleton_subset_iff.mpr hmem) (hcl Z hZ))).symm)
  -- the union of the components missing `x` is closed and misses `x`
  have hBclosed : IsClosed (⋃ Z ∈ {Z ∈ irreducibleComponents X | x ∉ Z}, Z) :=
    Set.Finite.isClosed_biUnion (hX.subset (Set.sep_subset _ _)) fun Z hZ => hcl Z hZ.1
  have hxB : x ∈ (⋃ Z ∈ {Z ∈ irreducibleComponents X | x ∉ Z}, Z)ᶜ := by
    intro hx
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_iUnion₂.mp hx
    exact hZ.2 hxZ
  -- an affine open `W ∋ x` avoiding all components not through `x`
  obtain ⟨W, hWaff, hxW, hWB⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨_, hBclosed.isOpen_compl⟩) hxB
  -- `W`, hence also its closure, only meets the components through `x`
  have hWsub : (W : Set X) ⊆ ⋃ Z ∈ {Z ∈ irreducibleComponents X | x ∈ Z}, Z := by
    intro w hw
    by_cases hxZ : x ∈ irreducibleComponent w
    · exact Set.mem_iUnion₂.mpr ⟨irreducibleComponent w,
        ⟨irreducibleComponent_mem_irreducibleComponents w, hxZ⟩, mem_irreducibleComponent⟩
    · exact absurd (Set.mem_iUnion₂.mpr ⟨irreducibleComponent w,
        ⟨irreducibleComponent_mem_irreducibleComponents w, hxZ⟩, mem_irreducibleComponent⟩)
        (hWB hw)
  have hclWsub : closure (W : Set X) ⊆ ⋃ Z ∈ {Z ∈ irreducibleComponents X | x ∈ Z}, Z :=
    closure_minimal hWsub
      (Set.Finite.isClosed_biUnion (hX.subset (Set.sep_subset _ _)) fun Z hZ => hcl Z hZ.1)
  -- generic points whose component passes through `x` already lie in `W`
  have hgenW : ∀ η ∈ genericPoints X, x ∈ closure {η} → η ∈ W := by
    intro η hη hxη
    obtain ⟨z, hzW, hz⟩ := mem_closure_iff.mp hxη W W.isOpen hxW
    exact hz ▸ hzW
  -- for each generic point whose component misses `x`, an affine open around it
  -- avoiding `closure W` and all other components
  have hfar : ∀ η : {η : X // η ∈ genericPoints X ∧ x ∉ closure {η}},
      ∃ V : X.Opens, IsAffineOpen V ∧ η.1 ∈ V ∧ (V : Set X) ⊆
        (closure (W : Set X) ∪ ⋃ Z ∈ irreducibleComponents X \ {closure {η.1}}, Z)ᶜ := by
    rintro ⟨η, hη, hxη⟩
    have hOclosed : IsClosed
        (closure (W : Set X) ∪ ⋃ Z ∈ irreducibleComponents X \ {closure {η}}, Z) :=
      isClosed_closure.union
        (Set.Finite.isClosed_biUnion (hX.subset Set.sdiff_subset) fun Z hZ => hcl Z hZ.1)
    have hηO : η ∈
        (closure (W : Set X) ∪ ⋃ Z ∈ irreducibleComponents X \ {closure {η}}, Z)ᶜ := by
      rintro (hmem | hmem)
      · -- `η` would lie on a component through `x`, forcing `x ∈ closure {η}`
        obtain ⟨Z, hZ, hηZ⟩ := Set.mem_iUnion₂.mp (hclWsub hmem)
        have hZη : closure ({η} : Set X) = Z := hmax _ hη Z hZ.1
          (closure_minimal (Set.singleton_subset_iff.mpr hηZ) (hcl Z hZ.1))
        exact hxη (by rw [hZη]; exact hZ.2)
      · obtain ⟨Z, hZ, hηZ⟩ := Set.mem_iUnion₂.mp hmem
        exact hgen_not_mem η hη Z hZ.1 hZ.2 hηZ
    obtain ⟨V, hVaff, hηV, hVsub⟩ :=
      exists_isAffineOpen_mem_and_subset (U := ⟨_, hOclosed.isOpen_compl⟩) hηO
    exact ⟨V, hVaff, hηV, hVsub⟩
  choose V hVaff hVmem hVsub using hfar
  -- each far affine open is contained in the component of its generic point
  have hVcomp : ∀ η, (V η : Set X) ⊆ closure {η.1} := by
    intro η v hv
    by_cases h : irreducibleComponent v = closure {η.1}
    · rw [← h]; exact mem_irreducibleComponent
    · exact absurd (Or.inr (Set.mem_iUnion₂.mpr ⟨irreducibleComponent v,
        ⟨irreducibleComponent_mem_irreducibleComponents v, h⟩, mem_irreducibleComponent⟩))
        (hVsub η hv)
  -- the finitely many chosen opens are pairwise disjoint
  have hGfin : Finite {η : X // η ∈ genericPoints X ∧ x ∉ closure {η}} :=
    Set.Finite.to_subtype ((genericPoints.finite hX).subset fun η hη => hη.1)
  have hdisjWV : ∀ η, Disjoint (W : Set X) (V η : Set X) := by
    intro η
    rw [Set.disjoint_left]
    intro v hvW hvV
    exact hVsub η hvV (Or.inl (subset_closure hvW))
  have hdisjVV : ∀ η η', η ≠ η' → Disjoint (V η : Set X) (V η' : Set X) := by
    intro η η' hne
    rw [Set.disjoint_left]
    intro v hvV hvV'
    have hcompne : closure ({η.1} : Set X) ≠ closure {η'.1} := fun h =>
      hne (Subtype.ext (inseparable_iff_closure_eq.mpr h).eq)
    exact hVsub η' hvV' (Or.inr (Set.mem_iUnion₂.mpr
      ⟨closure {η.1}, ⟨η.2.1, hcompne⟩, hVcomp η hvV⟩))
  have hFaff : ∀ i : Option {η : X // η ∈ genericPoints X ∧ x ∉ closure {η}},
      IsAffineOpen (i.elim W V) := by
    rintro (_ | η)
    · exact hWaff
    · exact hVaff η
  have hFdisj : Pairwise (Function.onFun Disjoint
      fun i : Option {η : X // η ∈ genericPoints X ∧ x ∉ closure {η}} => i.elim W V) := by
    have key : ∀ i j : Option {η : X // η ∈ genericPoints X ∧ x ∉ closure {η}},
        i ≠ j → Disjoint ((i.elim W V : X.Opens) : Set X) ((j.elim W V : X.Opens) : Set X) := by
      rintro (_ | η) (_ | η') hne
      · exact absurd rfl hne
      · exact hdisjWV η'
      · exact (hdisjWV η).symm
      · exact hdisjVV η η' fun h => hne (congrArg _ h)
    intro i j hne
    exact Opens.coe_disjoint.mp (key i j hne)
  refine ⟨⨆ i, (Option.elim · W V) i, IsAffineOpen.iSup_of_disjoint hFaff hFdisj, ?_, ?_⟩
  · exact Opens.mem_iSup.mpr ⟨none, hxW⟩
  · intro η hη
    by_cases hxη : x ∈ closure {η}
    · exact Opens.mem_iSup.mpr ⟨none, hgenW η hη hxη⟩
    · exact Opens.mem_iSup.mpr ⟨some ⟨η, hη, hxη⟩, hVmem ⟨η, hη, hxη⟩⟩

/-- **Dense affine covers exist**: a quasi-compact scheme with finitely many
irreducible components admits a finite affine open cover whose total intersection
contains every generic point, and is therefore dense.
(Stacks Project Tag 01ZX, simplified for the finite-components case; blueprint
`lemma:nagata-dense-affine-cover-exists`.) -/
theorem exists_isAffineOpen_iSup_eq_top_and_genericPoints_subset_iInter
    (X : Scheme.{u}) [CompactSpace X] (hX : (irreducibleComponents X).Finite) :
    ∃ (n : ℕ) (U : Fin n → X.Opens), (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ ∧
      genericPoints X ⊆ ⋂ i, (U i : Set X) ∧ Dense (⋂ i, (U i : Set X)) := by
  choose U hUaff hUmem hUgen using exists_isAffineOpen_mem_and_genericPoints_subset hX
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X))
    (fun x => (U x).isOpen) fun y _ => Set.mem_iUnion.mpr ⟨y, hUmem y⟩
  have hgen : genericPoints X ⊆ ⋂ i, (U (t.equivFin.symm i).1 : Set X) := fun η hη =>
    Set.mem_iInter.mpr fun i => hUgen _ hη
  refine ⟨t.card, fun i => U (t.equivFin.symm i).1, fun i => hUaff _, ?_, hgen, ?_⟩
  · rw [eq_top_iff]
    intro y hy
    obtain ⟨z, hzt, hyz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact Opens.mem_iSup.mpr ⟨t.equivFin ⟨z, hzt⟩, by simpa using hyz⟩
  · exact (dense_iff_closure_eq.mpr genericPoints.closure).mono hgen

open CategoryTheory Limits in
/-- The disjoint union `∐_ι Spec k ≅ Spec (ι → k)` is compatible with the structure maps to
`Spec k`: the fold map `∐_ι Spec k ⟶ Spec k` is `Spec` of the diagonal `k → (ι → k)`. -/
lemma sigmaSpec_comp_Spec_map_algebraMap (ι : Type u) (k : Type u) [CommRing k] :
    sigmaSpec (fun _ : ι ↦ CommRingCat.of k) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (ι → k))) =
      Sigma.desc fun _ : ι ↦ 𝟙 (Spec (.of k)) := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [Sigma.ι_comp_desc, ι_sigmaSpec_assoc, ← Spec.map_comp, ← Spec.map_id]
  rfl

/-- A scheme whose ring of global sections is the zero ring is empty: at a point `p` the germ map
`Γ(X, ⊤) → 𝒪_{X,p}` would send `0 = 1` to `0 = 1` in the nonzero local ring `𝒪_{X,p}`. This is
the converse of the instance `Subsingleton Γ(X, U)` for empty `X`. -/
lemma Scheme.isEmpty_of_subsingleton_Γ (h : Subsingleton Γ(X, ⊤)) : IsEmpty X :=
  ⟨fun p ↦ by
    have := congrArg (X.presheaf.germ ⊤ p trivial).hom (Subsingleton.elim (0 : Γ(X, ⊤)) 1)
    rw [map_zero, map_one] at this
    exact zero_ne_one this⟩

open CategoryTheory Limits in
/-- A morphism from a scheme with exactly one point into a coproduct of schemes factors through
one of the summands. -/
lemma exists_comp_sigmaι_eq_of_subsingleton {σ : Type*} [Small.{u} σ] {g : σ → Scheme.{u}}
    [Subsingleton X] [Nonempty X] (f : X ⟶ ∐ g) :
    ∃ (i : σ) (f' : X ⟶ g i), f' ≫ Sigma.ι g i = f := by
  obtain ⟨z⟩ := ‹Nonempty X›
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover g).exists_eq (f z)
  have hy' : Sigma.ι g i y = f z := hy
  refine ⟨i, IsOpenImmersion.lift (Sigma.ι g i) f ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨w, rfl⟩
  exact ⟨y, by rw [hy', Subsingleton.elim w z]⟩

open CategoryTheory Limits in
/-- The ring of global functions on the terminal scheme `Spec ℤ` is a quotient of `ℤ`. -/
lemma surjective_intCastRingHom_Γ_terminal :
    Function.Surjective (Int.castRingHom Γ(⊤_ Scheme.{u}, ⊤)) := by
  let e : Γ(⊤_ Scheme.{u}, ⊤) ≅ CommRingCat.of (ULift.{u} ℤ) :=
    Scheme.Γ.mapIso (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).op ≪≫
      Scheme.ΓSpecIso _
  intro y
  refine ⟨(e.hom y).down, e.commRingCatIsoToRingEquiv.injective ?_⟩
  change e.hom _ = e.hom y
  rw [eq_intCast, map_intCast]
  rfl

end AlgebraicGeometry
