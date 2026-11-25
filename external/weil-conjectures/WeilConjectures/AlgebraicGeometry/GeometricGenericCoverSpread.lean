/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.GeometricGenericCoverModel
import WeilConjectures.AlgebraicGeometry.GenericClosedSubsetFibreNonempty
import WeilConjectures.AlgebraicGeometry.CommonFieldFibreComparison

/-!
# Spreading a supplied geometric generic cover

Source: Stacks Project, Tag 055G, proof after splitting generic components.
(blueprint: lem-sbc-geometric-generic-cover-spread)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

/-- A supplied finite geometric closed cover spreads while retaining its generic edges.

Source: Stacks Project, Tag 055G, closures and intersection-image argument;
Tags 0551, 054Y, 0559, 052A, 01UA and 054W.
Proof: realize the supplied finite separable extension by a finite etale surjective
map from an irreducible affine scheme to an affine generic neighbourhood (the
polynomial construction in Tag 0551). Reduce the model. In the pulled back total
space take the reduced closures of the supplied closed subsets. Their generic
fibres are the supplied subsets. By Tag 054Y, shrink so they cover the total space.
Their generic fibres are geometrically irreducible by the field-base-change
hypothesis, so Tag 0559 shrinks the base so all their fibres are geometrically
irreducible. For each pair with nonempty generic intersection, give the intersection
of these closures its reduced closed subscheme structure. Generic flatness, Tag
052A, makes its map flat and finitely presented after shrinking. Its image is open
by Tag 01UA and contains the generic point. Intersect these finitely many images
with the previous opens. Transfer this open through the reduction homeomorphism;
its image W under the finite etale map is open and contains the original generic
point. Given s in W and a field-valued point over s, choose a model point over s in
the open. A residue field of the tensor product of the model point's residue field
with the test field over kappa(s) is a common extension E in universe u. Take Z to
be the E-fibre and p its projection to the test fibre. Field extension is faithfully
flat, so p is surjective. The fibres of the closures give the irreducible nonempty
sets B covering Z, and all prescribed intersections remain nonempty after field
extension. If the index type is empty, the generic cover forces the generic fibre
to be empty; Tag 054W supplies an open of empty fibres. Take Z to be the test fibre,
p its identity, and B the empty family. No connectedness is used.

(blueprint: lem-sbc-geometric-generic-cover-spread) -/
theorem exists_open_spreading_geometric_generic_cover {X S : Scheme.{u}}
    [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    {L : Type u} [Field L]
    (yη : Spec (CommRingCat.of L) ⟶
      Spec (CommRingCat.of (S.residueField (genericPoint S))))
    [IsFinite yη] [Etale yη] {I : Type u} [Finite I]
    (A : I → Set ↥(pullback (f.fiberToSpecResidueField (genericPoint S)) yη))
    (hclosed : ∀ i, IsClosed (A i)) (hcover : (⋃ i, A i) = Set.univ)
    (hgeom : ∀ i, ∀ (E : Type u) (_ : Field E)
      (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L)),
      IsIrreducible ((pullback.fst
        (pullback.snd (f.fiberToSpecResidueField (genericPoint S)) yη) z) ⁻¹' A i)) :
    ∃ (W : Set S), IsOpen W ∧ genericPoint S ∈ W ∧
      ∀ s ∈ W, ∀ (K : Type u) (_ : Field K)
        (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (S.residueField s))),
        ∃ (Z : Scheme.{u}) (p : Z ⟶ pullback (f.fiberToSpecResidueField s) y)
          (B : I → Set Z), Surjective p ∧
          (∀ i, IsIrreducible (B i)) ∧ (⋃ i, B i) = Set.univ ∧
          ∀ i j, (A i ∩ A j).Nonempty → (B i ∩ B j).Nonempty  := by
  classical
  obtain ⟨T, g, η, C, hg, hη, hgη, hCclosed, hCcover, hCgeom, hCedges⟩ :=
    exists_geometric_generic_cover_model f yη A hclosed hcover hgeom
  have : Etale g := hg
  let h := pullback.snd f g
  have hneighbourhood (ij : I × I) :
      ∃ V : Set T, IsOpen V ∧ η ∈ V ∧
        ∀ t ∈ V, (A ij.1 ∩ A ij.2).Nonempty →
          (C ij.1 ∩ C ij.2 ∩ h ⁻¹' {t}).Nonempty := by
    by_cases hedge : (A ij.1 ∩ A ij.2).Nonempty
    · obtain ⟨V, hV, hηV, hnonempty⟩ :=
        exists_open_closed_subset_fibre_nonempty h η hη (C ij.1 ∩ C ij.2)
          ((hCclosed ij.1).inter (hCclosed ij.2)) (hCedges ij.1 ij.2 hedge)
      exact ⟨V, hV, hηV, fun t ht _ ↦ hnonempty t ht⟩
    · exact ⟨Set.univ, isOpen_univ, Set.mem_univ η,
        fun _ _ he ↦ (hedge he).elim⟩
  choose V hV hηV hnonempty using hneighbourhood
  let U : Set T := ⋂ ij, V ij
  have hU : IsOpen U := isOpen_iInter_of_finite hV
  have hηU : η ∈ U := Set.mem_iInter.mpr hηV
  refine ⟨g '' U, g.isOpenMap U hU, ⟨η, hηU, hgη⟩, ?_⟩
  intro s hs K hK y
  obtain ⟨t, htU, hts⟩ := hs
  obtain ⟨E, hE, z, k, heq, -, hp⟩ := exists_common_field_fibre_comparison f g t s hts K y
  let p := (commonFieldFibreIso f g t s z k y heq).hom ≫
    pullback.fst (pullback.snd (f.fiberToSpecResidueField s) y) k
  let q := pullback.fst (h.fiberToSpecResidueField t) z ≫ h.fiberι t
  let B : I → Set ↥(pullback (h.fiberToSpecResidueField t) z) := fun i ↦ q ⁻¹' C i
  refine ⟨pullback (h.fiberToSpecResidueField t) z, p, B, hp,
    fun i ↦ hCgeom i t E hE z, ?_, ?_⟩
  · change (⋃ i, q ⁻¹' C i) = Set.univ
    rw [← Set.preimage_iUnion, hCcover, Set.preimage_univ]
  · intro i j hedge
    obtain ⟨x, hxC, hxt⟩ := hnonempty (i, j) t (Set.mem_iInter.mp htU (i, j)) hedge
    have hxrange : x ∈ Set.range (h.fiberι t) := by
      rw [h.range_fiberι t]
      exact hxt
    obtain ⟨v, hv⟩ := hxrange
    have : Surjective z :=
      ⟨fun w ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
    obtain ⟨w, hw⟩ := (pullback.fst (h.fiberToSpecResidueField t) z).surjective v
    refine ⟨w, ?_⟩
    change q w ∈ C i ∧ q w ∈ C j
    simpa only [q, Scheme.Hom.comp_apply, hw, hv, Set.mem_inter_iff] using hxC

end AlgebraicGeometry
