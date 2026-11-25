/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # The boundary of a dense open after field extension

Source: Stacks Project, Tag 0GJA, proof and remark (c).
(blueprint: lemma-removing-finitely-many-points--1)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry.IsCurve

private theorem dense_open_boundary
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] (U : X.Opens) (hU : Dense (U : Set X)) :
    (U : Set X)ᶜ.Finite ∧ ∀ x ∉ U, IsClosed ({x} : Set X) := by
  classical
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have hdim := IsCurve.krullDim_le_one (f := f)
  let I := ↥(irreducibleComponents X)
  have : Finite I := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hirr (Z : I) : IsIrreducible Z.1 := Z.2.1
  have hcl (Z : I) : IsClosed Z.1 := isClosed_of_mem_irreducibleComponents _ Z.2
  have hmem (x : X) : ∃ Z : I, x ∈ Z.1 := by
    obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
      isIrreducible_singleton
    exact ⟨⟨Z, hZ⟩, hxZ rfl⟩
  choose ξ hξ using fun Z : I ↦ QuasiSober.sober (hirr Z) (hcl Z)
  let O (Z : I) : X.Opens := ⟨⋂ Z' ∈ ({Z}ᶜ : Set I), Z'.1ᶜ,
    (Set.toFinite _).isOpen_biInter fun Z' _ ↦ (hcl Z').isOpen_compl⟩
  have hO (Z Z' : I) (x : X) (hx : x ∈ O Z) (hx' : x ∈ Z'.1) : Z' = Z := by
    by_contra h
    exact (Set.mem_iInter₂.1 hx Z' h) hx'
  have hξO (Z : I) : ξ Z ∈ O Z := by
    refine Set.mem_iInter₂.2 fun Z' hZ' hξZ' ↦ hZ' ?_
    have hsub : Z.1 ⊆ Z'.1 := by
      rw [← (hξ Z).def]
      exact closure_minimal (Set.singleton_subset_iff.2 hξZ') (hcl Z')
    exact (Subtype.ext (Z.2.eq_of_le (hirr Z') hsub)).symm
  have hUne (Z : I) : (Subtype.val ⁻¹' (U : Set X) : Set Z.1).Nonempty := by
    obtain ⟨x, hxO, hxU⟩ := hU.inter_open_nonempty (O Z) (O Z).isOpen ⟨ξ Z, hξO Z⟩
    obtain ⟨Z', hxZ'⟩ := hmem x
    exact ⟨⟨x, (hO Z Z' x hxO hxZ') ▸ hxZ'⟩, hxU⟩
  let T (Z : I) : Set X := Subtype.val ''
    (Subtype.val ⁻¹' (U : Set X) : Set Z.1)ᶜ
  have hTfin (Z : I) : (T Z).Finite := by
    have : IrreducibleSpace Z.1 := Subtype.irreducibleSpace (hirr Z)
    have : QuasiSober Z.1 := (hcl Z).isClosedEmbedding_subtypeVal.quasiSober
    exact ((U.isOpen.preimage continuous_subtype_val).finite_compl_of_topologicalKrullDim_le_one
      (IsInducing.subtypeVal.topologicalKrullDim_le.trans hdim) (hUne Z)).image _
  have hTcl (Z : I) (x : X) (hx : x ∈ T Z) : IsClosed ({x} : Set X) := by
    have : IrreducibleSpace Z.1 := Subtype.irreducibleSpace (hirr Z)
    obtain ⟨z, hz, rfl⟩ := hx
    rw [← Set.image_singleton]
    exact (hcl Z).isClosedEmbedding_subtypeVal.isClosedMap _
      ((U.isOpen.preimage continuous_subtype_val).isClosed_singleton_of_mem_compl
        (IsInducing.subtypeVal.topologicalKrullDim_le.trans hdim) (hUne Z) hz)
  have hsub : (U : Set X)ᶜ ⊆ ⋃ Z, T Z := by
    intro x hx
    obtain ⟨Z, hxZ⟩ := hmem x
    exact Set.mem_iUnion.2 ⟨Z, ⟨⟨x, hxZ⟩, hx, rfl⟩⟩
  refine ⟨(Set.finite_iUnion hTfin).subset hsub, fun x hx ↦ ?_⟩
  obtain ⟨Z, hxZ⟩ := Set.mem_iUnion.1 (hsub hx)
  exact hTcl Z x hxZ

/-- The inverse image of a dense open in a curve over an algebraically closed field has
finite complement consisting of closed points with separably closed residue fields.
Source: Stacks Project, Tag 0GJA, proof, first sentence and remark (c).
(blueprint: lemma-removing-finitely-many-points--1)

Proof: The curve is Noetherian and has finitely many irreducible components. For each
component Z, take the open O avoiding all the other components. Its generic point belongs
to O, so density gives a point of U intersect O, necessarily in Z. Thus U restricts to a
nonempty open of each irreducible component. In a Noetherian irreducible sober space of
dimension at most one, the complement of a nonempty open is finite and its points are
closed. Apply this to each Z and take the finite union of the images of the complements.
Closedness of Z transports closed singletons to X. This proves finiteness and closedness
of the boundary in X, without irreducibility or reducedness assumptions on X.

For a boundary point x, its residue field is k by the Nullstellensatz, so the composite
Spec κ(x) to X to Spec k is an isomorphism. Paste the square defining the fiber of ι' at x
with the given field-extension square. The resulting square is cartesian, and pulling
back the isomorphism just obtained shows that this fiber maps isomorphically to Spec k'.
Consequently its underlying space, and the topological fiber of ι', are subsingletons.
Therefore ι' is injective on the inverse image of the finite boundary; this inverse image
is finite. The inverse image of each closed singleton in the boundary is a singleton
whenever nonempty and is closed by continuity. Finally f' is locally of finite type by
base change, so the residue field of each closed boundary point in X' is k', hence
separably closed. Empty curves, empty boundaries, zero-dimensional curves and nonreduced
curves require no extra assumptions or separate choices. -/
theorem dense_open_baseChange_boundary
    {k k' : Type u} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of k')}
    {ι' : X' ⟶ X} (h : IsPullback ι' f' f ι)
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let V := ι' ⁻¹ᵁ U
    (V : Set X')ᶜ.Finite ∧
      (∀ x ∉ V, IsClosed ({x} : Set X')) ∧
      (∀ x ∉ V, IsSepClosed (X'.residueField x))  := by
  classical
  dsimp only
  obtain ⟨hfin, hcl⟩ := dense_open_boundary f U hU
  have hfiber (x : X) (hx : x ∉ U) : (ι' ⁻¹' {x}).Subsingleton := by
    have hi : IsIso (X.fromSpecResidueField x ≫ f) := by
      rw [← SpecMap_residueFieldIsoBase_inv f x (hcl x hx)]
      infer_instance
    have hp := (IsPullback.of_hasPullback ι' (X.fromSpecResidueField x)).flip.paste_vert h
    have : IsIso ((ι'.fiberι x) ≫ f') := hp.isIso_snd_of_isIso
    have : Subsingleton (ι'.fiber x) :=
      ((asIso ((ι'.fiberι x) ≫ f')).hom.homeomorph).injective.subsingleton
    exact (ι' ⁻¹' {x}).subsingleton_coe.mp (Equiv.subsingleton (ι'.fiberHomeo x).symm.toEquiv)
  have hinj : Set.InjOn ι' (ι' ⁻¹' (U : Set X)ᶜ) := by
    intro x hx y _hy hxy
    exact hfiber (ι' x) hx (by simp) (by simpa using hxy.symm)
  have hcl' (x : X') (hx : x ∉ ι' ⁻¹ᵁ U) : IsClosed ({x} : Set X') := by
    have heq : ι' ⁻¹' {ι' x} = {x} := by
      ext y
      constructor
      · intro hy
        exact hfiber (ι' x) hx hy (by simp)
      · rintro rfl
        simp
    rw [← heq]
    exact (hcl (ι' x) hx).preimage ι'.continuous
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback h inferInstance
  refine ⟨?_, hcl', fun x hx ↦ ?_⟩
  · exact hfin.preimage hinj
  · have : IsAlgClosed (X'.residueField x) := IsAlgClosed.of_ringEquiv k' _
      (residueFieldIsoBase f' x (hcl' x hx)).symm.commRingCatIsoToRingEquiv
    infer_instance

end AlgebraicGeometry.IsCurve
