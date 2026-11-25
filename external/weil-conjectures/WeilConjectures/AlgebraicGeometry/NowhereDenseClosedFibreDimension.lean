/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # NowhereDenseClosedFibreDimension

Source: Stacks Project, Tag 054X, final dimension contradiction; Tags 00OT and 00OS.
(blueprint: lem-sbc-nowhere-dense-closed-fibre-dimension)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

private theorem exists_generalization_outside_closed {B : Type*}
    [TopologicalSpace B] [TopologicalSpace.NoetherianSpace B] [QuasiSober B]
    {W : Set B} (hW : IsClosed W) (hinterior : interior W = ∅) (w : B) :
    ∃ b : B, b ⤳ w ∧ b ∉ W := by
  let C := irreducibleComponent w
  have hC : C ∈ irreducibleComponents B := irreducibleComponent_mem_irreducibleComponents w
  have hgen := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
  refine ⟨hC.1.genericPoint, hgen.specializes mem_irreducibleComponent, fun hb ↦ ?_⟩
  have hCW : C ⊆ W := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hb) hW
  obtain ⟨O, hO, ⟨b, hbO⟩, hOC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  have : b ∈ interior W := interior_mono (hOC.trans hCW) (by rwa [hO.interior_eq])
  simp [hinterior] at this

private theorem closed_nowhere_dense_dimension_lt {B : Type*}
    [TopologicalSpace B] [TopologicalSpace.NoetherianSpace B] [QuasiSober B] [T0Space B]
    {W : Set B} (hW : IsClosed W) (hinterior : interior W = ∅) {n : ℕ}
    (hdim : topologicalKrullDim B < (n : WithBot ℕ∞) + 1) :
    topologicalKrullDim W < n := by
  apply topologicalKrullDim_lt_of_forall_exists_specializes
    (Z := Set.univ) isClosed_univ hW (Set.subset_univ W)
  · intro w _
    obtain ⟨b, hbw, hbW⟩ := exists_generalization_outside_closed hW hinterior w
    exact ⟨b, Set.mem_univ b, hbw, hbW⟩
  · exact (topologicalKrullDim_subspace_le B Set.univ).trans_lt hdim

private theorem local_dimension_lt_of_closed_embedding {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace.NoetherianSpace B]
    [QuasiSober B] [T0Space B] (j : A → B) (hj : IsClosedEmbedding j)
    (hinterior : interior (Set.range j) = ∅)
    (hfinite : topologicalKrullDim B ≠ ⊤) (a : A) :
    topologicalKrullDimAt a < topologicalKrullDimAt (j a) := by
  have hnonneg : 0 ≤ topologicalKrullDimAt (j a) := by
    refine le_iInf₂ fun U haU ↦ ?_
    have : Nonempty (TopologicalSpace.IrreducibleCloseds U) :=
      ⟨⟨closure {⟨j a, haU⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_nonneg
  have hlt : topologicalKrullDimAt (j a) < ⊤ := by
    exact ((iInf₂_le (⊤ : TopologicalSpace.Opens B) (by trivial)).trans
      (topologicalKrullDim_subspace_le B Set.univ)).trans_lt hfinite.lt_top
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot (by simp) hnonneg)
  have hdtop : d ≠ ⊤ := by
    intro hdtop
    simp [← hd, hdtop] at hlt
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hdtop
  have hsucc : topologicalKrullDimAt (j a) < (n : WithBot ℕ∞) + 1 := by
    rw [← hd]
    exact_mod_cast Nat.lt_succ_self n
  obtain ⟨U, hU⟩ := iInf_lt_iff.mp hsucc
  obtain ⟨haU, hdimU⟩ := iInf_lt_iff.mp hU
  let V : TopologicalSpace.Opens A := ⟨j ⁻¹' U, U.isOpen.preimage hj.continuous⟩
  let jU : V → U := fun x ↦ ⟨j x, x.2⟩
  have hjU : IsEmbedding jU := by
    apply IsEmbedding.of_comp (g := Subtype.val) (by fun_prop) continuous_subtype_val
    exact hj.isEmbedding.comp IsEmbedding.subtypeVal
  have hrange : Set.range jU = (Subtype.val : U → B) ⁻¹' Set.range j := by
    ext b
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      refine ⟨⟨x, ?_⟩, ?_⟩
      · change j x ∈ U
        rw [hx]
        exact b.2
      · exact Subtype.ext hx
  have hclosed : IsClosed (Set.range jU) := by
    rw [hrange]
    exact hj.isClosed_range.preimage continuous_subtype_val
  have hempty : interior (Set.range jU) = ∅ := by
    rw [hrange, ← U.isOpenEmbedding'.isOpenMap.preimage_interior_eq_interior_preimage
      U.isOpenEmbedding'.continuous (Set.range j), hinterior]
    exact Set.preimage_empty
  have : TopologicalSpace.NoetherianSpace U := U.isOpenEmbedding'.isInducing.noetherianSpace
  have : QuasiSober U := U.isOpenEmbedding'.quasiSober
  have hdrop := closed_nowhere_dense_dimension_lt hclosed hempty hdimU
  have hlocal : topologicalKrullDimAt a ≤ topologicalKrullDim V := iInf₂_le V haU
  rw [hjU.topologicalKrullDim_eq_range] at hlocal
  exact hlocal.trans_lt (hdrop.trans_eq hd)

/-- A nowhere dense closed fibre has strictly smaller local dimension at each point.
Source: Stacks Project, Tag 054X, final dimension contradiction; Tags 00OT and 00OS.
Proof: the fibre of a quasi-compact locally finite type morphism is a noetherian,
finite-dimensional scheme over the residue field. In any noetherian sober space,
each point specializes from the generic point of an irreducible component. Such a
generic point cannot lie in a nowhere dense closed subset: otherwise that subset
contains its component and hence a nonempty ambient open. Thus every chain in the
closed subset extends by a point outside it. The local dimension at the image point
is a natural number n. The infimum defining it supplies an open neighbourhood of
dimension less than n + 1. Restrict the closed embedding to this neighbourhood;
its range is still nowhere dense, so the chain-extension inequality bounds its
dimension strictly by n. The source's local dimension is at most the dimension of
this restricted source. Apply this topological argument to the base change of i
on the fibre and identify its distinguished point with f.asFiber (i z).
(blueprint: lem-sbc-nowhere-dense-closed-fibre-dimension) -/
theorem fibre_dimension_lt_of_closed_interior_eq_empty
    {Z X T : Scheme.{u}} (f : X ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] (t : T)
    (h : interior ((f.fiberι t) ⁻¹' Set.range i) = ∅)
    (z : Z) (hz : (i ≫ f) z = t) :
    topologicalKrullDimAt ((i ≫ f).asFiber z) <
      topologicalKrullDimAt (f.asFiber (i z)) := by
  classical
  let g := i ≫ f
  let s := f (i z)
  have hs : s = t := by simpa [s, Scheme.Hom.comp_apply] using hz
  let j : g.fiber s ⟶ f.fiber s := CategoryTheory.Limits.pullback.map
    g (T.fromSpecResidueField s) f (T.fromSpecResidueField s)
    i (𝟙 _) (𝟙 _) (by simp [g]) (by simp)
  have hsq : IsPullback j (g.fiberι s) (f.fiberι s) i := by
    refine IsPullback.of_right ?_ ?_
      (IsPullback.of_hasPullback f (T.fromSpecResidueField s)).flip
    · simpa [j, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiberι, g] using
        (IsPullback.of_hasPullback g (T.fromSpecResidueField s)).flip
    · simp [j, Scheme.Hom.fiberι]
  have : IsClosedImmersion j := MorphismProperty.of_isPullback hsq.flip inferInstance
  have hrange : Set.range j = (f.fiberι s) ⁻¹' Set.range i := by
    dsimp only [j, Scheme.Hom.fiber]
    rw [Scheme.Pullback.range_map]
    simp [Scheme.Hom.fiberι]
  have hpoint : j (g.asFiber z) = f.asFiber (i z) := by
    apply (f.fiberι s).isEmbedding.injective
    change (j ≫ f.fiberι s) (g.asFiber z) = _
    rw [hsq.w, Scheme.Hom.comp_apply]
    change i ((g.fiberι (g z)) (g.asFiber z)) =
      (f.fiberι (f (i z))) (f.asFiber (i z))
    simp
  have hnowhere : interior (Set.range j) = ∅ := by
    rw [hrange, hs]
    exact h
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  have : IsNoetherian (f.fiber s) := ⟨⟩
  have hfinite := topologicalKrullDim_ne_top_of_compactSpace (f.fiberToSpecResidueField s)
  have hdrop := local_dimension_lt_of_closed_embedding j j.isClosedEmbedding
    hnowhere hfinite (g.asFiber z)
  rwa [hpoint] at hdrop

end AlgebraicGeometry
