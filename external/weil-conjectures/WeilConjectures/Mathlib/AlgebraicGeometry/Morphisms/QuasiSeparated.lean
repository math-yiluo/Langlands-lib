/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The qcqs lemma for the sections of the restricted scheme

`AlgebraicGeometry.Γ_restrict_isLocalization_of_qcqs`: for a quasi-compact quasi-separated
scheme `X` and a global section `f`, the global sections of the open subscheme `X.basicOpen f`
are the localization of `Γ(X, ⊤)` away from `f`. This is the analogue of
`AlgebraicGeometry.Γ_restrict_isLocalization` with the affineness hypothesis relaxed to
quasi-compact quasi-separated, deduced from the qcqs lemma
`AlgebraicGeometry.isLocalization_basicOpen_of_qcqs`.

We also record `AlgebraicGeometry.Scheme.Opens.quasiCompact_ι`: the inclusion of a
quasi-compact open of a quasi-separated scheme is a quasi-compact morphism, and
`AlgebraicGeometry.quasiSeparatedSpace_of_surjective`: quasi-separatedness of a scheme descends
along a surjective quasi-compact morphism.
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Variant of `isLocalization_basicOpen_of_qcqs` for any open `V` equal to `X.basicOpen f`,
analogous to `IsAffineOpen.isLocalization_of_eq_basicOpen`. -/
theorem isLocalization_of_eq_basicOpen_of_qcqs {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (f : Γ(X, ⊤)) {V : X.Opens} (i : V ⟶ (⊤ : X.Opens))
    (e : V = X.basicOpen f) :
    @IsLocalization.Away _ _ f Γ(X, V) _ (X.presheaf.map i.op).hom.toAlgebra := by
  subst e
  exact isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ f

/-- The **qcqs lemma** for the global sections of an open subscheme: if `X` is quasi-compact
and quasi-separated and `f : Γ(X, ⊤)`, then `Γ(X.basicOpen f, ⊤)` is the localization of
`Γ(X, ⊤)` away from `f`. See `AlgebraicGeometry.Γ_restrict_isLocalization` for the affine
case. -/
theorem Γ_restrict_isLocalization_of_qcqs (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (f : Γ(X, ⊤)) :
    IsLocalization.Away f Γ(X.basicOpen f, ⊤) :=
  isLocalization_of_eq_basicOpen_of_qcqs f _ (Opens.isOpenEmbedding_obj_top _)

/-- The inclusion of a quasi-compact open of a quasi-separated scheme is a quasi-compact
morphism. -/
lemma Scheme.Opens.quasiCompact_ι {X : Scheme.{u}} [QuasiSeparatedSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) : QuasiCompact U.ι :=
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  inferInstance

/-- Quasi-separatedness of schemes descends along surjective quasi-compact morphisms: the
intersection of two quasi-compact opens of `Y` is the image of the intersection of their
quasi-compact preimages. -/
lemma quasiSeparatedSpace_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [QuasiCompact f] [QuasiSeparatedSpace X] : QuasiSeparatedSpace Y := by
  refine ⟨fun U V hU hUc hV hVc ↦ ?_⟩
  have h := QuasiSeparatedSpace.inter_isCompact _ _ (hU.preimage f.continuous)
    (QuasiCompact.isCompact_preimage (f := f) U hU hUc) (hV.preimage f.continuous)
    (QuasiCompact.isCompact_preimage (f := f) V hV hVc)
  rw [← Set.preimage_inter] at h
  simpa [Set.image_preimage_eq _ f.surjective] using h.image f.continuous

/-- **Intersections of quasi-compact opens**: in a quasi-separated scheme the intersection of two
quasi-compact open subschemes is quasi-compact. (blueprint: `pqf-lem-qs-intersection-qc`) -/
lemma Scheme.isCompact_inf_of_quasiSeparatedSpace {X : Scheme.{u}} [QuasiSeparatedSpace X]
    {U V : X.Opens} (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X)) :
    IsCompact ((U ⊓ V : X.Opens) : Set X) :=
  QuasiSeparatedSpace.inter_isCompact _ _ U.2 hU V.2 hV


end AlgebraicGeometry
