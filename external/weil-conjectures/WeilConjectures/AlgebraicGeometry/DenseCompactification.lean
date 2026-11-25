/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Dense compactifications of the same dimension

Blueprint `theorem-verdier-biduality--1` (reduction to the proper case): a separated
scheme `X` of finite type over a field `k` admits a proper compactification `j : X ↪ X̄` with
dense image, obtained by replacing a Nagata compactification by the scheme-theoretic closure of
`X`; then `dim X̄ = dim X`.

## Main results

- `AlgebraicGeometry.mem_of_dense_of_forall_specializes_eq`: in a noetherian sober space, the
  generic points of the irreducible components lie in every dense open subset.
- `AlgebraicGeometry.topologicalKrullDim_le_of_dense`: a dense open subscheme of a quasi-compact
  scheme locally of finite type over a field has the same dimension as the scheme.
- `AlgebraicGeometry.exists_dense_compactification`: a separated scheme of finite type over a
  field has a proper compactification with dense image and of the same dimension.
-/

@[expose] public section

universe u

open CategoryTheory Topology TopologicalSpace Order

namespace AlgebraicGeometry

/-- In a noetherian quasi-sober `T₀` space, a maximal point `η` (one without proper
generalization, i.e. the generic point of an irreducible component) lies in every dense open
subset `U`: the complement of the closures of the other finitely many maximal points is an open
neighbourhood of `η`, which meets `U` in a point specializing from `η` only.

Blueprint `theorem-verdier-biduality--1` (reduction to the proper case). -/
theorem mem_of_dense_of_forall_specializes_eq {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] [T0Space X] {U : Set X} (hU : IsOpen U)
    (hd : Dense U) {η : X} (hη : ∀ y, y ⤳ η → y = η) : η ∈ U := by
  set M := {ξ | ξ ∈ (Set.univ : Set X) ∧ ∀ z ∈ Set.univ, z ⤳ ξ → z = ξ}
  have hM : M.Finite := isClosed_univ.finite_setOf_maximal_specializes
  set W := (⋃ ξ ∈ M \ {η}, closure ({ξ} : Set X))ᶜ
  have hW : IsOpen W :=
    ((hM.sdiff).isClosed_biUnion fun _ _ ↦ isClosed_closure).isOpen_compl
  have hηW : η ∈ W := by
    simp only [W, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro ξ hξ hηξ
    rw [← specializes_iff_mem_closure] at hηξ
    exact hξ.2 (hη ξ hηξ)
  obtain ⟨y, hyW, hyU⟩ := hd.inter_open_nonempty W hW ⟨η, hηW⟩
  obtain ⟨ξ, -, hξ, hξy⟩ := isClosed_univ.exists_maximal_specializes (Set.mem_univ y)
  obtain rfl : ξ = η := by
    by_contra h
    exact hyW (Set.mem_biUnion (x := ξ) ⟨⟨trivial, hξ⟩, h⟩
      (specializes_iff_mem_closure.mp hξy))
  exact hξy.mem_open hU hyU

/-- Blueprint `theorem-verdier-biduality--1` (reduction to the proper case): a dense open
subscheme `U` of a quasi-compact scheme `Y` locally of finite type over a field `k` has at least
the dimension of `Y`. Every point of `Y` specializes from the generic point `η` of an irreducible
component, which lies in `U`; the closure of `η` with its reduced structure is integral, so its
dimension is that of its nonempty open subscheme meeting `U`. -/
theorem topologicalKrullDim_le_of_dense {k : Type u} [Field k] {Y : Scheme.{u}}
    (a : Y ⟶ Spec (.of k)) [LocallyOfFiniteType a] [QuasiCompact a] (U : Y.Opens)
    (hU : Dense (U : Set Y)) : topologicalKrullDim Y ≤ topologicalKrullDim U := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian a
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian Y := ⟨⟩
  let := specializationOrder Y
  rw [topologicalKrullDim_eq_krullDim_specializationOrder, krullDim_eq_iSup_height]
  refine iSup_le fun x ↦ ?_
  obtain ⟨η, -, hη, hηx⟩ := isClosed_univ.exists_maximal_specializes (Set.mem_univ x)
  have hηU : η ∈ U :=
    mem_of_dense_of_forall_specializes_eq U.isOpen hU fun y hy ↦ hη y trivial hy
  refine (WithBot.coe_le_coe.mpr (height_mono (show x ≤ η from hηx))).trans ?_
  rw [← topologicalKrullDim_closure_singleton]
  let C : Closeds Y := ⟨closure {η}, isClosed_closure⟩
  let ι := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have hrange : Set.range ι.base = closure {η} := by
    simp [ι, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, C]
  have hemb := ι.isClosedEmbedding.isEmbedding
  have : IrreducibleSpace (Set.range ι.base) :=
    Subtype.irreducibleSpace (hrange ▸ isIrreducible_singleton.closure)
  have : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    hemb.toHomeomorph.symm.surjective.irreducibleSpace hemb.toHomeomorph.symm.continuous
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨z, hz⟩ : η ∈ Set.range ι.base := hrange ▸ subset_closure rfl
  have : Nonempty (ι ⁻¹ᵁ U) := ⟨⟨z, show ι.base z ∈ U from hz ▸ hηU⟩⟩
  rw [← hrange, ← hemb.topologicalKrullDim_eq_range,
    ← topologicalKrullDim_opens_eq (ι ≫ a) (ι ⁻¹ᵁ U)]
  exact (hemb.restrictPreimage (U : Set Y)).isInducing.topologicalKrullDim_le

/-- Blueprint `theorem-verdier-biduality--1` (reduction to the proper case): a separated
scheme `X` of finite type over a field `k` admits a proper compactification `j : X ⟶ X̄` over
`k` with dense image and `dim X̄ = dim X`. Take a Nagata compactification `X ⟶ Z ⟶ Spec k` and
replace `Z` by the scheme-theoretic closure `X̄` of `X`: it is a closed subscheme of `Z`, hence
proper over `k`, the open immersion factors through it with dense image, and the dimension of
`X̄` is that of its dense open subscheme `X`
(`AlgebraicGeometry.topologicalKrullDim_le_of_dense`). -/
theorem exists_dense_compactification {k : Type u} [Field k] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] :
    ∃ (X' : Scheme.{u}) (aX' : X' ⟶ Spec (.of k)) (j : X ⟶ X'), IsProper aX' ∧
      IsOpenImmersion j ∧ j ≫ aX' = aX ∧ Dense (Set.range j.base) ∧
      topologicalKrullDim X' = topologicalKrullDim X := by
  let c := HasCompactification.compactification aX
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have hcomm : c.i.toImage ≫ c.i.imageι ≫ c.g = aX := by
    rw [c.i.toImage_imageι_assoc]
    exact c.comm.symm
  have hdense : Dense (Set.range c.i.toImage.base) := by
    have hι := c.i.imageι.isClosedEmbedding
    refine dense_iff_closure_eq.mpr (hι.injective.image_injective ?_)
    rw [Set.image_univ, ← hι.closure_image_eq, ← Set.range_comp, ← TopCat.coe_comp,
      ← Scheme.Hom.comp_base, c.i.toImage_imageι, c.i.range_imageι]
  refine ⟨_, c.i.imageι ≫ c.g, c.i.toImage, inferInstance, inferInstance, hcomm, hdense,
    le_antisymm ?_ ?_⟩
  · refine (topologicalKrullDim_le_of_dense (c.i.imageι ≫ c.g) c.i.toImage.opensRange
      hdense).trans_eq ?_
    exact c.i.toImage.isOpenEmbedding.isEmbedding.topologicalKrullDim_eq_range.symm
  · exact c.i.toImage.isOpenEmbedding.isInducing.topologicalKrullDim_le

end AlgebraicGeometry
