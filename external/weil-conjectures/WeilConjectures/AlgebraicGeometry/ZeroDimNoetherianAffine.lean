/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Ample
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Affineness and ampleness in dimension zero

Source: Stacks Project, Properties, Lemmas 0AAX and 0CKV, and Definition 01PS
(blueprint: lem-sc-zero-dim-noetherian-affine).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def unitStalkCocone (Y : Scheme.{u}) (y : Y) :
    CategoryTheory.Limits.Cocone ((TopologicalSpace.OpenNhds.inclusion y).op ⋙
      (𝟙_ Y.Modules).presheaf) where
  pt := AddCommGrpCat.of (Y.presheaf.stalk y)
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        (Y.presheaf.germ U.unop.1 y U.unop.2).hom.toAddMonoidHom
      naturality := by
        intro U V f
        ext r
        exact Y.presheaf.germ_res_apply f.unop y V.unop.2 r }

private noncomputable def unitStalkToRingAdd (Y : Scheme.{u}) (y : Y) :
    (𝟙_ Y.Modules).presheaf.stalk y →+ Y.presheaf.stalk y :=
  (CategoryTheory.Limits.colimit.desc _ (unitStalkCocone Y y)).hom

private lemma unitStalkToRingAdd_germ (Y : Scheme.{u}) (y : Y)
    (U : Y.Opens) (hy : y ∈ U) (r : Γ(Y, U)) :
    unitStalkToRingAdd Y y ((𝟙_ Y.Modules).presheaf.germ U y hy r) =
      Y.presheaf.germ U y hy r := by
  change (CategoryTheory.Limits.colimit.ι _
    (Opposite.op (⟨U, hy⟩ : TopologicalSpace.OpenNhds y)) ≫
      CategoryTheory.Limits.colimit.desc _ (unitStalkCocone Y y)) r = _
  rw [CategoryTheory.Limits.colimit.ι_desc]
  rfl

private noncomputable def unitStalkToRing (Y : Scheme.{u}) (y : Y) :
    (𝟙_ Y.Modules).presheaf.stalk y →ₗ[Y.presheaf.stalk y] Y.presheaf.stalk y :=
  stalkLinearMapMk (unitStalkToRingAdd Y y) fun U hy r m => by
    rw [unitStalkToRingAdd_germ, unitStalkToRingAdd_germ]
    let m' : Γ(Y, U) := m
    change Y.presheaf.germ U y hy (r * m') =
      Y.presheaf.germ U y hy r * Y.presheaf.germ U y hy m'
    exact map_mul (Y.presheaf.germ U y hy).hom r m'

/-- The tensor unit is ample on a compact affine scheme. The proof unfolds `IsAmple`,
chooses the global section `1` in tensor power one, and identifies its nonvanishing locus
with the top open using the stalk germ of `1`. Source: Stacks Project, Definition 01PS
(blueprint: def-weil-pbc-ample-invertible-module). -/
private theorem isAmple_tensorUnit_of_affine (Y : Scheme.{u}) [CompactSpace Y]
    (h_aff : IsAffine Y) : IsAmple Y (𝟙_ Y.Modules) := by
  have : IsAffine Y := h_aff
  refine ⟨inferInstance, fun x => ?_⟩
  let e : (𝟙_ Y.Modules).tensorPow 1 ≅ 𝟙_ Y.Modules := ρ_ _
  let s := e.inv.val.app (Opposite.op ⊤) (1 : Γ(Y, ⊤))
  refine ⟨1, Nat.zero_lt_one, s, ⊤, trivial, ?_, ?_⟩
  · exact isAffineOpen_top Y
  · intro y
    simp only [TopologicalSpace.Opens.mem_top, true_iff]
    intro h
    let f := (unitStalkToRing Y y).comp (e.hom.stalkLinearMap y)
    have hf : f ((TopCat.Presheaf.germ
        ((𝟙_ Y.Modules).tensorPow 1).val.presheaf ⊤ y trivial) s) = 1 := by
      change unitStalkToRing Y y
        (e.hom.stalkLinearMap y (((𝟙_ Y.Modules).tensorPow 1).presheaf.germ
          ⊤ y trivial s)) = 1
      rw [Hom.stalkLinearMap_germ]
      change unitStalkToRingAdd Y y
        ((𝟙_ Y.Modules).presheaf.germ ⊤ y trivial
          (e.hom.val.app (Opposite.op ⊤) (e.inv.val.app (Opposite.op ⊤) (1 : Γ(Y, ⊤))))) = 1
      have he : e.hom.val.app (Opposite.op ⊤)
          (e.inv.val.app (Opposite.op ⊤) (1 : Γ(Y, ⊤))) = (1 : Γ(Y, ⊤)) := by
        have hcomp := congrArg
          (fun φ : (𝟙_ Y.Modules) ⟶ (𝟙_ Y.Modules) => φ.val.app (Opposite.op ⊤))
          e.inv_hom_id
        exact ConcreteCategory.congr_hom hcomp (1 : Γ(Y, ⊤))
      rw [he, unitStalkToRingAdd_germ]
      exact map_one (Y.presheaf.germ ⊤ y trivial).hom
    have hm := Submodule.mem_map_of_mem (f := f) h
    rw [Submodule.map_smul'', Submodule.map_top] at hm
    have hle : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) • LinearMap.range f ≤
        IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
      Submodule.smul_le.2 fun r hr m _ =>
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).mul_mem_right m hr
    have hm' := hle hm
    rw [hf] at hm'
    exact (IsLocalRing.maximalIdeal.isMaximal (Y.presheaf.stalk y)).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hm' isUnit_one)

/-- A Noetherian separated scheme of topological Krull dimension at most zero is affine,
and its trivial invertible module is ample. The empty scheme is included.
Source: Stacks Project, Properties, Lemmas 0AAX and 0CKV, and Definition 01PS
(blueprint: lem-sc-zero-dim-noetherian-affine).

Proof:
1. The dimension bound makes `Y` locally Artinian
(`IsLocallyArtinian.of_topologicalKrullDim_le_zero`), hence Artinian, so its underlying
space is finite (`IsArtinianScheme.finite`) and discrete. This includes the empty case.
2. Mathlib's finite-discrete scheme instance gives `IsAffine Y` directly.
3. Take tensor power one. Transport the global section `1` along the inverse right
unitor to obtain a section of this tensor power. Choose the top affine open.
At every point the linear stalk map induced by the unitor, followed by the canonical
linear map from the structure-module stalk to the local ring, sends its germ to `1`.
If the germ belonged to the maximal ideal times the stalk module, linearity would
put `1` in the maximal ideal, a contradiction. Thus the nonvanishing locus is all of Y.
Compactness supplies the remaining condition of ampleness.
-/
theorem isAffine_and_isAmple_tensorUnit_of_dim_le_zero (Y : Scheme.{u})
    [IsLocallyNoetherian Y] [CompactSpace Y] [Y.IsSeparated]
    (hdim : topologicalKrullDim Y ≤ 0) :
    IsAffine Y ∧ IsAmple Y (𝟙_ Y.Modules) := by
  have : IsLocallyArtinian Y := .of_topologicalKrullDim_le_zero hdim
  have : IsArtinianScheme Y := {}
  have h_aff : IsAffine Y := inferInstance
  exact ⟨h_aff, isAmple_tensorUnit_of_affine Y h_aff⟩

end AlgebraicGeometry.Scheme.Modules
