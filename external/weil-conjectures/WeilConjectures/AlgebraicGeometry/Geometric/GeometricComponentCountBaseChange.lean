/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Finite

import WeilConjectures.FieldTheory.CommonExtensionFields
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SepClosedFieldComponentsBijection

/-!
# Geometric component counts and base change

Source: Stacks Project, More on Morphisms, Tag 055F,
`lemma-base-change-fibres-nr-geometrically-connected-components`
(blueprint: lem-weil-pbc-geometric-component-count-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem componentCount_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    ENat.card (ConnectedComponents X) = ENat.card (ConnectedComponents Y) := by
  let h := e.hom.homeomorph
  apply ENat.card_congr
  exact
    { toFun := h.continuous.connectedComponentsMap
      invFun := h.symm.continuous.connectedComponentsMap
      left_inv := by
        intro c
        obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
        simp
      right_inv := by
        intro c
        obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
        simp }

private theorem componentCount_fieldExtension {k M : Type u}
    [Field k] [IsSepClosed k] [Field M]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of k)) (φ : k →+* M) :
    ENat.card (ConnectedComponents (pullback f (Spec.map (CommRingCat.ofHom φ)) : Scheme.{u})) =
      ENat.card (ConnectedComponents Z) := by
  algebraize [φ]
  let : Z.Over (Spec (CommRingCat.of k)) := ⟨f⟩
  exact ENat.card_congr (Equiv.ofBijective _
    (bijective_connectedComponentsMap_pullback_fst_of_isSepClosed k M Z))

private theorem componentCount_commonExtension {k : Type u} [Field k]
    {X S : Scheme.{u}} (f : X ⟶ S) (q : Spec (CommRingCat.of k) ⟶ S)
    (K L : Type u) [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L]
    (i : CommRingCat.of k ⟶ CommRingCat.of K)
    (j : CommRingCat.of k ⟶ CommRingCat.of L) :
    ENat.card (ConnectedComponents (pullback f (Spec.map i ≫ q) : Scheme.{u})) =
      ENat.card (ConnectedComponents (pullback f (Spec.map j ≫ q) : Scheme.{u})) := by
  let := i.hom.toAlgebra
  let := j.hom.toAlgebra
  obtain ⟨M, _, _, a, b, _, _⟩ := Field.exists_common_extension k K L
  let ai := Spec.map (CommRingCat.ofHom a.toRingHom)
  let bj := Spec.map (CommRingCat.ofHom b.toRingHom)
  have hab : ai ≫ (Spec.map i ≫ q) = bj ≫ (Spec.map j ≫ q) := by
    have h : ai ≫ Spec.map i = bj ≫ Spec.map j := by
      dsimp [ai, bj]
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      exact (a.commutes x).trans (b.commutes x).symm
    simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ q) h
  calc
    _ = ENat.card (ConnectedComponents
        (pullback (pullback.snd f (Spec.map i ≫ q)) ai : Scheme.{u})) :=
      (componentCount_fieldExtension (pullback.snd f (Spec.map i ≫ q)) a.toRingHom).symm
    _ = ENat.card (ConnectedComponents (pullback f (ai ≫ (Spec.map i ≫ q)) : Scheme.{u})) :=
      componentCount_iso (pullbackLeftPullbackSndIso f (Spec.map i ≫ q) ai)
    _ = ENat.card (ConnectedComponents (pullback f (bj ≫ (Spec.map j ≫ q)) : Scheme.{u})) := by
      rw [hab]
    _ = ENat.card (ConnectedComponents
        (pullback (pullback.snd f (Spec.map j ≫ q)) bj : Scheme.{u})) :=
      (componentCount_iso (pullbackLeftPullbackSndIso f (Spec.map j ≫ q) bj)).symm
    _ = _ := componentCount_fieldExtension (pullback.snd f (Spec.map j ≫ q)) b.toRingHom

/-- Geometric connected-component counts are independent of the algebraically closed
extension of the residue field and commute with arbitrary base change. The count is
`ENat.card` of `ConnectedComponents`: zero for an empty fibre and infinity for infinitely
many components.

Source: Stacks Project, More on Morphisms, Tag 055F
(blueprint: lem-weil-pbc-geometric-component-count-base-change).

Proof: First embed two algebraically closed extensions of the same residue field into a
common field using `Field.exists_common_extension` [lem-weil-common-extension-fields].
Algebraically closed fields are separably closed [def-pc-separably-closed]. The projections
from the common extension induce component bijections by
[lem-weil-pbc-sepclosed-field-components-bijection]. The pullback universal property
[def-pc-fibre-product] identifies their source schemes, proving independence of the field.
Next, for `t` over `s`, use the residue-field embedding from `κ(s)` to `κ(t)`
[def-weil-residue-field] to embed the two chosen closed fields into a common field over
`κ(s)`. The pullback universal property identifies both further base changes with the
same scheme over that field. Apply the same component bijections and compose them with
the homeomorphism induced by this identification. Their extended-natural cardinalities
agree, including the empty and infinite cases. Independence already proved makes this
exactly the claimed equality of geometric component counts. -/
theorem geometricComponentCount_baseChange {X S : Scheme.{u}} (f : X ⟶ S) :
    (∀ (s : S) (K L : Type u) [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L]
      (i : S.residueField s ⟶ CommRingCat.of K)
      (j : S.residueField s ⟶ CommRingCat.of L),
      ENat.card (ConnectedComponents
        (pullback f (Spec.map i ≫ S.fromSpecResidueField s) : Scheme.{u})) =
      ENat.card (ConnectedComponents
        (pullback f (Spec.map j ≫ S.fromSpecResidueField s) : Scheme.{u}))) ∧
    (∀ (T : Scheme.{u}) (g : T ⟶ S) (t : T)
      (K L : Type u) [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L]
      (i : S.residueField (g t) ⟶ CommRingCat.of K)
      (j : T.residueField t ⟶ CommRingCat.of L),
      ENat.card (ConnectedComponents
        (pullback (pullback.snd f g)
          (Spec.map j ≫ T.fromSpecResidueField t) : Scheme.{u})) =
      ENat.card (ConnectedComponents
        (pullback f (Spec.map i ≫ S.fromSpecResidueField (g t)) : Scheme.{u}))) := by
  constructor
  · intro s K L _ _ _ _ i j
    exact componentCount_commonExtension f (S.fromSpecResidueField s) K L i j
  · intro T g t K L _ _ _ _ i j
    let q := Spec.map j ≫ T.fromSpecResidueField t
    have hq : q ≫ g =
        Spec.map (g.residueFieldMap t ≫ j) ≫ S.fromSpecResidueField (g t) := by
      simp only [q, Spec.map_comp, Category.assoc,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    calc
      _ = ENat.card (ConnectedComponents (pullback f (q ≫ g) : Scheme.{u})) :=
        componentCount_iso (pullbackLeftPullbackSndIso f g q)
      _ = ENat.card (ConnectedComponents
          (pullback f (Spec.map (g.residueFieldMap t ≫ j) ≫
            S.fromSpecResidueField (g t)) : Scheme.{u})) := by rw [hq]
      _ = _ := componentCount_commonExtension f (S.fromSpecResidueField (g t)) L K
        (g.residueFieldMap t ≫ j) i

end AlgebraicGeometry
