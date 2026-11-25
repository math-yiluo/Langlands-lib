/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationBaseChangeCone


public import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry
import WeilConjectures.AlgebraicGeometry.StrictHenselizationCanonicalBaseChangeCone
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Existence of the canonical strict-local neighbourhood geometry

Source: Stacks Project, Tag 03Q9, first proof paragraph.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pullback of the strict henselization is the limit of the small affine
neighbourhood pullbacks, with qcqs stages and affine transition morphisms.
This supplies only geometry, with no derived sheaves, cocones or mates.
Source: Stacks, Tag 03Q9, first proof paragraph
(blueprint: lem-weil-pbc-strict-local-neighbourhood-geometry).

Proof: `strictHenselizationAffineBaseChangeCone_exists` supplies the limiting cone over
exactly the same small affine neighbourhood diagram, with vertex S_(s) ×_S X and
both specified projection equations. Precompose its legs with pullback symmetry
from X ×_S S_(s), and transport the limit by the induced cone isomorphism.
Precomposing each supplied projection equation with that symmetry proves `first`
and `over`. Each neighbourhood is a spectrum, hence affine, compact and
quasi-separated. Its stage projection is a base change of f, so Mathlib's
`QuasiCompact.compactSpace_of_compactSpace` and
`quasiSeparatedSpace_of_quasiSeparated` prove the two stage properties. Each
transition is the base change of a map between affine neighbourhoods, so
`MorphismProperty.pullbackLift_fst_snd` proves that it is affine. No global qcqs
assumption on X or S is used. -/
theorem nonempty_strictLocalNeighbourhoodGeometry {X S : Scheme.{v}}
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    Nonempty (StrictLocalNeighbourhoodGeometry f s) := by
  classical
  obtain ⟨π, hπ, hp, hf⟩ := Scheme.strictHenselizationAffineBaseChangeCone_exists f s
  let A := strictLocalNeighbourhoods s
  let D := strictLocalNeighbourhoodDiagram f s
  have hAff (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
      IsAffine (A.obj i).left := by
    change IsAffine (Spec _)
    infer_instance
  let hComp (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
      CompactSpace (D.obj i) := by
    let : IsAffine (A.obj i).left := hAff i
    exact QuasiCompact.compactSpace_of_compactSpace
      (Y := (A.obj i).left) (pullback.fst (A.obj i).hom f)
  let hQS (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
      QuasiSeparatedSpace (D.obj i) := by
    let : IsAffine (A.obj i).left := hAff i
    exact quasiSeparatedSpace_of_quasiSeparated
      (Y := (A.obj i).left) (pullback.fst (A.obj i).hom f)
  let hTrans {i j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)}
      (a : i ⟶ j) : IsAffineHom (D.map a) := by
    let : IsAffine (A.obj i).left := hAff i
    let : IsAffine (A.obj j).left := hAff j
    change IsAffineHom (pullback.lift _ _ _)
    exact MorphismProperty.pullbackLift_fst_snd
      (P := @IsAffineHom) f (MorphismProperty.Over.w (A.map a)).symm
      (isAffineHom_of_isAffine
        (X := (A.obj i).left) (Y := (A.obj j).left) _)
  let c : Cone D := Cone.mk _ π
  let e := pullbackSymmetry f (Scheme.strictLocalizationToBase s)
  let c' := c.extend e.hom
  refine ⟨{
    legs := c'.π
    isLimit := ?_
    compact := hComp
    quasiSeparated := hQS
    affine := hTrans
    first := ?_
    over := ?_ }⟩
  · exact hπ.some.ofIsoLimit (Cone.extendIso c e.symm)
  · intro i
    change e.hom ≫ π.app i ≫ pullback.fst (A.obj i).hom f = _
    simpa [e, A, strictLocalNeighbourhoods, Scheme.strictHenselizationEtaleDiagram] using
      congrArg (fun g ↦ e.hom ≫ g) (hf i)
  · intro i
    change e.hom ≫ π.app i ≫ pullback.snd (A.obj i).hom f = _
    simpa [e, A, strictLocalNeighbourhoods, Scheme.strictHenselizationEtaleDiagram] using
      congrArg (fun g ↦ e.hom ≫ g) (hp i)

end AlgebraicGeometry.Etale
