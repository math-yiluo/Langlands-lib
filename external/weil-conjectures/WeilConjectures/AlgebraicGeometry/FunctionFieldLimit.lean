/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Filtered.Final
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField

/-!
# The generic point of an integral scheme as an inverse limit

Let `X` be an integral scheme with function field `K`. The nonempty affine opens `U` of `X`,
ordered by inclusion, form a cofiltered category, and `Spec K` is the limit of the affine schemes
`Spec Γ(X, U)`: the function field is the stalk at the generic point, the colimit of the rings of
sections over the open neighbourhoods of the generic point, among which the nonempty affine opens
are cofinal, and `Spec` turns colimits of rings into limits of schemes.

## Main definitions

- `AlgebraicGeometry.Scheme.NonemptyAffineOpens`: the nonempty affine opens of `X`.
- `AlgebraicGeometry.Scheme.affineOpensDiagram`: the diagram `U ↦ Spec Γ(X, U)`.
- `AlgebraicGeometry.Scheme.functionFieldCone`: the cone with point `Spec K`.

## Main statements

- `AlgebraicGeometry.Scheme.isLimitFunctionFieldCone`: it is a limit cone.
- `AlgebraicGeometry.Scheme.fromSpecFunctionField_eq_functionFieldCone_comp`: the canonical
  morphism `Spec K ⟶ X` factors through every `Spec Γ(X, U) ⟶ X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The nonempty affine opens of an integral scheme, ordered by inclusion. -/
def NonemptyAffineOpens : Type u :=
  {U : X.Opens // IsAffineOpen U ∧ (U : Set X).Nonempty}

instance : PartialOrder X.NonemptyAffineOpens :=
  inferInstanceAs (PartialOrder {U : X.Opens // IsAffineOpen U ∧ (U : Set X).Nonempty})

variable {X} in
lemma NonemptyAffineOpens.genericPoint_mem (U : X.NonemptyAffineOpens) :
    genericPoint X ∈ U.1 :=
  ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).2 (by simpa using U.2.2)

/-- Every open neighbourhood of the generic point contains a nonempty affine open. -/
lemma NonemptyAffineOpens.exists_le {V : X.Opens} (hV : genericPoint X ∈ V) :
    ∃ U : X.NonemptyAffineOpens, U.1 ≤ V := by
  obtain ⟨U, hU, hxU, hUV⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hV
  exact ⟨⟨U, hU, ⟨_, hxU⟩⟩, hUV⟩

instance : Nonempty X.NonemptyAffineOpens :=
  ⟨(NonemptyAffineOpens.exists_le X (V := ⊤) trivial).choose⟩

instance : IsDirected X.NonemptyAffineOpens (· ≥ ·) where
  directed U V := by
    obtain ⟨W, hW⟩ := NonemptyAffineOpens.exists_le X (V := U.1 ⊓ V.1)
      ⟨U.genericPoint_mem, V.genericPoint_mem⟩
    exact ⟨W, hW.trans inf_le_left, hW.trans inf_le_right⟩

/-- The nonempty affine opens as open neighbourhoods of the generic point. -/
abbrev NonemptyAffineOpens.toOpenNhds : X.NonemptyAffineOpens ⥤ OpenNhds (genericPoint X) :=
  (show Monotone fun U : X.NonemptyAffineOpens ↦
    (⟨U.1, U.genericPoint_mem⟩ : OpenNhds (genericPoint X)) from fun _ _ h ↦ h).functor

instance : (NonemptyAffineOpens.toOpenNhds X).op.Final :=
  Functor.final_of_exists_of_isFiltered _
    (fun V ↦ by
      obtain ⟨U, hU⟩ := NonemptyAffineOpens.exists_le X V.unop.2
      exact ⟨op U, ⟨(homOfLE hU).op⟩⟩)
    (fun s s' ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)

/-- The diagram of rings `U ↦ Γ(X, U)` over the nonempty affine opens. -/
noncomputable abbrev affineOpensRingDiagram : X.NonemptyAffineOpensᵒᵖ ⥤ CommRingCat.{u} :=
  (NonemptyAffineOpens.toOpenNhds X).op ⋙ (OpenNhds.inclusion (genericPoint X)).op ⋙ X.presheaf

/-- The function field as a cocone over the sections over the nonempty affine opens. -/
noncomputable def affineOpensRingCocone : Cocone X.affineOpensRingDiagram :=
  (colimit.cocone ((OpenNhds.inclusion (genericPoint X)).op ⋙ X.presheaf)).whisker
    (NonemptyAffineOpens.toOpenNhds X).op

/-- The function field is the colimit of the sections over the nonempty affine opens. -/
noncomputable def isColimitAffineOpensRingCocone : IsColimit X.affineOpensRingCocone :=
  (Functor.Final.isColimitWhiskerEquiv (NonemptyAffineOpens.toOpenNhds X).op _).symm
    (colimit.isColimit _)

/-- The diagram of affine schemes `U ↦ Spec Γ(X, U)` over the nonempty affine opens. -/
noncomputable abbrev affineOpensDiagram : X.NonemptyAffineOpens ⥤ Scheme.{u} :=
  X.affineOpensRingDiagram.rightOp ⋙ Scheme.Spec

/-- The cone over `U ↦ Spec Γ(X, U)` with point `Spec K`. -/
noncomputable def functionFieldCone : Cone X.affineOpensDiagram :=
  Scheme.Spec.mapCone (coneRightOpOfCocone X.affineOpensRingCocone)

/-- **The generic point is the limit of the nonempty affine opens.** -/
noncomputable def isLimitFunctionFieldCone : IsLimit X.functionFieldCone :=
  isLimitOfPreserves Scheme.Spec (isLimitConeRightOpOfCocone _ X.isColimitAffineOpensRingCocone)

/-- The open immersions `Spec Γ(X, U) ⟶ X` of the nonempty affine opens. -/
noncomputable def affineOpensDiagramι :
    X.affineOpensDiagram ⟶ (Functor.const X.NonemptyAffineOpens).obj X where
  app U := U.2.1.fromSpec
  naturality U V f := by
    change Spec.map (X.presheaf.map (homOfLE (leOfHom f) : U.1 ⟶ V.1).op) ≫ V.2.1.fromSpec = _
    rw [IsAffineOpen.map_fromSpec _ U.2.1]
    simp

lemma functionFieldCone_pt : X.functionFieldCone.pt = Spec X.functionField := rfl


/-- The canonical morphism `Spec K ⟶ X` factors through every `Spec Γ(X, U) ⟶ X`. -/
lemma fromSpecFunctionField_eq_functionFieldCone_comp (U : X.NonemptyAffineOpens) :
    X.fromSpecFunctionField =
      X.functionFieldCone.π.app U ≫ X.affineOpensDiagramι.app U := by
  exact (U.2.1.fromSpecStalk_eq_fromSpecStalk U.genericPoint_mem).symm

end AlgebraicGeometry.Scheme
