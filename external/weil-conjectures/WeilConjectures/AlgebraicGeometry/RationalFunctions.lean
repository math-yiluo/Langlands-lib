/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Category.Ring.Colimits

/-!
# The ring of rational functions on a scheme

We define the diagram of section rings over the dense opens of a scheme `X` and its colimit
`Scheme.rationalFunctionRing X`, the ring of rational functions on `X`.

Source: Stacks Project, Morphisms, Definitions 01RS, 01RT, 01RU and Lemma 01RV
(blueprint: def-sc-function-field).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

/-- The dense open subsets of a scheme, ordered by inclusion (Stacks, Tag 01RS;
(blueprint: def-sc-function-field)). -/
def DenseOpens (X : Scheme) := {U : X.Opens // Dense (U : Set X)}

instance (X : Scheme) : PartialOrder (DenseOpens X) := inferInstanceAs
  (PartialOrder {U : X.Opens // Dense (U : Set X)})

/-- The intersection of two dense opens is dense (Stacks, Tag 01RS;
(blueprint: def-sc-function-field)). -/
def DenseOpens.inter {X : Scheme} (U V : DenseOpens X) : DenseOpens X :=
  ⟨U.val ⊓ V.val, by
    change Dense ((U.val : Set X) ∩ (V.val : Set X))
    exact U.property.inter_of_isOpen_left V.property U.val.isOpen⟩

/-- Dense opens are cofiltered: `⊤` is dense and two dense opens contain their intersection. -/
instance (X : Scheme) : IsCofiltered (DenseOpens X) := by
  have : Nonempty (DenseOpens X) := ⟨⟨⊤, dense_univ⟩⟩
  have : IsDirected (DenseOpens X) (· ≥ ·) :=
    ⟨fun U V => ⟨U.inter V, (inf_le_left : U.val ⊓ V.val ≤ U.val),
      (inf_le_right : U.val ⊓ V.val ≤ V.val)⟩⟩
  infer_instance

/-- The inclusion of dense opens into all opens (Stacks, Tag 01RS;
(blueprint: def-sc-function-field)). -/
def denseOpensInclusion (X : Scheme) : DenseOpens X ⥤ X.Opens where
  obj U := U.val
  map f := homOfLE (leOfHom f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The section rings over dense opens with restriction maps (Stacks, Tag 01RV;
(blueprint: def-sc-function-field)). -/
def denseOpenSections (X : Scheme) : (DenseOpens X)ᵒᵖ ⥤ CommRingCat :=
  (denseOpensInclusion X).op ⋙ X.presheaf

/-- The ring of rational functions on a scheme is the colimit of its section rings on
 dense opens, with transition maps given by restriction. Thus elements are section classes,
 identified when they agree on a smaller dense open; addition and multiplication are induced
 by restriction to intersections and the ring operations on sections. Source: Stacks Project,
 Tags 01RT, 01RU and Lemma 01RV (blueprint: def-sc-function-field). -/
noncomputable def rationalFunctionRing (X : Scheme.{u}) : CommRingCat.{u} :=
  colimit (denseOpenSections X)

end Scheme

end AlgebraicGeometry
