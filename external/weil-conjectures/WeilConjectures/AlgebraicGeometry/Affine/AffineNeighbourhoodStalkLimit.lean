/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Filtered.Final

/-!
# The spectrum of a local stalk as a limit of affine neighbourhoods

Source: Stacks Project, Limits, Tag 01YW, and Sheaves, section 0078.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The spectrum of a stalk is an affine-transition inverse limit of affine open
neighbourhoods, indexed by a directed preorder. The projection equations use the
canonical morphism from the spectrum of the stalk to the original scheme.

Source: Stacks Project, Sheaves section 0078 and Limits Tag 01YW;
compare `Scheme.isLimitFunctionFieldCone` for integral schemes.
(blueprint: lem-weil-pbc-affine-neighbourhood-stalk-limit)

Proof: Order affine neighbourhoods of x by inclusion. Every neighbourhood contains an
affine one, and the intersection of two contains an affine neighbourhood, so this is
cofiltered and cofinal among all neighbourhoods. Restriction of the stalk's defining
ring colimit to this cofinal family is still a colimit. Spec converts it to a limit.
Reindex by the order-dual preorder to obtain the directed-set convention. The open
immersions from affine charts identify its objects with open subschemes, and the germ
maps give the asserted projection equations. No reducedness or irreducibility is used.
-/
theorem exists_affine_neighbourhood_stalk_limit (X : Scheme.{u}) (x : X) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
      (e : Spec (X.presheaf.stalk x) ≅ c.pt),
      Nonempty (IsLimit c) ∧ (∀ i, IsAffine (D.obj i)) ∧
      (∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)) ∧
      ∀ i : I, ∃ (U : X.Opens) (_ : x ∈ U) (_ : IsAffineOpen U)
        (eU : D.obj (op i) ≅ U.toScheme),
        e.hom ≫ c.π.app (op i) ≫ eU.hom ≫ U.ι = X.fromSpecStalk x := by
  classical
  let N := {U : X.Opens // IsAffineOpen U ∧ x ∈ U}
  have hex {V : X.Opens} (hx : x ∈ V) : ∃ U : N, U.1 ≤ V := by
    obtain ⟨U, hU, hxU, hUV⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hx
    exact ⟨⟨U, hU, hxU⟩, hUV⟩
  let : Nonempty N := ⟨(hex (V := ⊤) trivial).choose⟩
  let : IsDirected N (· ≥ ·) := ⟨fun U V ↦ by
    obtain ⟨W, hW⟩ := hex (V := U.1 ⊓ V.1) ⟨U.2.2, V.2.2⟩
    exact ⟨W, hW.trans inf_le_left, hW.trans inf_le_right⟩⟩
  let F : N ⥤ OpenNhds x :=
    (show Monotone (fun U : N ↦ (⟨U.1, U.2.2⟩ : OpenNhds x)) from
      fun _ _ h ↦ h).functor
  have : F.op.Final := Functor.final_of_exists_of_isFiltered _
    (fun V ↦ by
      obtain ⟨U, hU⟩ := hex V.unop.2
      exact ⟨op U, ⟨(homOfLE hU).op⟩⟩)
    (fun s s' ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
  let R := F.op ⋙ (OpenNhds.inclusion x).op ⋙ X.presheaf
  let C : Cocone R :=
    (colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf)).whisker F.op
  have hC : IsColimit C :=
    (Functor.Final.isColimitWhiskerEquiv F.op _).symm (colimit.isColimit _)
  let A := R.rightOp ⋙ Scheme.Spec
  let a : Cone A := Scheme.Spec.mapCone (coneRightOpOfCocone C)
  have ha : IsLimit a :=
    isLimitOfPreserves Scheme.Spec (isLimitConeRightOpOfCocone _ hC)
  let E := (orderDualEquivalence N).op.trans (opOpEquivalence N)
  let D := E.functor ⋙ A
  let c := a.whisker E.functor
  refine ⟨Nᵒᵈ, inferInstance, inferInstance, inferInstance, D, c, Iso.refl _,
    ⟨ha.whiskerEquivalence E⟩, ?_, ?_, ?_⟩
  · intro i
    exact inferInstanceAs (IsAffine (Spec Γ(X, (E.functor.obj i).1)))
  · intro i j f
    have : IsAffine (D.obj i) :=
      inferInstanceAs (IsAffine (Spec Γ(X, (E.functor.obj i).1)))
    have : IsAffine (D.obj j) :=
      inferInstanceAs (IsAffine (Spec Γ(X, (E.functor.obj j).1)))
    infer_instance
  · intro i
    let U := E.functor.obj (op i)
    refine ⟨U.1, U.2.2, U.2.1, U.2.1.isoSpec.symm, ?_⟩
    change 𝟙 _ ≫ Spec.map (X.presheaf.germ U.1 x U.2.2) ≫
      U.2.1.isoSpec.inv ≫ U.1.ι = _
    simpa only [Category.id_comp, IsAffineOpen.isoSpec_inv_ι,
      IsAffineOpen.fromSpecStalk] using
      U.2.1.fromSpecStalk_eq_fromSpecStalk U.2.2

end AlgebraicGeometry
