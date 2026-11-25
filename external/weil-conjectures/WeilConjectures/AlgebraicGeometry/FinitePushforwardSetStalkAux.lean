/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Finite.Stalk
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Types.Products

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- (blueprint: lem-weil-pbc-sets-finite-pushforward-stalk-map-bijective)
The substantive restriction-of-germs bijection in the finite pushforward stalk formula,
assuming finiteness of the geometric fibre.

Source: Stacks Project, Proposition 59.55.2, Tag 03QP (1), first display and its
proof. The proof identifies the pushforward stalk with sections of the inverse image
on the strict henselization. A finite base change is affine and its finite algebra is
a product of henselian local factors; the separably closed residue field makes every
factor strictly henselian. The resulting clopen pieces form a disjoint etale cover,
so the sheaf condition identifies sections on the whole base change with the product
of sections on the pieces. Sections on each piece identify with its stalk, and
inverse-image stalks identify with the stalks of `H`. Matching the unique geometric
point of each factor with the finite geometric fibre, then checking a representative
germ, gives exactly the displayed restriction map. -/
theorem finite_pushforward_set_stalk_map_bijective_of_finite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (H : Sheaf X.smallEtaleTopology (Type (u + 1)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (hfin : Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) :
    Function.Bijective
        (fun a : (Scheme.pointSmallEtale y).sheafFiber.obj
            ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
              Y.smallEtaleTopology X.smallEtaleTopology).obj H) ↦
          fun t : {x : Spec (.of Ω) ⟶ X // x ≫ f = y} ↦
            (colimit.pre
              ((Functor.Elements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙ H.obj)
              (Etale.baseChangeNbhd f y t).op) a) := by
  set_option backward.isDefEq.respectTransparency.types false in
  open Scheme Scheme.Hom Scheme.Hom.SplitNbhd Opposite in
  classical
  let : Finite (GeometricFiber f y) := hfin
  let : Fintype (GeometricFiber f y) := Fintype.ofFinite _
  have : PreservesLimitsOfShape (Discrete (GeometricFiber f y))
      (colim (J := (SplitNbhd f y)ᵒᵖ) (C := Type (u + 1))) :=
    preservesLimitsOfShape_of_equiv
      (Discrete.equivalence (Fintype.equivFin (GeometricFiber f y)).symm) colim
  let e₀ : colimit (sectionsFunctor f y H) ≅
      (pointSmallEtale y).sheafFiber.obj
        ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
          Y.smallEtaleTopology X.smallEtaleTopology).obj H) :=
    Functor.Final.colimitIso (forget f y).op
      ((Functor.Elements.π (pointSmallEtale y).fiber).op ⋙
        ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
          Y.smallEtaleTopology X.smallEtaleTopology).obj H).obj)
  let e₁ (t : GeometricFiber f y) :
      colimit (pieceSectionsFunctor f y H t) ≅ (pointSmallEtale t.1).sheafFiber.obj H :=
    Functor.Final.colimitIso (pieceFunctor t).op
      ((Functor.Elements.π (pointSmallEtale t.1).fiber).op ⋙ H.obj)
  let r (t : GeometricFiber f y) :
      (pointSmallEtale y).sheafFiber.obj
        ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
          Y.smallEtaleTopology X.smallEtaleTopology).obj H) ⟶
        (pointSmallEtale t.1).sheafFiber.obj H :=
    colimit.pre ((Functor.Elements.π (pointSmallEtale t.1).fiber).op ⋙ H.obj)
      (Etale.baseChangeNbhd f y t).op
  have he : e₀.hom ≫ Pi.lift r =
      colim.map (sectionsIsoPi f y H).hom ≫
        (PreservesProduct.iso colim (pieceSectionsFunctor f y H)).hom ≫
        Limits.Pi.map (fun t ↦ (e₁ t).hom) := by
    apply colimit.hom_ext
    intro s
    apply Pi.hom_ext
    intro t
    simp only [Category.assoc, Pi.lift_comp_π, Limits.Pi.map_π, PreservesProduct.iso_hom]
    dsimp only [r, e₀, e₁]
    erw [Functor.Final.ι_colimitIso_hom_assoc,
      colimit.ι_pre ((Functor.Elements.π (pointSmallEtale t.1).fiber).op ⋙ H.obj)
        (Etale.baseChangeNbhd f y t).op (op s.unop.obj),
      piComparison_comp_π_assoc, colim_map, ι_colimMap_assoc, ι_colimMap_assoc,
      sectionsIsoPi_hom, ← NatTrans.comp_app_assoc, Pi.lift_comp_π,
      Functor.Final.ι_colimitIso_hom]
    exact (colimit.w ((Functor.Elements.π (pointSmallEtale t.1).fiber).op ⋙ H.obj)
      (Functor.Elements.homMk
        (x := Functor.elementsMk _ (s.unop.pieceObj t) (s.unop.piecePt t))
        (y := (Etale.baseChangeNbhd f y t).obj s.unop.obj) (s.unop.pieceIncl t)
        (CategoryTheory.Over.OverMorphism.ext (s.unop.piecePt_comp_pieceIncl t))).op).symm
  have : IsIso (Pi.lift r) := by
    rw [← Iso.eq_inv_comp] at he
    rw [he]
    infer_instance
  let e := asIso (Pi.lift r) ≪≫
    Types.productIso.{u, u + 1}
      (fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber.obj H)
  have hmap : (fun a ↦ e.hom a) = (fun a t ↦ r t a) := by
    funext a t
    have hp : e.hom ≫ (↾fun z ↦ z t) = r t := by
      simp only [e, Iso.trans_hom, Category.assoc,
        Types.productIso_hom_comp_eval, asIso_hom, Pi.lift_comp_π]
    exact ConcreteCategory.congr_hom hp a
  change Function.Bijective (fun a t ↦ r t a)
  rw [← hmap]
  exact ConcreteCategory.bijective_of_isIso e.hom

end AlgebraicGeometry
