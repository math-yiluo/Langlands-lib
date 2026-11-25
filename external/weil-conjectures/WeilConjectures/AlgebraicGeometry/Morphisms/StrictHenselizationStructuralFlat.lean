/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.ProEtale.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Flatness of the canonical affine strict henselization map

## References

* Stacks Project, Tags 04HX and 07QM
* Tag 0EYG, first reduction paragraph
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ring map inducing the canonical strict henselization structural map is flat. -/
theorem strictHenselization_structural_ringHom_flat
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    RingHom.Flat b.hom := by
  classical
  have := (strictHenselizationAffineProperties barY).2.1
  let I := SmallModel.{u} (strictHenselizationNeighbourhoods barY)
  let F := (equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse
  let ψ (i : I) := ((AffineEtale.Spec (Spec R)).obj (F.obj i).1).hom
  let t : (Functor.const Iᵒᵖ).obj R ⟶ strictHenselizationAffineDiagram barY :=
    { app := fun i ↦ (ΓSpecIso R).inv ≫ (ψ i.unop).appTop
      naturality := fun i j a ↦ by
        dsimp only [Functor.const_obj_map, Functor.const_obj_obj]
        rw [Category.id_comp]
        symm
        change ((ΓSpecIso R).inv ≫ (ψ i.unop).appTop) ≫
          (Spec.map (F.map a.unop).1.left.unop).appTop =
            (ΓSpecIso R).inv ≫ (ψ j.unop).appTop
        rw [Category.assoc, ← Scheme.Hom.comp_appTop]
        exact congrArg (fun k ↦ (ΓSpecIso R).inv ≫ k.appTop) (F.map a.unop).1.w }
  apply RingHom.Flat.of_isColimit b Iᵒᵖ (strictHenselizationAffineDiagram barY)
    (t := t) (c := (smallStrictHenselizationCocone barY).ι)
    (isColimitSmallStrictHenselizationCocone barY)
  intro i
  constructor
  · have : Etale (ψ i.unop) := inferInstance
    have : IsAffine ((AffineEtale.Spec (Spec R)).obj (F.obj i.unop).1).left := by
      change IsAffine (Spec (F.obj i.unop).1.left.unop)
      infer_instance
    exact (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (ΓSpecIso R).inv)).comp
        (Scheme.Hom.flat_appTop (f := ψ i.unop)
          (X := Spec (F.obj i.unop).1.left.unop) (Y := Spec R))
  · have h := (strictHenselizationStructuralMap_eq barY)
      i.unop
    apply Spec.map_injective
    rw [hb]
    change Spec.map ((ΓSpecIso R).inv ≫ (ψ i.unop).appTop ≫
      (smallStrictHenselizationCocone barY).ι.app i) = _
    have ht : (ΓSpecIso R).inv ≫ (ψ i.unop).appTop =
        Spec.preimage (ψ i.unop) ≫ (ΓSpecIso (F.obj i.unop).1.left.unop).inv := by
      rw [ΓSpecIso_inv_naturality, Spec.map_preimage]
    rw [← Category.assoc, ht, Category.assoc, Spec.map_comp, Spec.map_comp,
      Spec.map_preimage]
    change Spec.map ((smallStrictHenselizationCocone barY).ι.app i) ≫
      Spec.map (ΓSpecIso (F.obj i.unop).1.left.unop).inv ≫ ψ i.unop =
        strictLocalizationToBase barY at h
    exact h

end AlgebraicGeometry.Scheme
