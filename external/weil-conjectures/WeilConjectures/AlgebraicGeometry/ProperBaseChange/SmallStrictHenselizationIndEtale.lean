/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.RingTheory.ProEtale.IndEtale
import WeilConjectures.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale

/-! # Ind-etaleness for the small representative strict henselization

Transport the upstream affine-chart theorem along the canonical comparison of the small
representative colimit with the full affine pointed-neighbourhood colimit.

## References

* Stacks Project, Tag 04HX, with independence of the neighbourhood presentation from Tag 04GW
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem smallStrictHenselization_base_compatibility
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Spec.map (smallStrictHenselizationColimitIso s).inv ≫ strictLocalizationToBase s =
      strictHenselizationStructuralMap s := by
  classical
  let : HasColimit (strictHenselizationDiagram s) := inferInstance
  have := (strictHenselization_properties s).2.1
  let incl := strictHenselizationAffineInclusion s
  let : incl.IsEquivalence := strictHenselizationAffineInclusion_isEquivalence s
  let rep := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse
  let j := Classical.choice (IsCofiltered.nonempty (C :=
    SmallModel.{u} (strictHenselizationNeighbourhoods s)))
  have hbig := strictLocalizationCone_π_app_hom s (incl.obj (rep.obj j))
  rw [strictLocalizationCone_π_app] at hbig
  have hsmall := (exists_strictHenselizationStructuralMap s).choose_spec j
  have hleg := Functor.Final.ι_colimitIso_inv (rep ⋙ incl).op
    (strictHenselizationDiagram s) (op j)
  change colimit.ι (strictHenselizationDiagram s) (op (incl.obj (rep.obj j))) ≫
    (smallStrictHenselizationColimitIso s).inv =
      colimit.ι (strictHenselizationAffineDiagram s) (op j) at hleg
  let B := (rep.obj j).1.left.unop
  let f : Spec B ⟶ S := ((AffineEtale.Spec S).obj (rep.obj j).1).hom
  change (Spec.map (colimit.ι (strictHenselizationDiagram s)
    (op (incl.obj (rep.obj j)))) ≫ inv (Spec B).toSpecΓ) ≫ f =
      strictLocalizationToBase s at hbig
  change Spec.map (colimit.ι (strictHenselizationAffineDiagram s) (op j)) ≫
    Spec.map (ΓSpecIso B).inv ≫ f = strictHenselizationStructuralMap s at hsmall
  have hinv : inv (Spec B).toSpecΓ = Spec.map (ΓSpecIso B).inv := by
    apply (cancel_mono (Spec B).toSpecΓ).1
    simp only [IsIso.inv_hom_id, SpecMap_ΓSpecIso_inv_toSpecΓ]
  rw [hinv] at hbig
  have hh := congrArg (fun z ↦ Spec.map z ≫ Spec.map (ΓSpecIso B).inv ≫ f) hleg
  simp only [Spec.map_comp, Category.assoc] at hh
  rw [← hbig]
  simpa only [Category.assoc] using hh.trans hsmall

/-- The upstream ind-etale chart theorem also holds for the small representative model. -/
theorem smallStrictHenselization_indEtale_of_affine_chart
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω] [CommRing A]
    (s : Spec (.of Ω) ⟶ S) (R : CommRingCat.{u})
    (i : Spec R ⟶ S) [IsOpenImmersion i]
    (hs : s (IsLocalRing.closedPoint Ω) ∈ Set.range i)
    (e : Spec (.of A) ≅ strictHenselizationScheme s)
    (a : R →+* A)
    (ha : Spec.map (CommRingCat.ofHom a) ≫ i =
      e.hom ≫ strictHenselizationStructuralMap s) :
    letI : Algebra R A := a.toAlgebra
    Algebra.IndEtale R A := by
  apply strictHenselization_indEtale_of_affine_chart s R i hs
    (e ≪≫ Scheme.Spec.mapIso (smallStrictHenselizationColimitIso s).symm.op) a
  change Spec.map (CommRingCat.ofHom a) ≫ i =
    (e.hom ≫ Spec.map (smallStrictHenselizationColimitIso s).inv) ≫
      strictLocalizationToBase s
  rw [Category.assoc, smallStrictHenselization_base_compatibility]
  exact ha

end AlgebraicGeometry.Scheme
