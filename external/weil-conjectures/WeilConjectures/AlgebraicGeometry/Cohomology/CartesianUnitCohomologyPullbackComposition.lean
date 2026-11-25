/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Cohomology.UnitCohomologyPullbackLinear
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Cohomology.StructuralUnitCoefficientComposition
import WeilConjectures.AlgebraicGeometry.Cohomology.InverseImageCohomologyComposition

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- The explicitly constructed forward transport intertwines the two structural
pullback maps in a displayed cartesian square.
Source: Stacks Project, Tag 01F7, cohomology-equation-functorial; Tag 02KH,
the untensored comparison map; Mathlib's adjunction identity for pullback of the unit.
(blueprint: lem-pbc-cartesian-unit-cohomology-pullback-comp)

Proof: Put d = h.isoPullback.hom and a = baseChangeFst f. The projection identity
says d followed by a is iota'. The hom of pullbackObjUnitIso a is adjoint to the
structural map from the unit on C to a_* of the unit on the categorical pullback.
The adjunction unit formula therefore identifies baseChangeUnit followed by the
pushforward of that hom with this structural map. Coefficient naturality moves
the hom through the coefficient comparison. The structural unit maps compose:
on each open this is the composition law for the scheme's structure-sheaf maps.
Applying the inverse-image composition comparison identifies the resulting
coefficient map with coeff iota' of the structural unit map. The constant integer
comparison for the composite is the composite of the two constant comparisons:
both are the unique comparison between the left adjoints to constant sections.
Apply functoriality of mapExactFunctor on Ext and associativity of Ext composition
with these two comparisons. This identifies the composite of the canonical
base-change map with the specified forward transport with ordinary structural
pullback along iota', as claimed. Linearity was already proved in the definition
of the forward map; its bijectivity is not used here. The argument works in degree
zero and for empty schemes and zero rings. -/
theorem cartesian_unit_cohomology_pullback_comp
    {k k' : Type u} [CommRing k] [CommRing k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) (n : ℕ)
    (x : HOver f (SheafOfModules.unit C.ringCatSheaf) n) :
    unitCohomologyPullbackLinear (baseChangeSnd (S := k') f) f' h.isoPullback.hom
      h.isoPullback_hom_snd
      (baseChangedModule (S := k') f (SheafOfModules.unit C.ringCatSheaf))
      ((pullbackObjUnitIso (baseChangeFst (S := k') f)).hom ≫
        SheafOfModules.unitToPushforwardObjUnit h.isoPullback.hom.toRingCatSheafHom) n
      (H.baseChangeLinear (S := k') f (SheafOfModules.unit C.ringCatSheaf) n x) =
    Sheaf.H.map (coeff ι' (SheafOfModules.unitToPushforwardObjUnit
        ι'.toRingCatSheafHom)) n
      (Sheaf.H.mapFunctor (invImage ι') (constIso ι').symm
        ((SheafOfModules.toSheaf C.ringCatSheaf).obj
          (SheafOfModules.unit C.ringCatSheaf)) n x) := by
  let a := baseChangeFst (S := k') f
  let d := h.isoPullback.hom
  let F := (SheafOfModules.toSheaf C.ringCatSheaf).obj
    (SheafOfModules.unit C.ringCatSheaf)
  let α := coefficientUnit a (SheafOfModules.unit C.ringCatSheaf)
  let β := coeff d ((pullbackObjUnitIso a).hom ≫
    SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom)
  let y := Sheaf.H.mapFunctor (invImage a) (constIso a).symm F n x
  let z := Sheaf.H.mapFunctor (invImage d) (constIso d).symm ((invImage a).obj F) n y
  change Sheaf.H.map β n
    (Sheaf.H.mapFunctor (invImage d) (constIso d).symm _ n (Sheaf.H.map α n y)) = _
  have hn := Sheaf.H.mapFunctor_map (invImage d) (constIso d).symm n α y
  have hc := Sheaf.H.map_comp_apply ((invImage d).map α) β z
  have hs := structuralUnitCoefficient_comp d a
  have ht := Sheaf.H.map_comp_apply ((invImageComp d a).hom.app F)
    (coeff (d ≫ a) (SheafOfModules.unitToPushforwardObjUnit (d ≫ a).toRingCatSheafHom)) z
  have hi := inverseImageCohomology_comp d a F n x
  have hp : d ≫ a = ι' := h.isoPullback_hom_fst
  have he := (congrArg (fun w ↦ Sheaf.H.map β n w) hn).trans hc.symm
  have he' := he.trans (congrArg (fun φ ↦ Sheaf.H.map φ n z) hs)
  have he'' := (he'.trans ht).trans
    (congrArg (fun w ↦ Sheaf.H.map
      (coeff (d ≫ a) (SheafOfModules.unitToPushforwardObjUnit
        (d ≫ a).toRingCatSheafHom)) n w) hi)
  have heq := congrArg (fun (t : C' ⟶ C) ↦
    Sheaf.H.map (coeff t (SheafOfModules.unitToPushforwardObjUnit
      t.toRingCatSheafHom)) n
      (Sheaf.H.mapFunctor (invImage t) (constIso t).symm F n x)) hp
  exact he''.trans heq

end AlgebraicGeometry.Scheme.Modules
