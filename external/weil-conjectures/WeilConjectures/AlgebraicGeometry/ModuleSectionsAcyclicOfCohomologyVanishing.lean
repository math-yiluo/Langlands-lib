/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.AlgebraicGeometry.Modules.Ext

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- Module-cohomology vanishing on all opens implies acyclicity for sections on all opens.

Source: Stacks Project, Cohomology of Sheaves, Tag 01E1 (2), and the final clause of 01EX.
(blueprint: lem-weil-pbc-module-sections-acyclic-of-cohomology-vanishing).

Proof: Fix V and choose an injective resolution F → J• in S.Modules, which has enough
injectives. Restriction to V is exact and preserves injectives by Tag 01E1 (2), so the
restricted augmented complex is an injective resolution of F|V. Evaluation of J• at V
computes the right derived functors of the module-valued sections functor on S.Modules.
Global sections of the restricted resolution compute moduleCohomology on V.toScheme.
For each term, restricted global sections are the original sections on V. The canonical
identification of O_V(V) with O_S(V) transports the scalar module structures; it is
compatible with all differentials. Hence these complexes have the same cohomology up
to that scalar equivalence. Equivalences preserve and reflect zero objects. The assumed
vanishing in degree q+1 gives IsZero for the (q+1)-st right derived sections object.
Quantifying over q is rightAcyclic, and quantifying over V gives the conclusion. -/
theorem module_sections_acyclic_of_cohomology_vanishing (S : Scheme.{u}) (F : S.Modules)
    (hcoh : ∀ (V : S.Opens) (p : ℕ), 0 < p →
      IsZero ((RingedSpace.moduleCohomology V.toScheme.toRingedSpace p).obj
        ((restrictFunctor V.ι).obj F))) :
    ∀ V : S.Opens,
      (SheafOfModules.forget.{u} S.ringCatSheaf ⋙
        PresheafOfModules.evaluation.{u} S.ringCatSheaf.obj (op V)).rightAcyclic F := by
  let : EnoughInjectives S.Modules := inferInstance
  intro V q
  let : EnoughInjectives V.toScheme.Modules := inferInstance
  let R := restrictFunctor V.ι
  obtain ⟨hlim, hcolim, hleft, _, ⟨adj⟩⟩ :=
    open_restriction_adjunction_exact S.toRingedSpace V
  let := hlim
  let := hcolim
  let := hleft
  let : (SheafOfModules.overFunctor.{u} S.ringCatSheaf V).PreservesInjectiveObjects :=
    adj.preservesInjectiveObjects_of_preservesFiniteLimits
  let : PreservesFiniteLimits R := preservesFiniteLimits_of_natIso (overFunctorEquiv V)
  let : PreservesFiniteColimits R := preservesFiniteColimits_of_natIso (overFunctorEquiv V)
  let : R.Additive := Functor.additive_of_preserves_binary_products R
  let : R.PreservesInjectiveObjects :=
    { injective_obj := fun {I} hI ↦ by
        let := hI
        change Injective ((restrictFunctor V.ι).obj I)
        exact Injective.of_iso ((overFunctorEquiv V).app I) inferInstance }
  let I := injectiveResolution F
  let e := (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℕ) 0).app F
  let J : InjectiveResolution (R.obj F) :=
    { cocomplex := (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
      injective := fun n ↦ by
        change Injective (R.obj (I.cocomplex.X n))
        exact R.injective_obj_of_injective (I.injective n)
      ι := e.inv ≫ (R.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
      quasiIso := by infer_instance }
  let E := SheafOfModules.forget.{u} S.ringCatSheaf ⋙
    PresheafOfModules.evaluation.{u} S.ringCatSheaf.obj (op V)
  let G := RingedSpace.globalSectionsFunctor V.toScheme.toRingedSpace
  let : E.Additive := inferInstanceAs
    ((SheafOfModules.forget S.ringCatSheaf ⋙
      PresheafOfModules.evaluation S.ringCatSheaf.obj (op V)).Additive)
  let : G.Additive := RingedSpace.globalSectionsFunctor_additive _
  let U := forget₂ (ModuleCat.{u} (S.ringCatSheaf.obj.obj (op V))) AddCommGrpCat.{u}
  let W := forget₂
    (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat.{u}
  let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let L := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  let c : ((W.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) ≅
      ((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents (fun n ↦
      (I.cocomplex.X n).restrictAppIso V.ι ⊤ ≪≫
        (I.cocomplex.X n).presheaf.mapIso (eqToIso (congrArg op V.ι_image_top))) (by
          intro i j hij
          dsimp [L, K, J, R, E, G, U, W, RingedSpace.globalSectionsFunctor]
          simp only [restrictAppIso, Iso.refl_hom, Category.assoc]
          exact
            (I.cocomplex.d i j).mapPresheaf.naturality
              ((eqToIso (congrArg op V.ι_image_top)).hom))
  have hz : IsZero (L.homology (q + 1)) :=
    (hcoh V (q + 1) (Nat.zero_lt_succ q)).of_iso
      (J.isoRightDerivedObj G (q + 1)).symm
  have hz' : IsZero (((W.mapHomologicalComplex _).obj L).homology (q + 1)) :=
    (W.map_isZero hz).of_iso ((L.sc (q + 1)).mapHomologyIso W)
  have hz'' : IsZero (((U.mapHomologicalComplex _).obj K).homology (q + 1)) :=
    hz'.of_iso ((HomologicalComplex.homologyFunctor _ _ (q + 1)).mapIso c).symm
  have hzK : IsZero (K.homology (q + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mpr
      (AddCommGrpCat.isZero_iff_subsingleton.mp
        (hz''.of_iso ((K.sc (q + 1)).mapHomologyIso U).symm))
  exact hzK.of_iso (I.isoRightDerivedObj E (q + 1))

end AlgebraicGeometry.Scheme.Modules
