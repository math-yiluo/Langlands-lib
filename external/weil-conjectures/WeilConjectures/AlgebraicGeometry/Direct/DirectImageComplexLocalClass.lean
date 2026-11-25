/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareLocalClassModels
import WeilConjectures.AlgebraicGeometry.Direct.DirectImageIntegerLocalClass
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NonnegativeComplexLocalClass

/-! # Local classes computed on an arbitrary nonnegative K-injective complex

Source: Stacks Project, Cohomology, Tag 01E4, lemma-describe-higher-direct-images,
and Tags 0BKJ and 0D5X.
(blueprint: lem-weil-pbc-direct-image-complex-local-class).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorOfQuasiIsoResolutions
  AlgebraicGeometry.RingedSpace.topEdgeLocalClass
  AlgebraicGeometry.RingedSpace.topEdgeLocalLeray
namespace AlgebraicGeometry
open Scheme.Modules
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The class map of a nonnegative complex agrees with the derived local-class map,
when its integer extension is K-injective. The input is an arbitrary derived object
identified with that extension. There is no classical right-derived functor, coefficient
object, injective-resolution augmentation, or restricted-resolution choice in this statement.
Source: Stacks Project, Cohomology, Tag 01E4, lemma-describe-higher-direct-images
(the bounded-below-complex assertion), and Tags 0BKJ and 0D5X.
(blueprint: lem-weil-pbc-direct-image-complex-local-class).

Proof: First take K = Q(L extended by zero) and r the identity. Compute the inverse-open
presheaf by applying the section functor to that K-injective complex; this is b. The
unit equation defining localLerayComparison identifies the local derived sections of
Rf_*K with that same complex. Its comparison with the published direct image is
normalized by the inverse of the direct-image derived unit. Consequently the induced
cohomology-sheaf comparison is d. For the local class map, use the normalization of
localHypercohomologySheafificationAt on K-injective representatives and its naturality.
The abelian and module sheafification units have the same underlying map, by the
sheafification adjunctions after forgetting scalars. Commute their exact functors with
homology and use the counits: both maps take a cycle to its class in the cohomology
sheaf. Extension by zero commutes with these cycle and boundary quotients; the explicit
extendHomologyIso and mapExtendIso are exactly the factors in a and d. Evaluation is
exact and gives the displayed mapHomologyIso on the left and at the end of a. This
proves the equality on every open. For arbitrary K and r, transport this computation by
naturality of the local derived-section functors, the Leray comparison and the
sheafification unit. All intermediate isomorphisms cancel, leaving the stated b and d.
The argument includes degree zero, empty opens, and the zero complex. -/
theorem directImageComplex_localClass {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℕ)
    [CochainComplex.IsKInjective (L.extend ComplexShape.embeddingUpNat)]
    (K : schemeDerivedCategory X)
    (r : K ≅ DerivedCategory.Q.obj (L.extend ComplexShape.embeddingUpNat))
    (q : ℕ) (V : Y.Opens) :
    let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    letI : D.Additive := RingedSpace.moduleDirectImage_additive f.toLRSHom.toShHom
    let P := D ⋙ RingedSpace.localAbelianSections Y.toRingedSpace
    letI : P.Additive := inferInstanceAs
      (D ⋙ RingedSpace.localAbelianSections Y.toRingedSpace).Additive
    let E := (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
    let Γ := P ⋙ E
    letI : Γ.Additive := inferInstanceAs (P ⋙ E).Additive
    let B := (D.mapHomologicalComplex (ComplexShape.up ℕ)).obj L
    let a :=
      (((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).extendHomologyIso
        ComplexShape.embeddingUpNat (j := q) rfl).symm ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
        (q : ℤ)).mapIso (L.mapExtendIso ComplexShape.embeddingUpNat Γ).symm ≪≫
      (((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (L.extend ComplexShape.embeddingUpNat)).sc (q : ℤ)).mapHomologyIso E
    let b :=
      (RingedSpace.inverseOpenHypercohomologyPresheaf f.toLRSHom.toShHom
        (q : ℤ)).mapIso r ≪≫
      (DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
        (P.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
          (RingedSpace.localSectionsEnoughKInjectives X.toRingedSpace)
            (𝟙 (L.extend ComplexShape.embeddingUpNat))) ≪≫
      (DerivedCategory.homologyFunctorFactors _ (q : ℤ)).app _
    let d :=
      (DerivedCategory.homologyFunctor.{w, u, u + 1}
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (q : ℤ)).mapIso
        (D.rightDerivedFunctor.mapIso r ≪≫
          D.rightDerivedFunctorObjQIso (L.extend ComplexShape.embeddingUpNat)) ≪≫
      (DerivedCategory.homologyFunctorFactors.{w, u, u + 1}
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (q : ℤ)).app _ ≪≫
      (HomologicalComplex.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) (q : ℤ)).mapIso
        (L.mapExtendIso ComplexShape.embeddingUpNat D) ≪≫
      B.extendHomologyIso ComplexShape.embeddingUpNat (j := q) rfl
    (((((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj B).sc q).mapHomologyIso
        (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙ E)).hom ≫
        ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
          (sectionCohomologyTheta B q)).app (op V) =
      (a ≪≫ E.mapIso b.symm ≪≫ E.mapIso
        (RingedSpace.topEdgeLocalLeray f.toLRSHom.toShHom (q : ℤ) K).symm).hom ≫
        (RingedSpace.topEdgeLocalClass Y.toRingedSpace (q : ℤ)
          ((schemeDerivedDirectImage f).obj K)).app (op V) ≫
        ((RingedSpace.localAbelianSections Y.toRingedSpace).map d.hom).app (op V) := by
  dsimp only
  let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let : D.Additive := RingedSpace.moduleDirectImage_additive f.toLRSHom.toShHom
  let F := RingedSpace.localAbelianSections Y.toRingedSpace
  let P := D ⋙ F
  let E := (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let Γ := P ⋙ E
  let B := (D.mapHomologicalComplex (ComplexShape.up ℕ)).obj L
  let a :=
    (((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).extendHomologyIso
      ComplexShape.embeddingUpNat (j := q) rfl).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
      (q : ℤ)).mapIso (L.mapExtendIso ComplexShape.embeddingUpNat Γ).symm ≪≫
    (((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (L.extend ComplexShape.embeddingUpNat)).sc (q : ℤ)).mapHomologyIso E
  let d :=
    (HomologicalComplex.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) (q : ℤ)).mapIso
      (L.mapExtendIso ComplexShape.embeddingUpNat D) ≪≫
    B.extendHomologyIso ComplexShape.embeddingUpNat (j := q) rfl
  have hi := directImage_integer_localClass f.toLRSHom.toShHom
    (L.extend ComplexShape.embeddingUpNat) K r (q : ℤ)
  have ho := nonnegativeComplex_localClass D L q V
  dsimp only at hi ho
  erw [ho]
  have h := congrArg (fun z ↦ a.hom ≫ z ≫ (F.map d.hom).app (op V))
    (NatTrans.congr_app hi (op V))
  simpa only [a, d, F, P, Γ, E, B, D, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, NatTrans.comp_app, evaluation_obj_map,
    Category.assoc] using h.symm

end AlgebraicGeometry
