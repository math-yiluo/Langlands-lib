/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality

/-!
# The canonical internal-Hom completion unit

Source: Stacks Project, algebraization.tex, Tag 099F, and sites-cohomology.tex, Section 08J7
(auxiliary; not a blueprint node).

The unit uses evaluation at one, the functorial K-injective resolution, and the specified
localization factorization of derived internal Hom. No arbitrary isomorphism from Hom of
the ring sheaf is chosen.
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory Opposite

-- Limit preservation gives a small proof of the required sheaf-composition instance.
attribute [local instance 0] CategoryTheory.hasSheafCompose_of_preservesMulticospan
attribute [local instance 20000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

namespace CategoryTheory

/-- The forgetful functor preserves the sheaf condition on a small site.
Source: Mathlib, `CategoryTheory.Sites.Whiskering`.
(auxiliary; not a blueprint node).
Proof: use the existing instance; the named proof prevents repeated instance search
through the concrete sheaf category in the completion constructions. -/
theorem ringedCompletionHasSheafCompose {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := by infer_instance

attribute [local instance 20000] ringedCompletionHasSheafCompose

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

/-- The degreewise evaluation map, using the projections of the actual ring complex.
Source: Stacks Project, sites-cohomology.tex, Section 08J7.
(auxiliary; not a blueprint node). -/
def ringedHomUnitEvaluationMap (M : ringedSiteComplex O) (n : ℤ) :
    (homComplex (R := O) (ringedSiteRingComplex O) M).X n ⟶ M.X n :=
  homComplexπ (ringedSiteRingComplex O) M n 0 n (by omega) ≫
    SheafOfModules.homObjMap (R := O)
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv
      (𝟙 _) ≫ (SheafOfModules.homObjUnitIso (M.X n)).hom

/-- The projection formula is the original evaluation map, definitionally.
Source: Stacks Project, sites-cohomology.tex, Section 08J7.
(auxiliary; not a blueprint node).
Proof: both maps project to source degree zero, identify that term with the ring sheaf,
and evaluate the resulting localized module homomorphism at one. -/
theorem ringedHomUnitEvaluationMap_eq (M : ringedSiteComplex O) (n : ℤ) :
    ringedHomUnitEvaluationMap O M n = homComplexUnitEvaluation J O M n := rfl

/-- Evaluation in literal degree zero needs no change of the source basis.
Source: Stacks Project, sites-cohomology.tex, Section 08J7.
(auxiliary; not a blueprint node).
Proof: the single-complex identification at literal zero is the identity.
Precomposition by that identity is the identity internal-Hom map. -/
theorem ringedHomUnitEvaluationMap_normalized (M : ringedSiteComplex O) (n : ℤ) :
    ringedHomUnitEvaluationMap O M n =
      homComplexπ (ringedSiteRingComplex O) M n 0 n (by omega) ≫
        (SheafOfModules.homObjUnitIso (M.X n)).hom := by
  let π : (homComplex (R := O) (ringedSiteRingComplex O) M).X n ⟶
      SheafOfModules.homObj (R := O)
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
        (M.X n) := homComplexπ (ringedSiteRingComplex O) M n 0 n (by omega)
  change π ≫ SheafOfModules.homObjMap (R := O)
      (𝟙 (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)))
      (𝟙 (M.X n)) ≫ (SheafOfModules.homObjUnitIso (M.X n)).hom =
    π ≫ (SheafOfModules.homObjUnitIso (M.X n)).hom
  rw [SheafOfModules.homObjMap_id, Category.id_comp]

attribute [local irreducible] ringedHomUnitEvaluationMap

/-- The actual evaluation component is invertible.
Source: Stacks Project, sites-cohomology.tex, Section 08J7.
(auxiliary; not a blueprint node).
Proof: identify it with `homComplexUnitEvaluation` and use its proved invertibility. -/
theorem ringedHomUnitEvaluationMap_isIso (M : ringedSiteComplex O) (n : ℤ) :
    IsIso (ringedHomUnitEvaluationMap O M n) := by
  rw [ringedHomUnitEvaluationMap_eq]
  exact homComplex_unit_evaluation_isIso J O M n

/-- Evaluation at one commutes with the differential.
Source: Stacks Project, sites-cohomology.tex, Section 08J7.
(auxiliary; not a blueprint node).
Proof: identify both components with the original evaluation maps and use their chain
compatibility. -/
theorem ringedHomUnitEvaluationMap_comm (M : ringedSiteComplex O) (n m : ℤ)
    (h : (ComplexShape.up ℤ).Rel n m) :
    ringedHomUnitEvaluationMap O M n ≫ M.d n m =
      (homComplex (R := O) (ringedSiteRingComplex O) M).d n m ≫
        ringedHomUnitEvaluationMap O M m := by
  rw [ringedHomUnitEvaluationMap_eq, ringedHomUnitEvaluationMap_eq]
  exact homComplex_unit_evaluation_comm J O M n m h

/-- Evaluation at one gives the canonical chain isomorphism from Hom of the ring complex.
Source: Stacks Project, sites-cohomology.tex, Section 08J7
(auxiliary; not a blueprint node). -/
def ringedHomUnitEvaluationIso (M : ringedSiteComplex O) :
    homComplex (R := O) (ringedSiteRingComplex O) M ≅ M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ @asIso _ _ _ _ (ringedHomUnitEvaluationMap O M n)
      (ringedHomUnitEvaluationMap_isIso O M n))
    (fun n m h ↦ ringedHomUnitEvaluationMap_comm O M n m h)

section FunctorEvaluation

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- Evaluation with its source expressed by the actual Hom-complex functor.
Source: Stacks Project, sites-cohomology.tex, Section 08J7.
(auxiliary; not a blueprint node).
Proof: the Hom-complex functor uses the same product complex as `homComplex`;
this is the existing canonical evaluation isomorphism with that endpoint. -/
def ringedHomUnitFunctorEvaluationIso (M : ringedSiteComplex O) :
    ((homComplexFunctor (R := O)).obj (op (ringedSiteRingComplex O))).obj M ≅ M :=
  ringedHomUnitEvaluationIso O M

/-- The functor presentation has the original inverse, including its normalization.
Source: Stacks Project, sites-cohomology.tex, Section 08J7.
(auxiliary; not a blueprint node).
Proof: the functor presentation is defined to be the original isomorphism. -/
theorem ringedHomUnitFunctorEvaluationIso_inv_eq (M : ringedSiteComplex O) :
    (ringedHomUnitFunctorEvaluationIso O M).inv =
      (ringedHomUnitEvaluationIso O M).inv := rfl

/-- The functor presentation retains the actual evaluation component.
Source: Stacks Project, sites-cohomology.tex, Section 08J7.
(auxiliary; not a blueprint node).
Proof: the forward map of the componentwise isomorphism is its defining map. -/
theorem ringedHomUnitFunctorEvaluationIso_hom_f (M : ringedSiteComplex O) (n : ℤ) :
    (ringedHomUnitFunctorEvaluationIso O M).hom.f n =
      ringedHomUnitEvaluationMap O M n := rfl

end FunctorEvaluation

section

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] homComplexFunctor

/-- The specified component of the canonical evaluation isomorphism.
Source: Stacks Project, sites-cohomology.tex, Section 08J7.
(auxiliary; not a blueprint node).
Proof: expose the isomorphism of components; its forward map is the specified
unit evaluation, independently of the inverse used by `asIso`. -/
theorem ringedHomUnitEvaluationIso_hom_f (M : ringedSiteComplex O) (n : ℤ) :
    (ringedHomUnitEvaluationIso O M).hom.f n = homComplexUnitEvaluation J O M n := by
  exact ringedHomUnitEvaluationMap_eq O M n

/-- Unit evaluation projects to source degree zero and evaluates at one.
Source: Stacks Project, sites-cohomology.tex, Section 08J7.
(auxiliary; not a blueprint node).
Proof: expose the specified component, then the definition of unit evaluation.
The preferred single functor and the ordinary single complex have identical underlying
functors. Thus their specified projections and degree-zero identifications agree. -/
theorem ringedHomUnitEvaluationIso_hom_f_projection (M : ringedSiteComplex O) (n : ℤ) :
    (ringedHomUnitEvaluationIso O M).hom.f n =
      homComplexπ (ringedSiteRingComplex O) M n 0 n (zero_add n) ≫
        SheafOfModules.homObjMap (R := O)
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv (𝟙 _) ≫
          (SheafOfModules.homObjUnitIso (R := O) (M.X n)).hom := by
  rw [ringedHomUnitEvaluationIso_hom_f]
  rfl

/-- Canonical unit evaluation is natural in the target complex.
Source: Stacks Project, sites-cohomology.tex, Section 08J7.
(auxiliary; not a blueprint node).
Proof: compare chain maps degreewise, expose their specified evaluation components,
and apply naturality of degreewise evaluation at one. -/
theorem ringedHomUnitEvaluationIso_naturality {M N : ringedSiteComplex O} (f : M ⟶ N) :
    ((homComplexFunctor (R := O)).obj (op (ringedSiteRingComplex O))).map f ≫
        (ringedHomUnitEvaluationIso O N).hom =
      (ringedHomUnitEvaluationIso O M).hom ≫ f := by
  apply HomologicalComplex.hom_ext
  intro n
  change (((homComplexFunctor (R := O)).obj
      (op (ringedSiteRingComplex O))).map f).f n ≫
        (ringedHomUnitEvaluationIso O N).hom.f n =
      (ringedHomUnitEvaluationIso O M).hom.f n ≫ f.f n
  erw [ringedHomUnitEvaluationIso_hom_f O N n, ringedHomUnitEvaluationIso_hom_f O M n]
  exact homComplex_unit_evaluation_naturality J O f n

end

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

/-- The canonical map `E → RHom(O[0], E)`, obtained by evaluation at one and the
localization factorization of the actual internal-Hom construction.
Source: Stacks Project, algebraization.tex, Tag 099F, and sites-cohomology.tex, Section 08J7
(auxiliary; not a blueprint node). -/
def ringedDerivedHomUnit (E : ringedSiteDerived O) :
    E ⟶ (derivedInternalHom J O).obj
      (op (DerivedCategory.Q.obj (ringedSiteRingComplex O)), E) :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u}
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  let η := CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  let c := Localization.fac
    ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := O)) ⋙ DerivedCategory.Q)
    (derivedInternalHom_inverts J O I η (fun M ↦
      ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)
  let M := DerivedCategory.Q.objPreimage E
  let e := DerivedCategory.Q.objObjPreimageIso E
  e.inv ≫ DerivedCategory.Q.map (η.app M) ≫
    (DerivedCategory.Q.mapIso (ringedHomUnitEvaluationIso O (I.obj M))).inv ≫
      (c.app (op (ringedSiteRingComplex O), M)).inv ≫
        (derivedInternalHom J O).map (𝟙 _, e.hom)

/-- Internal Hom out of a fixed complex, as a functor of its second variable.
Source: Stacks Project, algebraization.tex, Tag 099F
(auxiliary; not a blueprint node). -/
def ringedCechCompletionFunctor (K : ringedSiteComplex O) :
    ringedSiteDerived O ⥤ ringedSiteDerived O :=
  (Functor.curry.obj (derivedInternalHom J O)).obj (op (DerivedCategory.Q.obj K))

/-- The canonical completion unit induced by the augmentation, contravariantly in the
first argument of derived internal Hom.
Source: Stacks Project, algebraization.tex, Tag 099F
(auxiliary; not a blueprint node). -/
def ringedCechCompletionUnit (K : ringedSiteComplex O)
    (ε : K ⟶ ringedSiteRingComplex O) (E : ringedSiteDerived O) :
    E ⟶ (ringedCechCompletionFunctor O K).obj E :=
  ringedDerivedHomUnit O E ≫
    (derivedInternalHom J O).map ((DerivedCategory.Q.map ε).op, 𝟙 E)

end CategoryTheory
