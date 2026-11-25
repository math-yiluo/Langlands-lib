/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.OpenSectionsCohomologyComparison

/-! # The canonical unit in derived open sections

Source: Stacks Project, Tag 09M1, evaluation at one.
(blueprint: lem-sc-derived-open-structure-sections-unit).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
noncomputable section

/-- The ordinary tilde-to-open-sections unit.
Source: Stacks Project, Tag 06Z0, tilde and sections adjunction.
(blueprint: lem-sc-derived-open-structure-sections-unit). -/
def affineOpenTildeSectionsUnit (A : Type u) [CommRing A]
    (U : (Spec (.of A)).Opens) :
    𝟭 (ModuleCat.{u} A) ⟶ koszulOpenTilde A ⋙ affineOpenSections A U where
  app M := tilde.toOpen M U
  naturality _ _ g := (tilde.toOpen_map_app g U).symm

/-- The natural comparison from ordinary sections of complexes to derived sections.
Source: Stacks Project, Tag 09M1, K-injective computation of derived sections.
(blueprint: lem-sc-derived-open-structure-sections-unit). -/
def affineOpenSectionsDerivedUnit (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (U : (Spec (.of A)).Opens) :
    (affineOpenSections A U).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (affineOpenSections A U).rightDerivedFunctor :=
  let Sh := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let S := affineOpenSections A U
  (Functor.isoWhiskerLeft (S.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A))).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient Sh (.up ℤ))
      S.rightDerivedFunctorUnit ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso Sh)
      S.rightDerivedFunctor).hom

/-- Component of the natural ordinary-to-derived sections comparison.
Source: Stacks Project, Tag 09M1, K-injective computation of derived sections.
(blueprint: lem-sc-derived-open-structure-sections-unit). -/
def affineOpenSectionsToDerived (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (U : (Spec (.of A)).Opens)
    (C : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj (((affineOpenSections A U).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (affineOpenSections A U).rightDerivedFunctor.obj (DerivedCategory.Q.obj C) :=
  (affineOpenSectionsDerivedUnit A U).app C

/-- The extended single free rank-one module complex used for the structure object.
Source: Stacks Project, Tag 08CX, the structure complex A[0].
(blueprint: lem-sc-derived-open-structure-sections-unit). -/
def openStructureModuleComplex (A : Type u) [CommRing A] :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  ((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)).extend
    ComplexShape.embeddingDownNat

/-- The concrete sheaf complex representing the structure object.
Source: Stacks Project, Tag 08CX, tilde of A[0].
(blueprint: lem-sc-derived-open-structure-sections-unit). -/
def openStructureSheafComplex (A : Type u) [CommRing A] :
    CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ :=
  ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj (openStructureModuleComplex A)

/-- The ordinary open-sections homology class of one.
Source: Stacks Project, Tag 09M1, evaluation at one.
(blueprint: lem-sc-derived-open-structure-sections-unit). -/
def openStructureUnitClass (A : Type u) [CommRing A]
    (U : (Spec (.of A)).Opens) :
    (((affineOpenSections A U).mapHomologicalComplex (.up ℤ)).obj
      (openStructureSheafComplex A)).homology 0 := by
  let K := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
  let L := openStructureModuleComplex A
  let C := openStructureSheafComplex A
  let S := ((affineOpenSections A U).mapHomologicalComplex (.up ℤ)).obj C
  let η : L ⟶ S :=
    (NatTrans.mapHomologicalComplex (affineOpenTildeSectionsUnit A U) (.up ℤ)).app L
  let j : L.homology 0 ≅ ModuleCat.of A A :=
    K.extendHomologyIso ComplexShape.embeddingDownNat (j := 0) rfl ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0 (ModuleCat.of A A)
  exact (HomologicalComplex.homologyMap η 0) (j.inv (1 : A))

/-- Restriction of one, mapped through the ordinary-to-derived sections comparison.
This is a real construction, independent of any Koszul exponent or chosen equivalence.
Source: Stacks Project, Tag 09M1, evaluation at one.
(blueprint: lem-sc-derived-open-structure-sections-unit). -/
def derivedOpenStructureUnit (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (U : (Spec (.of A)).Opens) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((affineOpenSections A U).rightDerivedFunctor.obj (koszulOpenStructure A)) :=
  let C := openStructureSheafComplex A
  let S := ((affineOpenSections A U).mapHomologicalComplex (.up ℤ)).obj C
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  H.map (affineOpenSectionsToDerived A U C)
    (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app S).inv
      (openStructureUnitClass A U))

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation on a general open, with its ordinary sections unit normalization.
Source: Stacks Project, Tag 09M1, first paragraph, specialized to the structure
sheaf; Tag 06Z0, the sections adjunction and its unit.
(blueprint: lem-sc-derived-open-structure-sections-unit).

Proof: Identify the restricted tilde of A[0] with O_U[0]. Compute derived
sections on a K-injective representative J of the restricted object. Maps from
O_U[0] to J are degree-zero global cycles, and homotopies are boundaries, by
sending a module map to its value at one. Thus their homotopy classes are H^0
of sections. Restriction to an open preserves K-injectives: its exact left
adjoint is extension by zero. The over-equivalence also preserves them. Hence
restricting an ambient K-injective resolution computes derived sections on U.
Restriction of scalars along A to Gamma(U,O_U) is exact and commutes with
homology; it identifies this computation with affineOpenSections A U in the
chosen module derived category, including its localization comparison isos.
This gives the structure-sheaf Hom/hypercohomology identification by its
explicit cycle construction, retaining evaluation at one for the normalization.
Transport that construction through these comparisons. All maps are natural in
a chain map and descend to
derived arrows via K-injective representatives, giving the displayed family
and postcomposition law. For the structure identity, evaluation is restriction
of one. Before resolution this is the degree-zero class of the termwise
map tilde.toOpen, applied to the class of 1 in the extended single complex.
The derived-functor unit sends it to precisely derivedOpenStructureUnit.
Naturality of that unit with the resolution map proves the last equality.
For the empty open both Hom and sections vanish; the same construction works
for the zero ring. No quasi-coherence or boundedness of E is required. -/
theorem derivedOpenStructure_evaluation_unit
    (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)] :
    let R := ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
    let G := (affineOpenSections A U).rightDerivedFunctor
    ∃ b : ∀ E : schemeDerivedCategory (Spec (.of A)),
      (R.obj (koszulOpenStructure A) ⟶ R.obj E) ≃ H.obj (G.obj E),
      (∀ (E E' : schemeDerivedCategory (Spec (.of A))) (g : E ⟶ E')
        (ψ : R.obj (koszulOpenStructure A) ⟶ R.obj E),
        b E' (ψ ≫ R.map g) = H.map (G.map g) (b E ψ)) ∧
      b (koszulOpenStructure A) (𝟙 _) = derivedOpenStructureUnit A U := by
  classical
  let R := ((SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let G := (affineOpenSections A U).rightDerivedFunctor
  let := HasDerivedCategory.standard
    (ModuleCat.{u} ((moduleRings U.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
  let F := (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((moduleRings U.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤))) 0 ⋙
    forget₂ (ModuleCat.{u} ((moduleRings U.toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
      AddCommGrpCat
  let i := openStructureRestrictionIso A U
  obtain ⟨c, hc, hunit⟩ := openSections_cohomology_unit_comparison A U
  let a (E : schemeDerivedCategory (Spec (.of A))) :=
    Equiv.ofBijective (fun f ↦ F.map f (derivedStructureGlobalOne U.toScheme))
      (derivedStructure_evaluation_one_bijective U.toScheme (R.obj E))
  let b (E : schemeDerivedCategory (Spec (.of A))) :=
    (Iso.homCongr i (Iso.refl (R.obj E))).trans ((a E).trans (c E))
  refine ⟨b, ?_, ?_⟩
  · intro E E' g ψ
    have hn := hc E E' g (F.map (i.inv ≫ ψ) (derivedStructureGlobalOne U.toScheme))
    convert hn using 1
    all_goals simp only [b, a, F, Equiv.trans_apply, Iso.homCongr, Equiv.ofBijective_apply,
      Equiv.coe_fn_mk,
      Iso.refl_hom, Category.comp_id, Functor.map_comp,
      Functor.comp_map, CategoryTheory.comp_apply]
    all_goals rfl
  · convert hunit using 1
    all_goals simp only [b, a, F, Equiv.trans_apply, Iso.homCongr, Equiv.ofBijective_apply,
      Equiv.coe_fn_mk,
      Iso.refl_hom, Category.comp_id, derivedOpenStructureUnit,
      affineOpenSectionsToDerived, affineOpenSectionsDerivedUnit, openStructureUnitClass,
      openStructureSheafComplex, openStructureModuleComplex, affineOpenTildeSectionsUnit,
      Functor.comp_map]
    all_goals rfl

end
end AlgebraicGeometry
