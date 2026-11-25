/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import WeilConjectures.AlgebraicGeometry.DerivedStructureEvaluationOne
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.AlgebraicGeometry.OpenSectionsCohomologyModel
import WeilConjectures.AlgebraicGeometry.OpenSectionsStructureClass

/-! # Comparing derived sections on an open with ambient open sections

Source: Stacks Project, Tags 08BS, 079V and 06Z0.
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
noncomputable section

/-- The canonical restriction isomorphism for the extended structure complex.
Source: Stacks Project, Tag 08CX, the structure complex; Tag 06Z0, tilde of A.
(blueprint: lem-sc-open-sections-cohomology-unit-comparison).

Construction: Extend the single complex using `extendSingleIso`, apply tilde
and `singleMapHomologicalComplex`, then use the definitional identification
of tilde(A) with the structure module. Apply derived restriction, its
single-functor comparison and `sheafOfModulesEquivOverUnit`. -/
def openStructureRestrictionIso
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
    R.obj (koszulOpenStructure A) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings U.toScheme.toRingedSpace)) := by
  let C := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let C' := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  let T := koszulOpenTilde A
  let F := (SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
      (D := C') (Scheme.Modules.overEquiv U)
  let K := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
  let e : K.extend ComplexShape.embeddingDownNat ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) :=
    HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (ModuleCat.of A A) 0 0 rfl
  let t : ((T.mapHomologicalComplex (.up ℤ)).obj
      (K.extend ComplexShape.embeddingDownNat)) ≅
      (CochainComplex.singleFunctor C 0).obj (SheafOfModules.unit
        (moduleRings (Spec (.of A)).toRingedSpace)) :=
    (T.mapHomologicalComplex (.up ℤ)).mapIso e ≪≫
      (HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0).app (ModuleCat.of A A)
  let f : F.obj (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)) ≅
      SheafOfModules.unit (moduleRings U.toScheme.toRingedSpace) :=
    TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U _
  exact F.mapDerivedCategory.mapIso (DerivedCategory.Q.mapIso t) ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor C' 0).mapIso f


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction and exact scalar restriction compare the two sections computations,
including their canonical classes of one. This statement compares cohomology only;
it contains no equivalence of derived Hom sets.
Source: Stacks Project, Tag 08BS, preservation of K-injectives under open restriction;
Tag 079V, derived global sections; Tag 06Z0, the tilde/sections adjunction.
(blueprint: lem-sc-open-sections-cohomology-unit-comparison).

Proof: Identify the extended A[0] with the integer single complex, apply tilde,
and use tildeSelf to identify its degree-zero sheaf with the structure module.
Restriction and the over-equivalence take that module to the structure module
on U. These explicit complex isomorphisms give i. For an ambient K-injective
resolution J, open restriction preserves K-injectivity by its exact left
adjoint extension by zero (Tag 08BS). The over-equivalence preserves it too.
The sections of the restricted complex on all of U are the sections of J on U.
Restrict scalars along A → Γ(U,O_U); this is exact, so commutes with homology.
Both right-derived units are isomorphisms on these representatives. Compose
these units, the sections identification and the homology factorization isos
to obtain c. The constructions commute with chain maps. Full faithfulness on
K-injectives descends this compatibility to all ambient derived morphisms.
For the last equality, the source isomorphism takes the restricted structure
identity to the identity of O_U[0]. Before resolution its global class of one
is the restriction of 1 in A, namely tilde.toOpen applied to the degree-zero
class determined by extendHomologyIso and singleObjHomologySelfIso. Naturality
of both derived units with the ambient resolution map transports exactly this
class to the displayed right hand side. This proves compatibility with the
specified construction, not just with an unspecified generator. Empty U and
the zero ring give zero modules on both sides. No quasi-coherence is used. -/
theorem openSections_cohomology_unit_comparison
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
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} ((moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)))
    let F := (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤))) 0 ⋙
      forget₂ (ModuleCat.{u} ((moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)))
        AddCommGrpCat
    let O := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings U.toScheme.toRingedSpace))
    let K := (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)
    let L := K.extend ComplexShape.embeddingDownNat
    let C := ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj L
    let S := ((affineOpenSections A U).mapHomologicalComplex (.up ℤ)).obj C
    let η₀ : 𝟭 (ModuleCat.{u} A) ⟶ koszulOpenTilde A ⋙ affineOpenSections A U :=
      { app := fun M ↦ tilde.toOpen M U
        naturality := fun _ _ g ↦ (tilde.toOpen_map_app g U).symm }
    let η := (NatTrans.mapHomologicalComplex η₀ (.up ℤ)).app L
    let j : L.homology 0 ≅ ModuleCat.of A A :=
      K.extendHomologyIso ComplexShape.embeddingDownNat (j := 0) rfl ≪≫
        HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0 (ModuleCat.of A A)
    let Sh := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
    let β : (affineOpenSections A U).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ G :=
      (Functor.isoWhiskerLeft ((affineOpenSections A U).mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A))).inv ≫
      Functor.whiskerLeft (HomotopyCategory.quotient Sh (.up ℤ))
        (affineOpenSections A U).rightDerivedFunctorUnit ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso Sh) G).hom
    let i : R.obj (koszulOpenStructure A) ≅ O := openStructureRestrictionIso A U
    ∃ c : ∀ E : schemeDerivedCategory (Spec (.of A)),
        F.obj (R.obj E) ≃ H.obj (G.obj E),
        (∀ (E E' : schemeDerivedCategory (Spec (.of A))) (g : E ⟶ E')
          (z : F.obj (R.obj E)),
          c E' (F.map (R.map g) z) = H.map (G.map g) (c E z)) ∧
        c (koszulOpenStructure A) (F.map i.inv (derivedStructureGlobalOne U.toScheme)) =
          H.map (β.app C)
            (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app S).inv
              ((HomologicalComplex.homologyMap η 0) (j.inv (1 : A)))) := by
  intro R H G F O K L C S η₀ η j Sh β i
  obtain ⟨e, he⟩ := exists_openComparison_cohomology_model_iso A U
  let c (E : schemeDerivedCategory (Spec (.of A))) :=
    Equiv.ofBijective (e.hom.app E) (ConcreteCategory.bijective_of_isIso (e.hom.app E))
  refine ⟨c, ?_, ?_⟩
  · intro E E' g z
    exact CategoryTheory.congr_fun (e.hom.naturality g) z
  · let x : openComparisonOrdinaryCohomology A U C :=
      (HomologicalComplex.homologyMap η 0) (j.inv (1 : A))
    have hclass : F.map i.inv (derivedStructureGlobalOne U.toScheme) =
        openComparisonRestrictedUnit A U C x := openComparison_structure_class A U
    have hmodel := CategoryTheory.congr_fun (he C) x
    have hambient : openComparisonAmbientUnit A U C x =
        H.map (β.app C)
          (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) 0).app S).inv x) := rfl
    change (e.hom.app (koszulOpenStructure A)) _ = _
    exact (congrArg (fun z ↦ e.hom.app (koszulOpenStructure A) z) hclass).trans
      (hmodel.trans hambient)


end
end AlgebraicGeometry
