/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorLocalizedNaturality
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionLinear
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.AlgebraicGeometry.StalkDerivedExtensionComparisonIso

/-! # Derived scalar extension and the stalk of derived pullback

Source: Stacks Project, Cohomology, Tags 06YB and 0D5S; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-stalk-derived-extension-comparison).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section



namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem homology_comparison
    {D : Type u} [CommRing D] [HasDerivedCategory.{w} (ModuleCat.{u} D)]
    {M N : CochainComplex (ModuleCat.{u} D) ℤ}
    {U V W : DerivedCategory (ModuleCat.{u} D)}
    (s : U ≅ DerivedCategory.Q.obj M) (k : V ≅ DerivedCategory.Q.obj N)
    (t : M ≅ N) (v : V ⟶ W) (i : ℤ) :
    ((DerivedCategory.homologyFunctor _ i).mapIso s ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app M).inv ≫
        (DerivedCategory.homologyFunctor _ i).map
          (s.hom ≫ DerivedCategory.Q.map t.hom ≫ k.inv ≫ v) =
      HomologicalComplex.homologyMap t.hom i ≫
        ((DerivedCategory.homologyFunctor _ i).mapIso k ≪≫
          (DerivedCategory.homologyFunctorFactors _ i).app N).inv ≫
        (DerivedCategory.homologyFunctor _ i).map v := by
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, s.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg (fun h ↦ h ≫ (DerivedCategory.homologyFunctor _ i).map k.inv ≫
    (DerivedCategory.homologyFunctor _ i).map v)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} D) i).inv.naturality t.hom).symm

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

set_option linter.unusedVariables false in
/-- Derived extension of the original stalk identifies naturally with the stalk of
sheaf derived pullback. The computation on K-flat complexes uses precisely the
specified tensor-stalk isomorphism and the two universal counits.

Proof: derive extension along the actual stalk map A -> C using K-flat resolutions
of A-modules. The K-flat stalk criterion says that stalks of K-flat sheaf complexes
are K-flat A-complexes. Their ordinary scalar extensions therefore compute this
left-derived functor, with invertible universal counits. The natural pullback-stalk
isomorphism identifies their ordinary scalar extensions with stalks of ordinary
sheaf pullback. Its degreewise components are those specifying tensorStalkIso.
Both sides preserve quasi-isomorphisms on these resolving objects. Localize this
natural identification and its inverse on K-flat representatives to obtain the
natural isomorphism j. The two inverse identities descend from the identities on
complexes. Compatibility with the localization factors and universal counits gives
the displayed equation after taking homology; scalarExtensionHomologyIso contains
exactly the scalar-extension counit and its localization factors. Exactness of
stalks gives comparisonStalkHomologyIso on the sheaf side. No base-flatness or
invertibility of the base-derived cohomology comparison is involved.
Source: Stacks Project, Cohomology, Tags 06YB and 0D5S; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-stalk-derived-extension-comparison). -/
theorem exists_stalkDerivedExtensionComparison (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (C z))
    ∃ (L : DerivedCategory (ModuleCat.{u} (A g' z)) ⥤
          DerivedCategory (ModuleCat.{u} (C z)))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        (ModuleCat.extendScalars.{u, u, u}
          ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
            (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))).mapHomotopyCategory
              (.up ℤ) ⋙ DerivedCategory.Qh),
      L.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (ModuleCat.{u} (A g' z)) (.up ℤ)) ∧
      ∃ j : comparisonDerivedStalk X (g' z) ⋙ L ≅
          derivedPullback g' ⋙ comparisonDerivedStalk X' z,
        ∀ (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
          (hP : P.IsKFlatTensor)
          (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))),
          ∃ hsP : IsIso (ε.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj (stalkComplex g' z P))),
            ∀ i : ℤ,
              (ModuleCat.scalarExtensionHomologyIso (A := A g' z) (D := C z)
                _ L ε (stalkComplex g' z P) hsP i).inv ≫
                (DerivedCategory.homologyFunctor _ i).map
                  (L.map ((RingedSpace.moduleStalkFunctor X.toRingedSpace
                    (g' z)).mapDerivedCategoryFactors.inv.app P) ≫
                      j.hom.app (DerivedCategory.Q.obj P)) =
              HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i ≫
                (comparisonStalkHomologyIso X' z
                  (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
                    i).inv ≫
                (comparisonStalkCohomology X' z i).map
                  (cast (by rfl)
                    (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (C z))
  let ρ := (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
    (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))
  let : Algebra (A g' z) (C z) := ρ.toAlgebra
  obtain ⟨L, ε, hL, _hadd, _hscalar⟩ :=
    ModuleCat.exists_baseDerivedExtension_linear (A g' z) (C z)
  refine ⟨L, ε, hL, ?_⟩
  obtain ⟨j, hj⟩ := exists_stalkDerivedExtensionComparisonIso f f' g g' sq z L ε hL
  refine ⟨j, ?_⟩
  intro P hP hcP
  have hsP := ModuleCat.scalarExtensionCounit_isIso_of_kFlat ρ (stalkComplex g' z P)
    ((RingedSpace.isKFlat_iff_stalk_isKFlat X.toRingedSpace P).mp hP (g' z)) L ε hL
  refine ⟨hsP, ?_⟩
  intro i
  let := hsP
  let E := ModuleCat.extendScalars.{u, u, u} ρ
  let s := L.mapIso ((DerivedCategory.quotientCompQhIso _).symm.app
      (stalkComplex g' z P)) ≪≫
    asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (stalkComplex g' z P))) ≪≫
    DerivedCategory.Qh.mapIso ((E.mapHomotopyCategoryFactors (.up ℤ)).app
      (stalkComplex g' z P)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app (tensorComplex f f' g g' sq z P)
  let k := (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapDerivedCategoryFactors.app
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
  rw [hj P hP hcP]
  convert homology_comparison s k (tensorStalkIso f f' g g' sq z P)
    ((comparisonDerivedStalk X' z).map
      (cast (by rfl)
        (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))))) i using 1 <;>
    simp only [s, k, E, ρ, tensorComplex, RingHom.algebraMap_toAlgebra,
      Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
      ModuleCat.scalarExtensionHomologyIso,
      comparisonStalkHomologyIso, comparisonStalkCohomology, Functor.comp_map,
      Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom,
      asIso_hom, Category.assoc]
  rfl


end AlgebraicGeometry.SingleComplexBaseChange
