/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.TensorPullbackKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs

/-! Natural comparison transformation for the derived stalk extension.
(blueprint: lem-pc-stalk-derived-extension-comparison-core) -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem mapped_iso_left_normalization
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U V : C} {A B Z Y : D} (s : U ≅ V) (c : A ≅ B)
    (j : F.obj U ⟶ A) (ε : F.obj V ⟶ Z) (t : Z ⟶ Y) (k : Y ⟶ B)
    (hj : j ≫ c.hom = F.map s.hom ≫ ε ≫ t ≫ k) :
    F.map s.inv ≫ j = ε ≫ t ≫ k ≫ c.inv := by
  apply (cancel_mono c.hom).mp
  simp only [Category.assoc, c.inv_hom_id, Category.comp_id]
  rw [hj, ← F.map_comp_assoc, s.inv_hom_id, F.map_id, Category.id_comp]

private theorem extendScalars_transport_naturality
    {R₀ S₀ : Type u} [CommRing R₀] [CommRing S₀]
    {a b : R₀ →+* S₀} (h : a = b) {M N : ModuleCat.{u} R₀} (s : M ⟶ N) :
    (ModuleCat.extendScalars.{u, u, u} a).map s ≫
        eqToHom (congrArg (fun r ↦ (ModuleCat.extendScalars.{u, u, u} r).obj N) h) =
      eqToHom (congrArg (fun r ↦ (ModuleCat.extendScalars.{u, u, u} r).obj M) h) ≫
        (ModuleCat.extendScalars.{u, u, u} b).map s := by
  subst b
  simp


variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

private theorem tensorStalkIso_naturality (z : X')
    {P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ}
    (a : P ⟶ Q) :
    let := leftAlgebra f g' z
    let := rightAlgebra f f' g g' sq z
    let E := ModuleCat.extendScalars.{u, u, u}
      ((tensorMap f f' g g' sq z).comp
        (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))
    (E.mapHomologicalComplex (.up ℤ)).map
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (g' z)).mapHomologicalComplex (.up ℤ)).map a) ≫
        (tensorStalkIso f f' g g' sq z Q).hom =
      (tensorStalkIso f f' g g' sq z P).hom ≫
        ((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
          (.up ℤ)).map
            (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).map a) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  erw [Classical.choose_spec (exists_tensorStalkIso f f' g g' sq z Q) i,
    Classical.choose_spec (exists_tensorStalkIso f f' g g' sq z P) i]
  erw [← Category.assoc, extendScalars_transport_naturality
      (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).1,
    Category.assoc]
  exact congrArg (fun k ↦ _ ≫ k)
    ((Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)).inv.naturality
      (a.f i))

private theorem derivedPullback_stalk_isLeftDerivedFunctor (z : X') :
    (derivedPullback g' ⋙ comparisonDerivedStalk X' z).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh (derivedPullback g')
        (comparisonDerivedStalk X' z)).inv ≫
        Functor.whiskerRight (counit g') (comparisonDerivedStalk X' z))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) := by
  let A₀ := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let B₀ := SheafOfModules.{u} (moduleRings X'.toRingedSpace)
  let W := HomotopyCategory.quasiIso A₀ (.up ℤ)
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let : MonoidalCategory A₀ := SheafOfModules.monoidalCategory X.sheaf
  let : SymmetricCategory A₀ := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive A₀ := Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed A₀ := Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : HasColimitsOfSize.{0, 0} A₀ :=
    hasColimitsOfSizeShrink.{0, 0, u, u} A₀
  have : Abelian.HasFunctorialFlatResolution A₀ := schemeModule_hasFunctorialFlatResolution X
  have : IsGrothendieckAbelian.{u} A₀ :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have (M N : GradedObject ℤ A₀) : M.HasTensor N := inferInstance
  have (M N K : GradedObject ℤ A₀) : GradedObject.HasGoodTensor₁₂Tensor M N K :=
    inferInstance
  have (M N K : GradedObject ℤ A₀) : GradedObject.HasGoodTensorTensor₂₃ M N K :=
    inferInstance
  have (M N K T : GradedObject ℤ A₀) : GradedObject.HasTensor₄ObjExt M N K T :=
    inferInstance
  let : MonoidalCategory (CochainComplex A₀ ℤ) :=
    HomologicalComplex.monoidalCategory A₀ (.up ℤ)
  have : HasColimitsOfShape ℤ A₀ := inferInstance
  have : HasExactColimitsOfShape ℤ A₀ := inferInstance
  have (M : A₀) :
      PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A₀).obj M) := inferInstance
  have (M : A₀) :
      PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A₀).flip.obj M) := inferInstance
  have (j : ℤ) : HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j})) A₀ := inferInstance
  have : IsIdempotentComplete A₀ := inferInstance
  have : (ObjectProperty.flat (A := A₀)).IsStableUnderRetracts := inferInstance
  have : IsIdempotentComplete (ObjectProperty.flat (A := A₀)).FullSubcategory := inferInstance
  have : W.localizerMorphismKFlat.IsLeftDerivabilityStructure := by
    let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ A₀) := Classical.arbitrary _
    exact Λ.reduced.homotopyCategory_kFlat_isLeftDerivabilityStructure
      ObjectProperty.flat.essImage_ι_le
  let G : A₀ ⥤ B₀ := Scheme.Modules.tensorPullback g'
  have : G.Additive := tensorPullbackAdditive.{u, w} g'
  have : (derivedPullback g').IsLeftDerivedFunctor (counit g') W :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) g'
  have : G.PreservesKFlatQuasiIso := by
    refine ⟨?_⟩
    intro P Q hP hQ s hs
    have toIsKFlat (P : CochainComplex A₀ ℤ)
        (hP : (HomologicalComplex.quasiIso A₀ (.up ℤ)).kFlat P) :
        CochainComplex.IsKFlatTensor (R := X.sheaf) P := by
      intro F hF
      have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
        ((HomotopyCategory.quotient A₀ (.up ℤ)).obj P)).mp
          ((HomotopyCategory.kFlat_quotient_obj_iff P).mpr hP)
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
        (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).mpr hF)).2
    exact tensorPullback_quasiIso_of_isKFlat g' s (toIsKFlat P hP) (toIsKFlat Q hQ) hs
  exact W.localizerMorphismKFlat
    |>.isLeftDerivedFunctor_comp_of_isLeftDerivabilityStructure (counit g')
      (fun P ↦ G.derives_kFlat.isIso_of_isLeftDerivedFunctor (counit g') P)
      (comparisonDerivedStalk X' z)

-- Keep the original named proof binders, even though they do not occur in the conclusion.
set_option linter.unusedVariables false in
set_option synthInstance.maxSize 2048 in
/-- A natural comparison with the specified K-flat representative equation, without an
invertibility assertion.

Proof: identify the composite stalk ring map with the actual stalk map of g'.
On K-flat sheaf complexes use the scalar-extension counit, the Q/Qh factors,
the specified tensorStalkIso, the inverse exact-stalk factor and the inverse
pullback counit in the displayed order. Exact stalks preserve quasi-isomorphisms,
and their K-flatness follows from the stalk criterion. Naturality of the counits
and the degreewise pullback-stalk identification gives naturality for chain maps
between K-flat representatives. Every derived arrow is represented by a roof;
replace its middle complex by a K-flat resolution. Common refinements show the
induced maps are independent of the roof and resolution. They therefore descend
to a natural transformation on derived categories. For a K-flat P with invertible
pullback counit use P itself as its resolution; the construction is precisely the
stated equation. Invertibility of this transformation is a separate argument.
Source: Stacks Project, perfect.tex, equation-bc before Tag 0DJ8 (Tag 0DJ7);
Cohomology, Tags 06YB and 0D5S; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-stalk-derived-extension-comparison-core). -/
theorem exists_stalkDerivedExtensionComparisonTransformation (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (C z))
    ∀ (L : DerivedCategory (ModuleCat.{u} (A g' z)) ⥤
      DerivedCategory (ModuleCat.{u} (C z)))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        (ModuleCat.extendScalars.{u, u, u}
          ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
            (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))).mapHomotopyCategory
              (.up ℤ) ⋙ DerivedCategory.Qh)
      (hL : L.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (ModuleCat.{u} (A g' z)) (.up ℤ))),
    ∃ j : comparisonDerivedStalk X (g' z) ⋙ L ⟶
        derivedPullback g' ⋙ comparisonDerivedStalk X' z,
      ∀ (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (hP : P.IsKFlatTensor)
        (hcP : IsIso ((counit g').app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))),
        L.map ((RingedSpace.moduleStalkFunctor X.toRingedSpace
          (g' z)).mapDerivedCategoryFactors.inv.app P) ≫
            j.app (DerivedCategory.Q.obj P) =
          L.map ((DerivedCategory.quotientCompQhIso _).inv.app (stalkComplex g' z P)) ≫
            ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (stalkComplex g' z P)) ≫
            DerivedCategory.Qh.map
              (((ModuleCat.extendScalars.{u, u, u}
                ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
                  (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))).mapHomotopyCategoryFactors
                  (.up ℤ)).hom.app
                (stalkComplex g' z P)) ≫
            (DerivedCategory.quotientCompQhIso (ModuleCat.{u} (C z))).hom.app
              (tensorComplex f f' g g' sq z P) ≫
            DerivedCategory.Q.map (tensorStalkIso f f' g g' sq z P).hom ≫
            (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapDerivedCategoryFactors.inv.app
                (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) ≫
            (comparisonDerivedStalk X' z).map
              (cast (by rfl)
                (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (A g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (C z))
  dsimp only
  intro L ε hL
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let St := RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)
  let St' := RingedSpace.moduleStalkFunctor X'.toRingedSpace z
  let E := ModuleCat.extendScalars.{u, u, u}
    ((algebraMap (A g' z ⊗[R f g' z] B f' z) (C z)).comp
      (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)))
  let T := derivedPullback g' ⋙ comparisonDerivedStalk X' z
  let A₀ := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let B₀ := SheafOfModules.{u} (moduleRings X'.toRingedSpace)
  let W := HomotopyCategory.quasiIso A₀ (.up ℤ)
  let α := (Functor.associator DerivedCategory.Qh (derivedPullback g')
    (comparisonDerivedStalk X' z)).inv ≫
    Functor.whiskerRight (counit g') (comparisonDerivedStalk X' z)
  have hT : T.IsLeftDerivedFunctor α W :=
    derivedPullback_stalk_isLeftDerivedFunctor g' z
  have := hT
  let Sc := St.mapHomologicalComplex (.up ℤ)
  let Pc := (Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)
  let Stc := St'.mapHomologicalComplex (.up ℤ)
  let q := HomotopyCategory.quotient A₀ (.up ℤ)
  let F := ((Scheme.Modules.tensorPullback g').mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh (C := B₀)) ⋙ comparisonDerivedStalk X' z
  let δ : Sc ⋙ E.mapHomologicalComplex (.up ℤ) ⟶ Pc ⋙ Stc :=
    { app := fun P ↦ (tensorStalkIso f f' g g' sq z P).hom
      naturality := fun _ _ a ↦ tensorStalkIso_naturality f f' g g' sq z a }
  let βc : q ⋙ (DerivedCategory.Qh ⋙ (comparisonDerivedStalk X (g' z) ⋙ L)) ⟶
      q ⋙ F :=
    Functor.whiskerRight St.mapDerivedCategoryFactors.hom L ≫
      Functor.whiskerLeft (Sc ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε ≫
      Functor.whiskerRight δ DerivedCategory.Q ≫
      Functor.whiskerLeft Pc St'.mapDerivedCategoryFactors.inv
  let β : DerivedCategory.Qh ⋙ (comparisonDerivedStalk X (g' z) ⋙ L) ⟶ F :=
    CategoryTheory.Quotient.natTransLift _ βc
  let j := T.leftDerivedLift α W (comparisonDerivedStalk X (g' z) ⋙ L) β
  refine ⟨j, ?_⟩
  intro P hP hcP
  have := hcP
  have hj := T.leftDerived_fac_app α W (comparisonDerivedStalk X (g' z) ⋙ L) β (q.obj P)
  change j.app (DerivedCategory.Q.obj P) ≫ α.app (q.obj P) = βc.app P at hj
  have hα : α.app (q.obj P) =
      (comparisonDerivedStalk X' z).map ((counit g').app (q.obj P)) := by
    change 𝟙 _ ≫ _ = _
    exact Category.id_comp _
  rw [hα] at hj
  have hcoord := mapped_iso_left_normalization L (St.mapDerivedCategoryFactors.app P)
    ((comparisonDerivedStalk X' z).mapIso (asIso ((counit g').app (q.obj P))))
    (j.app (DerivedCategory.Q.obj P))
    (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj (Sc.obj P)))
    (DerivedCategory.Q.map (tensorStalkIso f f' g g' sq z P).hom)
    (St'.mapDerivedCategoryFactors.inv.app (Pc.obj P)) hj
  have hq : L.map ((DerivedCategory.quotientCompQhIso _).inv.app
      (stalkComplex g' z P)) = 𝟙 _ := L.map_id _
  have hE : DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (.up ℤ)).hom.app
      (stalkComplex g' z P)) = 𝟙 _ := DerivedCategory.Qh.map_id _
  have hq' : (DerivedCategory.quotientCompQhIso (ModuleCat.{u} (C z))).hom.app
      (tensorComplex f f' g g' sq z P) = 𝟙 _ := rfl
  erw [hq, hE, hq', Category.id_comp, Category.id_comp, Category.id_comp]
  exact hcoord

end AlgebraicGeometry.SingleComplexBaseChange
