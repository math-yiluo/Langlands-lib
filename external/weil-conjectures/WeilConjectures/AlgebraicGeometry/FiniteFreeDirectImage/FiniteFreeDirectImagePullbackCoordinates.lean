/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingComputed
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeOrdinaryPullbackCoordinates
import all WeilConjectures.AlgebraicGeometry.Derived.DerivedFiniteFreeScalarCoordinates
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Finite-free coordinates for the computed scalar pullback comparison

Source: Stacks Project, Tags 03EL, 06YY and 0944.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

section DerivedBridge

universe w uA vA uB vB
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
  (T : A ⥤ B) [T.Additive] (E : DerivedCategory A ⥤ DerivedCategory B)
  (ε : DerivedCategory.Qh ⋙ E ⟶ T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)

private def cochainCounit : DerivedCategory.Q ⋙ E ⟶
    T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app K := ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj K)
  naturality := by
    intro X Y f
    exact ε.naturality ((HomotopyCategory.quotient A (.up ℤ)).map f)

private instance [IsIso ε] : IsIso (cochainCounit T E ε) := by
  have (K : CochainComplex A ℤ) : IsIso ((cochainCounit T E ε).app K) :=
    inferInstanceAs (IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj K)))
  exact NatIso.isIso_of_isIso_app _

private theorem factorsh_eq (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [F.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app K ≫
    𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
  erw [F.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id]
  simp only [Category.id_comp]
  exact Category.comp_id _

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{w} D]
  (F : A ⥤ C) (G : B ⥤ D) (T' : C ⥤ D) [F.Additive] [G.Additive] [T'.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (E' : DerivedCategory C ⥤ DerivedCategory D)
  (ε' : DerivedCategory.Qh ⋙ E' ⟶ T'.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [IsIso ε] [IsIso ε']
  (χ : T ⋙ G ≅ F ⋙ T')

private theorem scalarComparisonDescent_homotopy_normalized (H : HomotopyCategory A (.up ℤ)) :
    (SheafOfModules.RingedTensor.scalarComparisonDescent T F G T' E
      (cochainCounit T E ε) E' (cochainCounit T' E' ε') χ).hom.app
      (DerivedCategory.Qh.obj H) ≫
      E'.map (F.mapDerivedCategoryFactorsh.hom.app H) ≫
      ε'.app ((F.mapHomotopyCategory (.up ℤ)).obj H) =
    G.mapDerivedCategory.map (ε.app H) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((T.mapHomotopyCategory (.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ G)) (.up ℤ)).hom.app H ≫
          (χ.hom.mapHomotopyCategory (.up ℤ)).app H ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ T')) (.up ℤ)).inv.app H) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  rw [factorsh_eq]
  erw [factorsh_eq]
  have h := SheafOfModules.RingedTensor.scalarComparisonDescent_normalized T F G T'
    E (cochainCounit T E ε) E' (cochainCounit T' E' ε') χ K
  have hh : DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ G)) (.up ℤ)).hom.app
          ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≫
        (χ.hom.mapHomotopyCategory (.up ℤ)).app
          ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ T')) (.up ℤ)).inv.app
          ((HomotopyCategory.quotient A (.up ℤ)).obj K)) =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ G)) (.up ℤ)).hom.app K ≫
          (χ.hom.mapHomologicalComplex (.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ T')) (.up ℤ)).inv.app K) := by
    simp only [Functor.map_comp]
    rfl
  rw [hh]
  exact h

end DerivedBridge

section CoordinateColumns

universe uA1 vA1 uB1 vB1
open CategoryTheory CategoryTheory.Limits
variable {A : Type uA1} [Category.{vA1} A] [Preadditive A] [HasFiniteBiproducts A]
  {B : Type uB1} [Category.{vB1} B] [Preadditive B] [HasFiniteBiproducts B]
  (d : ℕ)

private theorem powerInjection_naturality {X Y : A} (f : X ⟶ Y) (i : Fin d) :
    biproduct.ι (fun _ : Fin d ↦ X) i ≫
        (biproduct.isoProduct (fun _ : Fin d ↦ X)).hom ≫
        (Functor.const (Discrete (Fin d)) ⋙ (lim : (Discrete (Fin d) ⥤ A) ⥤ A)).map f =
      f ≫ biproduct.ι (fun _ : Fin d ↦ Y) i ≫
        (biproduct.isoProduct (fun _ : Fin d ↦ Y)).hom := by
  apply limit.hom_ext
  rintro ⟨j⟩
  change (biproduct.ι (fun _ : Fin d ↦ X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ X)).hom ≫
      (Functor.const (Discrete (Fin d)) ⋙ lim).map f) ≫ Pi.π (fun _ : Fin d ↦ Y) j =
    (f ≫ biproduct.ι (fun _ : Fin d ↦ Y) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ Y)).hom) ≫ Pi.π (fun _ : Fin d ↦ Y) j
  simp only [Functor.comp_map, Category.assoc]
  erw [limMap_π]
  change biproduct.ι (fun _ : Fin d ↦ X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ X)).hom ≫ Pi.π _ j ≫ f =
    f ≫ biproduct.ι (fun _ : Fin d ↦ Y) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ Y)).hom ≫ Pi.π _ j
  simp only [biproduct.isoProduct_hom, Pi.lift_comp_π]
  erw [Pi.lift_comp_π_assoc]
  by_cases h : i = j <;> simp [h]

private theorem coordinateInjection_naturality_private (V : A ⥤ A)
    (Φ : V ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
    {X Y : A} (f : X ⟶ Y) (i : Fin d) :
    biproduct.ι (fun _ : Fin d ↦ X) i ≫
        (biproduct.isoProduct (fun _ : Fin d ↦ X)).hom ≫ Φ.inv.app X ≫ V.map f =
      f ≫ biproduct.ι (fun _ : Fin d ↦ Y) i ≫
        (biproduct.isoProduct (fun _ : Fin d ↦ Y)).hom ≫ Φ.inv.app Y := by
  rw [← Φ.inv.naturality f]
  simpa only [Category.assoc] using
    congrArg (fun h ↦ h ≫ Φ.inv.app Y) (powerInjection_naturality d f i)

/-- Public export of the private `coordinateInjection_naturality_private`
(used by `import all` importers; linter.privateModule). -/
alias coordinateInjection_naturality := coordinateInjection_naturality_private

private theorem powerInjection_map (F : A ⥤ B) [F.Additive]
    (X : A) (i : Fin d) :
    F.map (biproduct.ι (fun _ : Fin d ↦ X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ X)).hom) ≫
      (SheafOfModules.RingedTensor.powerComparison F d).hom.app X =
    biproduct.ι (fun _ : Fin d ↦ F.obj X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ F.obj X)).hom := by
  apply limit.hom_ext
  rintro ⟨j⟩
  change _ ≫ Pi.π (fun _ : Fin d ↦ F.obj X) j =
    (biproduct.ι (fun _ : Fin d ↦ F.obj X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ F.obj X)).hom) ≫ Pi.π _ j
  rw [Category.assoc, SheafOfModules.RingedTensor.powerComparison_π,
    ← F.map_comp, Category.assoc, biproduct.isoProduct_hom, Pi.lift_comp_π,
    biproduct.isoProduct_hom, Category.assoc, Pi.lift_comp_π]
  by_cases h : i = j <;> simp [h]

private theorem coordinateInjection_square_private (F : A ⥤ B) [F.Additive]
    (V : A ⥤ A) (V' : B ⥤ B)
    (Φ : V ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
    (Φ' : V' ≅ Functor.const (Discrete (Fin d)) ⋙ lim)
    (τ : V ⋙ F ⟶ F ⋙ V')
    (hτ : ∀ X, F.map (Φ.hom.app X) ≫
      (SheafOfModules.RingedTensor.powerComparison F d).hom.app X =
      τ.app X ≫ Φ'.hom.app (F.obj X))
    (X : A) (i : Fin d) :
    F.map (biproduct.ι (fun _ : Fin d ↦ X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ X)).hom ≫ Φ.inv.app X) ≫ τ.app X =
    biproduct.ι (fun _ : Fin d ↦ F.obj X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ F.obj X)).hom ≫ Φ'.inv.app (F.obj X) := by
  apply (cancel_mono (Φ'.hom.app (F.obj X))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← hτ X, ← Category.assoc, ← F.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  change F.map (biproduct.ι (fun _ : Fin d ↦ X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ X)).hom ≫ 𝟙 _) ≫
      (SheafOfModules.RingedTensor.powerComparison F d).hom.app X =
    biproduct.ι (fun _ : Fin d ↦ F.obj X) i ≫
      (biproduct.isoProduct (fun _ : Fin d ↦ F.obj X)).hom ≫ 𝟙 _
  simp only [Category.comp_id]
  exact powerInjection_map d F X i

/-- Public export of the private `coordinateInjection_square_private`
(used by `import all` importers; linter.privateModule). -/
alias coordinateInjection_square := coordinateInjection_square_private

end CoordinateColumns

/-- The finite-basis tensor coordinates commute with termwise scalar pullback.
This concerns inverse image and the computed comparison, before the comparison
is identified with the conjugate of the derived direct-image square.
Source: Stacks Project, Tags 03EL, 06YY and 0944.
(blueprint: lem-sp-finite-free-direct-image-pullback-coordinates).

Proof: choose the given basis of S_W over R_W. Pull it back by the exact module
inverse image, identify the pulled-back regular module with the regular module
of S_Z, and use the restriction/pullback comparison to obtain a basis of S_Z
of the same rank. The maps from tuples to sums of basis tensors and from tensors
to their coordinate tuples are inverse by the tensor relations. They are natural
in the module. In these coordinates scalar extension is a finite power, hence
is exact, including in rank zero. Its universal derived counit is therefore
invertible on every complex. Apply the coordinates degreewise and descend through
localization, obtaining the two displayed families of isomorphisms and their
naturality. Apply ordinary balancing degreewise and conjugate by the two
invertible universal scalar counits to obtain beta and its computed equation.
For the last equation first project to each basis coordinate. The ordinary
restriction/pullback map identifies the coefficient actions, and ordinary
balancing sends each pulled-back basis tensor to the same tensor with its
pulled-back coefficient. Thus the coordinate projections agree on all pure
tensors; tensor extensionality proves the ordinary square. Passing to complexes
and localization proves the stated equation. -/
theorem finiteFreeDirectImage_pullbackCoordinates {Z W : Scheme.{u}} (q : Z ⟶ W)
    (sW : ScalarModel W) (sZ : ScalarModel Z)
    (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ)
    (hfree : Nonempty ((proEtaleRingRestrictScalars a.target).obj
            (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)) ≅
          SheafOfModules.free (R := (sheafCompose (ProEt.topology W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)
            (ULift.{u + 1} (Fin d)))) :
    ∃ (eW : ∀ X : DerivedCategory (proEtaleRingModules W R.target),
        (⨁ fun _ : Fin d ↦ X) ≅
          (proEtaleRingRestrictScalars a.target).mapDerivedCategory.obj
            ((sW.presentation a.target).derived.obj X))
      (eZ : ∀ X : DerivedCategory (proEtaleRingModules Z R.source),
        (⨁ fun _ : Fin d ↦ X) ≅
          (proEtaleRingRestrictScalars a.source).mapDerivedCategory.obj
            ((sZ.presentation a.source).derived.obj X))
      (β : (sW.presentation a.target).derived ⋙
          proEtaleRingDerivedPullback q S.target S.source S.identification ≅
        proEtaleRingDerivedPullback q R.target R.source R.identification ⋙
          (sZ.presentation a.source).derived),
      (∀ H : HomotopyCategory (proEtaleRingModules Z R.source) (.up ℤ),
        IsIso ((sZ.presentation a.source).counit.app H)) ∧
      BalancingComputed sW sZ a β ∧
      (∀ {X Y : DerivedCategory (proEtaleRingModules Z R.source)} (f : X ⟶ Y)
        (i : Fin d), biproduct.ι (fun _ : Fin d ↦ X) i ≫ (eZ X).hom ≫
          (proEtaleRingRestrictScalars a.source).mapDerivedCategory.map
            ((sZ.presentation a.source).derived.map f) =
          f ≫ biproduct.ι (fun _ : Fin d ↦ Y) i ≫ (eZ Y).hom) ∧
      ∀ (X : DerivedCategory (proEtaleRingModules W R.target)) (i : Fin d),
        (proEtaleRingDerivedPullback q R.target R.source R.identification).map
            (biproduct.ι _ i ≫ (eW X).hom) ≫
          (proEtaleRingRestrictionDerivedPullback q R.target S.target R.source S.source
            a.target a.source R.identification S.identification a.comm).inv.app
              ((sW.presentation a.target).derived.obj X) ≫
          (proEtaleRingRestrictScalars a.source).mapDerivedCategory.map (β.hom.app X) =
        biproduct.ι _ i ≫
          (eZ ((proEtaleRingDerivedPullback q R.target R.source R.identification).obj X)).hom := by
  obtain ⟨φW, φZ, hεW, hεZ, hordinary⟩ :=
    finiteFreeDirectImage_ordinaryPullbackCoordinates q sW sZ R S a d hfree
  let T := (sW.presentation a.target).ordinary
  let T' := (sZ.presentation a.source).ordinary
  let U := proEtaleRingRestrictScalars a.target
  let U' := proEtaleRingRestrictScalars a.source
  let F := proEtaleRingModulePullback q R.target R.source R.identification
  let G := proEtaleRingModulePullback q S.target S.source S.identification
  let E := (sW.presentation a.target).derived
  let E' := (sZ.presentation a.source).derived
  let εh := (sW.presentation a.target).counit
  let εh' := (sZ.presentation a.source).counit
  let (H : HomotopyCategory (proEtaleRingModules W R.target) (.up ℤ)) :
      IsIso (εh.app H) := hεW H
  let : IsIso εh := NatIso.isIso_of_isIso_app _
  let (H : HomotopyCategory (proEtaleRingModules Z R.source) (.up ℤ)) :
      IsIso (εh'.app H) := hεZ H
  let : IsIso εh' := NatIso.isIso_of_isIso_app _
  let ε := cochainCounit T E εh
  let ε' := cochainCounit T' E' εh'
  let χ := ordinaryBalancing sW sZ a
  let := proEtaleRingRestrictionPullbackInv_isIso q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm
  let ρ := asIso (proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm)
  let Φ := SheafOfModules.RingedTensor.coordinateDescent T U d E ε φW
  let Φ' := SheafOfModules.RingedTensor.coordinateDescent T' U' d E' ε' φZ
  let β := SheafOfModules.RingedTensor.scalarComparisonDescent T F G T' E ε E' ε' χ
  let ρD := Functor.mapDerivedCategoryCompIso U F ≪≫
    Functor.mapDerivedCategoryNatIso ρ ≪≫ (Functor.mapDerivedCategoryCompIso G U').symm
  let τ := Functor.whiskerLeft E ρD.hom ≫
    Functor.whiskerRight β.hom U'.mapDerivedCategory
  have hρD : ρD.hom = (proEtaleRingRestrictionDerivedPullback q R.target S.target
      R.source S.source a.target a.source R.identification S.identification a.comm).inv := by
    simp only [ρD, proEtaleRingRestrictionDerivedPullback,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
    rw [← Functor.mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq]
  have hsquare (M : proEtaleRingModules W R.target) :
      F.map (φW.hom.app M) ≫ (SheafOfModules.RingedTensor.powerComparison F d).hom.app M =
        ρ.hom.app (T.obj M) ≫ U'.map (χ.hom.app M) ≫ φZ.hom.app (F.obj M) := by
    unfold SheafOfModules.RingedTensor.powerComparison
    exact hordinary M
  have hτ (X : DerivedCategory (proEtaleRingModules W R.target)) :
      F.mapDerivedCategory.map (Φ.hom.app X) ≫
        (SheafOfModules.RingedTensor.powerComparison F.mapDerivedCategory d).hom.app X =
      τ.app X ≫ Φ'.hom.app (F.mapDerivedCategory.obj X) := by
    simpa only [τ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using
      SheafOfModules.RingedTensor.derivedCoordinateSquare T U d F G T' U' E ε E' ε' χ
      ρ φW φZ hsquare Φ Φ'
      (SheafOfModules.RingedTensor.coordinateDescent_normalized T U d E ε φW)
      (SheafOfModules.RingedTensor.coordinateDescent_normalized T' U' d E' ε' φZ) X
  let eW (X : DerivedCategory (proEtaleRingModules W R.target)) :=
    biproduct.isoProduct (fun _ : Fin d ↦ X) ≪≫ (Φ.app X).symm
  let eZ (X : DerivedCategory (proEtaleRingModules Z R.source)) :=
    biproduct.isoProduct (fun _ : Fin d ↦ X) ≪≫ (Φ'.app X).symm
  refine ⟨eW, eZ, β, hεZ, ?_, ?_, ?_⟩
  · intro H
    exact scalarComparisonDescent_homotopy_normalized T E εh F G T' E' εh' χ H
  · intro X Y f i
    simpa only [eZ, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
      Functor.comp_map, Category.assoc] using
      coordinateInjection_naturality_private d (E' ⋙ U'.mapDerivedCategory) Φ' f i
  · intro X i
    have h := coordinateInjection_square_private d F.mapDerivedCategory
      (E ⋙ U.mapDerivedCategory) (E' ⋙ U'.mapDerivedCategory) Φ Φ' τ hτ X i
    simpa only [τ, eW, eZ, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc, hρD] using h

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
