/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
public import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarSource
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import all WeilConjectures.AlgebraicGeometry.ResidueQuotientDerivedUnit
import WeilConjectures.AlgebraicGeometry.ScalarUniversalDerivedUnit
import WeilConjectures.AlgebraicGeometry.SupportedIntegralResidueSequence
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃ u
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
namespace CategoryTheory.Functor

private theorem scalar_unit_comp
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    [HasDerivedCategory.{w₃} C]
    (U : A ⥤ B) (V : B ⥤ C) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (F : C) (G : B) (H : A) (η : F ⟶ V.obj G) (θ : G ⟶ U.obj H)
    (hη : V.DerivedUnit F G η) (hθ : U.DerivedUnit G H θ) :
    (U ⋙ V).DerivedUnit F H (η ≫ V.map θ) := by
  unfold DerivedUnit at *
  intro K
  let e := (mapDerivedCategoryCompIso U V).symm.app K
  have hb := (hη (U.mapDerivedCategory.obj K)).comp (hθ K)
  have he (f : (DerivedCategory.singleFunctor A 0).obj H ⟶ K) :
      (DerivedCategory.singleFunctor C 0).map η ≫
          (V.mapDerivedCategorySingleFunctor 0).inv.app G ≫
        V.mapDerivedCategory.map ((DerivedCategory.singleFunctor B 0).map θ ≫
          (U.mapDerivedCategorySingleFunctor 0).inv.app H ≫ U.mapDerivedCategory.map f) =
      (DerivedCategory.singleFunctor C 0).map (η ≫ V.map θ) ≫
        ((U ⋙ V).mapDerivedCategorySingleFunctor 0).inv.app H ≫
          (U ⋙ V).mapDerivedCategory.map f ≫ e.hom := by
    simp only [Functor.map_comp, Category.assoc]
    erw [← (V.mapDerivedCategorySingleFunctor 0).inv.naturality_assoc θ]
    have hc := derivedCompSingle U V H
    have hci : (V.mapDerivedCategorySingleFunctor 0).inv.app (U.obj H) ≫
        V.mapDerivedCategory.map ((U.mapDerivedCategorySingleFunctor 0).inv.app H) =
      ((U ⋙ V).mapDerivedCategorySingleFunctor 0).inv.app H ≫
        (mapDerivedCategoryCompIso U V).inv.app
          ((DerivedCategory.singleFunctor A 0).obj H) := by
      let z := (V.mapDerivedCategorySingleFunctor 0).app (U.obj H)
      let y := V.mapDerivedCategory.mapIso ((U.mapDerivedCategorySingleFunctor 0).app H)
      apply (cancel_mono (y.hom ≫ z.hom)).1
      change (z.inv ≫ y.inv) ≫ (y.hom ≫ z.hom) = _
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
      change 𝟙 _ = ((U ⋙ V).mapDerivedCategorySingleFunctor 0).inv.app H ≫
        ((mapDerivedCategoryCompIso U V).inv.app
          ((DerivedCategory.singleFunctor A 0).obj H) ≫
            V.mapDerivedCategory.map ((U.mapDerivedCategorySingleFunctor 0).hom.app H) ≫
              (V.mapDerivedCategorySingleFunctor 0).hom.app (U.obj H))
      rw [hc]
      exact (Iso.inv_hom_id_app _ _).symm
    rw [reassoc_of% hci]
    erw [← (mapDerivedCategoryCompIso U V).inv.naturality f]
    rfl
  have hb' : Function.Bijective (fun f : (DerivedCategory.singleFunctor A 0).obj H ⟶ K ↦
      ((DerivedCategory.singleFunctor C 0).map (η ≫ V.map θ) ≫
        ((U ⋙ V).mapDerivedCategorySingleFunctor 0).inv.app H ≫
          (U ⋙ V).mapDerivedCategory.map f) ≫ e.hom) := by
    simpa only [Function.comp_def, he, Category.assoc] using hb
  apply Function.Bijective.of_comp_left (f := fun z ↦ z ≫ e.hom) hb'
  intro f g h
  exact (cancel_mono e.hom).1 h

private theorem scalar_unit_iso
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (U V : A ⥤ B) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (ε : U ≅ V) (F : B) (H : A) (η : F ⟶ U.obj H)
    (h : U.DerivedUnit F H η) :
    V.DerivedUnit F H (η ≫ ε.hom.app H) := by
  unfold DerivedUnit at *
  let e := mapDerivedCategoryNatIso ε
  have hn : (U.mapDerivedCategorySingleFunctor 0).inv.app H ≫
      e.hom.app ((DerivedCategory.singleFunctor A 0).obj H) =
    (DerivedCategory.singleFunctor B 0).map (ε.hom.app H) ≫
      (V.mapDerivedCategorySingleFunctor 0).inv.app H := by
    apply (cancel_mono ((V.mapDerivedCategorySingleFunctor 0).hom.app H)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    rw [derivedNatSingle U V ε H]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  intro K
  have hb := (Iso.homCongr (Iso.refl _) (e.app K)).bijective.comp (h K)
  have he (f : (DerivedCategory.singleFunctor A 0).obj H ⟶ K) :
      ((DerivedCategory.singleFunctor B 0).map η ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app H ≫ U.mapDerivedCategory.map f) ≫
          e.hom.app K =
        (DerivedCategory.singleFunctor B 0).map (η ≫ ε.hom.app H) ≫
          (V.mapDerivedCategorySingleFunctor 0).inv.app H ≫ V.mapDerivedCategory.map f := by
    simp only [Category.assoc]
    rw [e.hom.naturality, reassoc_of% hn]
    simp only [Functor.map_comp, Category.assoc]
  simpa only [Function.comp_def, Iso.homCongr_apply, Iso.refl_inv,
    Category.id_comp, Iso.app_hom, he] using hb

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
-- Reuse the instance witnesses fixed by the ordinary derived-category interface.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
private theorem cachedAbSheafify (Z : Scheme.{u}) :
    HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u + 1} := inferInstance
private theorem cachedModSheafify (Z : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    HasSheafify Z.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance
attribute [local instance] cachedAbSheafify cachedModSheafify
private theorem generator_scalar
    (T : Scheme.{u}) {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A)
    (η : ordinaryFiniteConstant R T ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (ordinaryFiniteConstant A T))
    (hη : ∀ (W : T.Etaleᵒᵖ) (r : R),
      η.hom.app W ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app W r) =
      (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of A A))).app W (φ r)) :
    ordinaryFiniteIntegralGenerator R T ≫ (moduleAbelianForget R T).map η =
      ordinaryFiniteIntegralGenerator A T := by
  let adj := constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  rw [ordinaryFiniteIntegralGenerator, ordinaryFiniteIntegralGenerator]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext x
  change η.hom.app (op (Scheme.Etale.mk (𝟙 T)))
      ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app _ (x.down : R)) = _
  rw [hη, map_intCast]
  rfl

/-- Let i:D→T be a closed immersion, n>0 and A a finite commutative ring killed by n. The normalized
integral generator i_*Z_D→forget(i_*A_D) has the unbounded DerivedUnit property
[def-sp-exact-functor-derived-unit, def-asd-ordinary-finite-p1-kummer-class]. No flatness of A over
Z/n is assumed.
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (auxiliary; not a blueprint node).
Proof: Apply the residue-quotient unit theorem to the supported integer/residue exact sequence. The
existing supported-constant coefficient theorem supplies its normalized derived unit from ULift(Z/n)
to A. Compose the two Hom bijections, using the derived composition/single coherence. The
constant-sections adjunction and normalization on generators identify the composed ordinary map with
the integral generator. Transport across the identity isomorphism between composite and direct
coefficient forgetting. -/
theorem supported_integral_derived_unit
    (T : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (n : A) = 0)
    {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    (moduleAbelianForget A T).DerivedUnit
      ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
      ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (supportedIntegralGenerator A i) := by
  let R := ULift.{u + 1} (ZMod n)
  let φ := supportedScalarMap n A hA
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  let V := moduleAbelianForget R T
  let F := (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D)
  let G := (lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D)
  let H := (lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D)
  obtain ⟨ηD, ηT, hD, hT, hηD, hη, hηT, hnat⟩ :=
    supported_kummer_scalar_source T n hn A hA i
  let θ : G ⟶ U.obj H :=
    (lowerStar (ModuleCat.{u + 1} R) i).map ηD ≫
      (lowerStarCompRestrictScalarsIso φ i).inv.app (ordinaryFiniteConstant A D)
  have hθ := hη
  unfold SupportedDerivedScalarUnit at hθ
  have hθ : U.DerivedUnit G H θ := by
    exact SheafExactDegreeZero.scalarUniversal_derivedUnit T.smallEtaleTopology φ G H θ hθ
  obtain ⟨w, hw⟩ := supported_integral_residue_sequence i n hn
  have hq := CategoryTheory.Sheaf.ConstantResidue.quotient_derived_unit
    T.smallEtaleTopology n hn F G (supportedIntegralGenerator R i) w hw
  have hcomp := CategoryTheory.Functor.scalar_unit_comp U V F G H
    (supportedIntegralGenerator R i) θ hq hθ
  have hγ : supportedIntegralGenerator R i ≫ V.map θ =
      supportedIntegralGenerator A i := by
    change (lowerStar AddCommGrpCat.{u + 1} i).map (ordinaryFiniteIntegralGenerator R D) ≫
      (lowerStar AddCommGrpCat.{u + 1} i).map
        ((moduleAbelianForget R D).map ηD) = _
    rw [← Functor.map_comp, generator_scalar D φ ηD hD]
    rfl
  have hiso := CategoryTheory.Functor.scalar_unit_iso (U ⋙ V)
    (moduleAbelianForget A T) (Iso.refl _) F H
    (supportedIntegralGenerator R i ≫ V.map θ) hcomp
  simp only [Iso.refl_hom, NatTrans.id_app, Category.comp_id, hγ] at hiso
  exact hiso

end AlgebraicGeometry.Etale
