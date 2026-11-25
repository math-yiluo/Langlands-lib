/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
/-!
# Ringed-topos pullback preserves K-flat complexes with flat terms
Source: Stacks Project, Cohomology on Sites, Tag 0G7E, lemma-pullback-K-flat
(auxiliary; not a blueprint node).
-/
@[expose] public section
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

open CategoryTheory.Functor MonoidalCategory

private def sheafUliftIso
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    (A : Type uD) [Category.{vD} A] (U : A ⥤ Type w)
    [J.HasSheafCompose U] [J.HasSheafCompose (U ⋙ uliftFunctor.{w, w})] :
    sheafCompose J (U ⋙ uliftFunctor.{w, w}) ≅ sheafCompose J U :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun X ↦ uliftTrivial (U.obj (M.obj.obj X)))
      (by intros; rfl))) (by intros; rfl)

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  {R : Sheaf JC CommRingCat.{w}} {RI : Sheaf JD CommRingCat.{w}}
  {L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w)}

set_option backward.isDefEq.respectTransparency false in
private noncomputable def inverseImageOfUniverses (I : AlgebraicInverseImage L R RI) :
    AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L R RI := by
  let eR := sheafUliftIso JC CommRingCat.{w} (CategoryTheory.forget CommRingCat.{w})
  let eS := sheafUliftIso JD CommRingCat.{w} (CategoryTheory.forget CommRingCat.{w})
  let eM := isoWhiskerLeft (toSheaf ((sheafCompose JC
    (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) <|
    sheafUliftIso JC AddCommGrpCat.{w} (CategoryTheory.forget AddCommGrpCat.{w})
  let eN := isoWhiskerLeft (toSheaf ((sheafCompose JD
    (forget₂ CommRingCat.{w} RingCat.{w})).obj RI)) <|
    sheafUliftIso JD AddCommGrpCat.{w} (CategoryTheory.forget AddCommGrpCat.{w})
  let er := L.mapIso (eR.app R) ≪≫ I.ringUnderlying ≪≫ (eS.app RI).symm
  let em := isoWhiskerLeft I.modules eN ≪≫ I.moduleUnderlying ≪≫
    isoWhiskerRight eM.symm L
  refine
    { ringUnderlying := er
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      modules := I.modules
      moduleUnderlying := em
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T a b t h V x
    have hr := I.ringAdd T (a ≫ (eR.app R).hom) (b ≫ (eR.app R).hom)
      (t ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a b t h V x
    have hr := I.ringMul T (a ≫ (eR.app R).hom) (b ≫ (eR.app R).hom)
      (t ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringZero T (a ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringOne T (a ≫ (eR.app R).hom) h V x
    simpa [er, eS, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleAdd M T (a ≫ (eM.app M).hom) (b ≫ (eM.app M).hom)
      (t ≫ (eM.app M).hom) h V x
    simpa [em, eN, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a h V x
    have hr := I.moduleZero M T (a ≫ (eM.app M).hom) h V x
    simpa [em, eN, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleSMul M T (a ≫ (eR.app R).hom) (b ≫ (eM.app M).hom)
      (t ≫ (eM.app M).hom) h V x
    simpa [er, em, eS, eN, sheafUliftIso, uliftTrivial, Functor.map_comp] using hr

set_option backward.isDefEq.respectTransparency false in
private theorem changeOfRings_eq_ofUniverses
    {S : Sheaf JD CommRingCat.{w}} (c : RI ⟶ S)
    (M : SheafOfModules.{w}
      ((sheafCompose JD (forget₂ CommRingCat.{w} RingCat.{w})).obj RI)) :
    changeOfRings c M = changeOfRingsOfUniverses c M := by
  rfl


section ConeHelpers

universe u v
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})

private local instance (I : Type w) :
    HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
  PresheafOfModules.hasColimitsOfShape
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj (Discrete I)

private theorem kFlat_cone_independent
    (K L : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (f : K ⟶ L) :
    (K.IsKFlatIndependentCoefficients → L.IsKFlatIndependentCoefficients →
      (CochainComplex.mappingCone f).IsKFlatIndependentCoefficients) ∧
    (K.IsKFlatIndependentCoefficients →
      (CochainComplex.mappingCone f).IsKFlatIndependentCoefficients →
      L.IsKFlatIndependentCoefficients) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := tensorLeft_additive_independent R
  constructor
  all_goals
    intro hK hL A hA
    have h₁ := hK A hA
    have h₂ := hL A hA
    let g := HomologicalComplex.mapBifunctorMap (𝟙 A) f (curriedTensor _) (.up ℤ)
    let e := CochainComplex.mapBifunctorMappingCone₂Iso A f (curriedTensor _)
    let Q := HomotopyCategory.subcategoryAcyclic (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    have hT := HomotopyCategory.mappingCone_triangleh_distinguished g
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h₁ h₂ ⊢
    apply Q.prop_of_iso ((HomotopyCategory.quotient _ _).mapIso e.symm)
    exact Q.ext_of_isTriangulatedClosed₃ _ hT h₁ h₂
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h₁ h₂ ⊢
    apply Q.ext_of_isTriangulatedClosed₂ _ hT h₁
    exact Q.prop_of_iso ((HomotopyCategory.quotient _ _).mapIso e) h₂

private theorem kFlat_iso_independent
    {K L : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ}
    (e : K ≅ L) (hK : K.IsKFlatIndependentCoefficients) :
    L.IsKFlatIndependentCoefficients := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro A hA
  let e' := ((curriedTensor _).map₂CochainComplex.obj A).mapIso e
  have h := hK A hA
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h ⊢
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso
    ((HomotopyCategory.quotient _ _).mapIso e') h

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
private theorem flatOnSite_biprod
    (M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (hM : IsFlatOnSite (J := J) (R := R) M) (hN : IsFlatOnSite (J := J) (R := R) N) :
    IsFlatOnSite (J := J) (R := R) (M ⊞ N) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let T := (curriedTensor (SheafOfModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))).flip
  have : T.Additive := by
    refine ⟨?_⟩
    intro X Y f g
    apply NatTrans.ext
    funext Z
    exact (tensorLeft_additive_independent R Z).map_add
  have hM' : exactFunctor _ _ (tensorRight M) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M) hM
  have hN' : exactFunctor _ _ (tensorRight N) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R N) hN
  let G := (pair M N ⋙ T).flip
  have : PreservesFiniteLimits G := preservesFiniteLimits_of_evaluation _ (by
    rintro ⟨_ | _⟩
    · exact hM'.1
    · exact hN'.1)
  have : PreservesFiniteColimits G := preservesFiniteColimits_of_evaluation _ (by
    rintro ⟨_ | _⟩
    · exact hM'.2
    · exact hN'.2)
  let e : tensorRight (M ⊞ N) ≅ G ⋙ colim :=
    T.mapIso (biprod.isoCoprod M N) ≪≫ preservesColimitIso T (pair M N) ≪≫
      colimitIsoFlipCompColim (pair M N ⋙ T)
  have : HasFiniteBiproducts (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : PreservesFiniteLimits (colim (J := Discrete WalkingPair)
      (C := SheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))) := inferInstance
  have he : exactFunctor _ _ (tensorRight (M ⊞ N)) :=
    (exactFunctor _ _).prop_of_iso e.symm ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩)
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (M ⊞ N)).symm he

set_option backward.isDefEq.respectTransparency false in
private theorem flatOnSite_of_iso
    {M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)}
    (e : M ≅ N) (hM : IsFlatOnSite (J := J) (R := R) M) :
    IsFlatOnSite (J := J) (R := R) N := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  have hM' : exactFunctor _ _ (tensorRight M) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M) hM
  have hN' : exactFunctor _ _ (tensorRight N) :=
    (exactFunctor _ _).prop_of_iso ((curriedTensor _).flip.mapIso e) hM'
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R N).symm hN'

private theorem flatOnSite_mappingCone
    {K L : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ}
    (f : K ⟶ L) (hK : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (K.X n))
    (hL : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (L.X n)) (n : ℤ) :
    IsFlatOnSite (J := J) (R := R) ((CochainComplex.mappingCone f).X n) := by
  exact flatOnSite_of_iso R
    (HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl).symm
    (flatOnSite_biprod R _ _ (hK (n + 1)) (hL n))

end ConeHelpers

/-- Termwise pullback along a morphism of ringed topoi preserves K-flatness and flat
terms. Source: Stacks Project, Tag 0G7E, lemma-pullback-K-flat
(auxiliary; not a blueprint node).

`I` presents the algebraic inverse image of rings and modules along `uInv`; `hobj`
and `hmap` identify `uStar` with inverse image followed by scalar extension.

Proof: choose a flat K-flat resolution q : L → P whose pullback is K-flat. Since q
is a quasi-isomorphism, its cone A is acyclic. Tensor commutes with mapping cones;
the acyclic subcategory is triangulated, so K-flatness of L and P makes A K-flat.
Its terms are finite sums of terms of L and P, hence flat. The acyclic case of
Stacks 0G7E makes uStar(A) K-flat. Additive functors commute with cones, so the cone
of uStar(q) is K-flat. Cone two-out-of-three with uStar(L) now proves that uStar(P)
is K-flat. Flatness in each degree follows separately from flat-module pullback.
-/
theorem isKFlat_ringedToposPullback
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{w}} {S RI : Sheaf JD CommRingCat.{w}}
    (uInv : Sheaf JC (Type (w)) ⥤ Sheaf JD (Type (w)))
    (uPush : Sheaf JD (Type (w)) ⥤ Sheaf JC (Type (w)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose JD
        (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hobj : ∀ M : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R),
      uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (a : M ⟶ N),
      uStar.map a = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm)
    [uStar.Additive]
    (P : CochainComplex (SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
      ∀ n : ℤ, IsFlatOnSite (J := JD) (R := S)
        (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨L, q, hL, hLflat, hq, hImageL⟩ :=
      exists_pullback_adapted_flat_resolution uInv uPush adj I c uStar hobj hmap P
    have hCone := (kFlat_cone_independent R L P q).1 hL hP
    have hConeFlat := flatOnSite_mappingCone R q hLflat hflat
    have hConeAcyclic := (CochainComplex.mappingCone.quasiIso_iff_acyclic q).mp hq
    have hImageCone := isKFlat_ringedToposPullback_of_acyclic uInv uPush adj I c
      uStar hobj hmap (CochainComplex.mappingCone q) hConeAcyclic hCone hConeFlat
    let F := uStar.mapHomologicalComplex (ComplexShape.up ℤ)
    have hMappedCone := kFlat_iso_independent S
      (CochainComplex.mappingCone.mapHomologicalComplexIso q uStar) hImageCone
    exact (kFlat_cone_independent S (F.obj L) (F.obj P) (F.map q)).2 hImageL hMappedCone
  · intro n
    change IsFlatOnSite (uStar.obj (P.X n))
    rw [hobj (P.X n), changeOfRings_eq_ofUniverses]
    exact isFlat_ringedToposPullback.{uC, vC, uD, vD, w, w} uInv uPush adj
      (inverseImageOfUniverses I) c (P.X n) (hflat n)
end SheafOfModules
