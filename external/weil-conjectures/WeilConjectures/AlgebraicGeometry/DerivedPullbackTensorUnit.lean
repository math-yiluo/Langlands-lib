/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

/-! # Unit laws for derived pullback tensor comparisons

Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; the parent descent proof, step 3.
(blueprint: lem-pc-derived-pullback-tensor-unit).
-/

@[expose] public section

universe uModel wModel uTransport vTransport uTransport' vTransport'

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

attribute [local instance]
  tensorDescentPullbackDescentModuleTensor
  tensorDescentModuleSymmetric
  tensorDescentModulePreadditive
  tensorDescentModuleClosed
  tensorDescentModuleGrothendieck
  tensorDescentModuleResolutions
  tensorDescentModuleDerivedMonoidal
  tensorDescentPullbackDescentQLax

private theorem tensorUnit_left_of_iso
    {C : Type uTransport} {D : Type uTransport'}
    [Category.{vTransport} C] [Category.{vTransport'} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) (μ : curriedTensorPre L ≅ curriedTensorPost L)
    (η : 𝟙_ D ≅ L.obj (𝟙_ C)) {A B : C} (e : A ≅ B)
    (h : (λ_ (L.obj A)).hom = η.hom ▷ L.obj A ≫
      ((μ.app (𝟙_ C)).app A).hom ≫ L.map (λ_ A).hom) :
    (λ_ (L.obj B)).hom = η.hom ▷ L.obj B ≫
      ((μ.app (𝟙_ C)).app B).hom ≫ L.map (λ_ B).hom := by
  let a := λ_ (L.obj A)
  let b := whiskerRightIso η (L.obj A) ≪≫ (μ.app (𝟙_ C)).app A ≪≫ L.mapIso (λ_ A)
  have hab : a = b := Iso.ext h
  have hi : (λ_ (L.obj A)).inv = L.map (λ_ A).inv ≫
      ((μ.symm.app (𝟙_ C)).app A).hom ≫ η.inv ▷ L.obj A :=
    by simpa [a, b, Category.assoc] using congrArg Iso.inv hab
  have hj := Functor.OplaxMonoidal.oplax_left_unitality_of_iso μ.inv e hi
  let c := λ_ (L.obj B)
  let d := whiskerRightIso η (L.obj B) ≪≫ (μ.app (𝟙_ C)).app B ≪≫ L.mapIso (λ_ B)
  have hcd : c.symm = d.symm := by
    apply Iso.ext
    simpa [c, d, Category.assoc] using hj
  exact congrArg Iso.hom (Iso.symm_eq_iff.mp hcd)
private theorem tensorUnit_right_of_iso
    {C : Type uTransport} {D : Type uTransport'}
    [Category.{vTransport} C] [Category.{vTransport'} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) (μ : curriedTensorPre L ≅ curriedTensorPost L)
    (η : 𝟙_ D ≅ L.obj (𝟙_ C)) {A B : C} (e : A ≅ B)
    (h : (ρ_ (L.obj A)).hom = L.obj A ◁ η.hom ≫
      ((μ.app A).app (𝟙_ C)).hom ≫ L.map (ρ_ A).hom) :
    (ρ_ (L.obj B)).hom = L.obj B ◁ η.hom ≫
      ((μ.app B).app (𝟙_ C)).hom ≫ L.map (ρ_ B).hom := by
  let a := ρ_ (L.obj A)
  let b := whiskerLeftIso (L.obj A) η ≪≫ (μ.app A).app (𝟙_ C) ≪≫ L.mapIso (ρ_ A)
  have hab : a = b := Iso.ext h
  have hi : (ρ_ (L.obj A)).inv = L.map (ρ_ A).inv ≫
      ((μ.symm.app A).app (𝟙_ C)).hom ≫ L.obj A ◁ η.inv :=
    by simpa [a, b, Category.assoc] using congrArg Iso.inv hab
  have hj := Functor.OplaxMonoidal.oplax_right_unitality_of_iso μ.inv e hi
  let c := ρ_ (L.obj B)
  let d := whiskerLeftIso (L.obj B) η ≪≫ (μ.app B).app (𝟙_ C) ≪≫ L.mapIso (ρ_ B)
  have hcd : c.symm = d.symm := by
    apply Iso.ext
    simpa [c, d, Category.assoc] using hj
  exact congrArg Iso.hom (Iso.symm_eq_iff.mp hcd)

/-- The extended natural tensor comparison admits a unit isomorphism satisfying
both unit laws. The associativity law is not assumed or asserted here.
Source: Stacks Project, Cohomology, Tag 079U, lemma-pullback-tensor-product,
and section-derived-pullback; parent descent proof, step 3 (unit).
(blueprint: lem-pc-derived-pullback-tensor-unit).
Proof: take the structure sheaf concentrated in degree zero, which is K-flat and
represents the derived tensor unit with its recorded unit comparison. F sends the
underived tensor unit to the target tensor unit by mF. Apply Q to the unit isomorphism
of mF, then use the inverse of the supplied left-derived counit at this single complex;
that counit is invertible by comparison with the recorded K-flat computation.
Together with the source and target localization unit isomorphisms these maps give
an isomorphism η from the target derived unit to L of the source derived unit.
For a K-flat complex P, substitute the structure sheaf single complex and P into hμ.
Postcompose the proposed left unit identity with the invertible counit and localization
maps. On the summand of total degree n corresponding to (0,n), hφ reduces the identity
to left unitality of mF at P.X n. All other summands are zero. Coproduct extensionality
and cancellation give left unitality on Q(P). The same argument on summands (n,0),
using right unitality of mF, proves the right unit identity. Both sides are natural in
P, so K-flat resolutions transport these identities to every derived object.
This proof does not use the derived associativity law. -/
theorem derivedPullback_tensor_unit {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (hmap : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    [F.Additive]
    (mF : F.CoreMonoidal)
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)))
    (φ : ∀ P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _))
    (hφ : ∀ P N p q n (h : p + q = n),
          F.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor _)
              (ComplexShape.up ℤ) p q n h) ≫ (φ P N).hom.f n =
            (mF.μIso (P.X p) (N.X q)).inv ≫
              HomologicalComplex.ιMapBifunctor
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
                (curriedTensor _) (ComplexShape.up ℤ) p q n h)
    (μ : curriedTensorPre (derivedPullback g) ≅ curriedTensorPost (derivedPullback g))
    (hμ : ∀ P N : CochainComplex
            (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlatTensor (R := X.sheaf) P →
          CochainComplex.IsKFlatTensor (R := X.sheaf) N →
          ((μ.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj N)).hom ≫
              (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
              cast (by rfl) (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _)))) ≫
              DerivedCategory.Q.map (φ P N).hom =
            cast (by rfl) (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ⊗ₘ
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
    : ∃ η : 𝟙_ (schemeDerivedCategory T) ≅
        (derivedPullback g).obj (𝟙_ (schemeDerivedCategory X)),
        (∀ A : schemeDerivedCategory X,
          (λ_ ((derivedPullback g).obj A)).hom =
            η.hom ▷ (derivedPullback g).obj A ≫
              ((μ.app (𝟙_ (schemeDerivedCategory X))).app A).hom ≫
              (derivedPullback g).map (λ_ A).hom) ∧
        (∀ A : schemeDerivedCategory X,
          (ρ_ ((derivedPullback g).obj A)).hom =
            (derivedPullback g).obj A ◁ η.hom ≫
              ((μ.app A).app (𝟙_ (schemeDerivedCategory X))).hom ≫
              (derivedPullback g).map (ρ_ A).hom) := by
  have : IsIso (ε.app (𝟙_ (HomotopyCategory
      (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)))) :=
    derivedPullback_tensor_unit_counit_isIso g F hF hmap ε hε
  let η := derivedPullback_tensorUnitIso g F mF ε
  refine ⟨η, ?_, ?_⟩
  · intro A
    let Q := DerivedCategory.Q
      (C := SheafOfModules.{uModel} (moduleRings X.toRingedSpace))
    obtain ⟨P, s, hP, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolution (R := X.sheaf) (Q.objPreimage A)
    have : QuasiIso s := hs
    let e : Q.obj P ≅ A := asIso (Q.map s) ≪≫ Q.objObjPreimageIso A
    exact tensorUnit_left_of_iso (derivedPullback g) μ η e
      (derivedPullback_tensor_unit_kFlat g F hF hmap mF ε hε φ hφ μ hμ P hP).1
  · intro A
    let Q := DerivedCategory.Q
      (C := SheafOfModules.{uModel} (moduleRings X.toRingedSpace))
    obtain ⟨P, s, hP, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolution (R := X.sheaf) (Q.objPreimage A)
    have : QuasiIso s := hs
    let e : Q.obj P ≅ A := asIso (Q.map s) ≪≫ Q.objObjPreimageIso A
    exact tensorUnit_right_of_iso (derivedPullback g) μ η e
      (derivedPullback_tensor_unit_kFlat g F hF hmap mF ε hε φ hφ μ hμ P hP).2

end AlgebraicGeometry
