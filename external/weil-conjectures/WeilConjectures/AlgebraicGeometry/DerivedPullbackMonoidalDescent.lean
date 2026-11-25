/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorAssociativity
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnit

/-! # Descent of coherent tensor pullback comparisons

Source: Stacks Project, Cohomology, Tag 079U and Section 20.27
(blueprint: lem-pc-derived-pullback-monoidal-descent).
-/

@[expose] public section

universe uModel wModel

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

noncomputable local instance pullbackDescentModuleTensor (S : Scheme.{uModel}) :
    MonoidalCategory (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.monoidalCategory S.sheaf

noncomputable local instance moduleSymmetric (S : Scheme.{uModel}) :
    SymmetricCategory (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.symmetricCategory S.sheaf

noncomputable local instance modulePreadditive (S : Scheme.{uModel}) :
    MonoidalPreadditive (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed S.sheaf).1

noncomputable local instance moduleClosed (S : Scheme.{uModel}) :
    MonoidalClosed (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed S.sheaf).2.1

local instance moduleGrothendieck (S : Scheme.{uModel}) :
    IsGrothendieckAbelian.{uModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings S.toRingedSpace)

local instance moduleResolutions (S : Scheme.{uModel}) :
    Abelian.HasFunctorialFlatResolution
      (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution S

local instance moduleDerivedMonoidal (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    Functor.HasDerivedMonoidalCategory
      (DerivedCategory.Qh (C := SheafOfModules.{uModel} (moduleRings S.toRingedSpace)))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uModel} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory _

noncomputable local instance pullbackDescentQLax (S : Scheme.{uModel})
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings S.toRingedSpace))] :
    Functor.LaxMonoidal
      (DerivedCategory.Q (C := SheafOfModules.{uModel} (moduleRings S.toRingedSpace))) :=
  inferInstance

attribute [local instance] tensorDescentPullbackDescentModuleTensor
  tensorDescentModuleSymmetric
  tensorDescentModulePreadditive
  tensorDescentModuleClosed
  tensorDescentModuleGrothendieck
  tensorDescentModuleResolutions
  tensorDescentModuleDerivedMonoidal
  tensorDescentPullbackDescentQLax

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Coherent termwise tensor comparisons descend along K-flat resolutions.
Source: Stacks Project, Cohomology, Tag 079U and Section 20.27
(blueprint: lem-pc-derived-pullback-monoidal-descent).
Proof: first restrict to K-flat complexes. Their tensor products are K-flat, their
pullbacks are K-flat, and the localization tensor maps are invertible there. The supplied
counit and complex comparison identify the left-derived tensor bifunctor with the tensor
of the two left-derived pullbacks. The left-derived universal property extends this
natural comparison to every derived object: on a K-flat pair write
A = L(μ_Q), B = ε_tensor followed by Q(φ), and C = (ε_P tensor ε_N) followed by μ_Q.
The tensorator is C followed by the inverse of B and then the inverse of A. Choose
K-flat resolutions of arbitrary arguments and use their comparison quasi-isomorphisms.
Naturality of ε and φ makes the result independent of
resolutions and natural in both arguments. The counit agrees with the recorded K-flat
computation by uniqueness of left-derived
functors, so it is invertible on K-flat inputs. All three maps A, B, C are invertible
by hiso and K-flat computation of each pullback. To check associativity, resolve three arguments by
K-flat complexes and precompose the total-complex diagrams with each triple summand
inclusion. The hypothesis hφ reduces the diagrams to associativity of mF; naturality
then descends equality through localization. Resolve the unit by the structure sheaf in
degree zero, which is K-flat; the unit comparison of mF and the derived counit give the
unit isomorphism. The same argument with summand inclusions gives both unit laws.
Package the inverse comparisons and this unit map as CoreMonoidal. The defining formula
on K-flat pairs is precisely the displayed equation, since the extension was made from
the supplied ε and φ. -/
theorem derivedPullback_monoidal_descent {T X : Scheme.{uModel}} (g : T ⟶ X)
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
    (hnatural : ∀ (P P' N N' : CochainComplex
              (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ)
            (a : P ⟶ P') (b : N ⟶ N'),
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (HomologicalComplex.mapBifunctorMap a b (curriedTensor _) (ComplexShape.up ℤ)) ≫
              (φ P' N').hom =
            (φ P N).hom ≫
              HomologicalComplex.mapBifunctorMap
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map b) (curriedTensor _)
                (ComplexShape.up ℤ))
    (hiso : ∀ P N : CochainComplex (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlatTensor (R := X.sheaf) P →
            CochainComplex.IsKFlatTensor (R := X.sheaf) N →
            IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
                (φ P N).hom)))
    : ∃ m : (derivedPullback g).CoreMonoidal,
        ∀ P N : CochainComplex
            (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
          CochainComplex.IsKFlatTensor (R := X.sheaf) P →
          CochainComplex.IsKFlatTensor (R := X.sheaf) N →
          (m.μIso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)).hom ≫
              (derivedPullback g).map (Functor.LaxMonoidal.μ DerivedCategory.Q P N) ≫
              cast (by rfl) (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _)))) ≫
              DerivedCategory.Q.map (φ P N).hom =
            cast (by rfl) (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ⊗ₘ
              ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) ≫
              Functor.LaxMonoidal.μ DerivedCategory.Q
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) := by
  obtain ⟨μ, hμ⟩ := derivedPullback_tensor_comparison_exists g F hF hmap ε hε
    φ hnatural hiso
  have hassoc := derivedPullback_tensor_associativity g F hF hmap mF ε hε φ hφ μ hμ
  obtain ⟨η, hleft, hright⟩ :=
    derivedPullback_tensor_unit g F hF hmap mF ε hε φ hφ μ hμ
  let m : (derivedPullback g).CoreMonoidal :=
    { εIso := η
      μIso A B := (μ.app A).app B
      μIso_hom_natural_left f A := NatTrans.congr_app (μ.hom.naturality f) A
      μIso_hom_natural_right A f := (μ.hom.app A).naturality f
      associativity := hassoc
      left_unitality := hleft
      right_unitality := hright }
  refine ⟨m, ?_⟩
  intro P N hP hN
  exact hμ P N hP hN

end AlgebraicGeometry
