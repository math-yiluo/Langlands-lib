/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorProduct
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalDescent
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensorCoherence

/-! # The canonical monoidal model of derived pullback

Source: Stacks Project, Cohomology, Tag 079U and Section 20.27
(blueprint: def-pc-derived-pullback-monoidal-model).
-/

@[expose] public section

universe uModel wModel

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

attribute [local instance] pullbackDescentModuleTensor moduleSymmetric modulePreadditive
  moduleClosed moduleGrothendieck moduleResolutions moduleDerivedMonoidal pullbackDescentQLax

/-- A monoidal structure on derived pullback is induced by the recorded module tensor
comparison when its left-derived counit is compatible with the tensor comparisons.
The module tensor comparison is pinned to `module_pullback_tensor`;
the unit is then fixed by its unit laws.
Source: Stacks Project, Cohomology, Tag 079U and Section 20.27
(blueprint: def-pc-derived-pullback-monoidal-model). -/
def IsDerivedPullbackMonoidalModel {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))]
    (m : (derivedPullback g).CoreMonoidal) : Prop := by
  letI := pullbackDescentModuleTensor X
  letI := pullbackDescentModuleTensor T
  letI := moduleSymmetric X
  letI := moduleSymmetric T
  haveI := modulePreadditive X
  haveI := modulePreadditive T
  letI := moduleClosed X
  letI := moduleClosed T
  haveI := moduleGrothendieck X
  haveI := moduleGrothendieck T
  haveI := moduleResolutions X
  haveI := moduleResolutions T
  haveI := moduleDerivedMonoidal X
  haveI := moduleDerivedMonoidal T
  letI := m.toMonoidal
  exact ∃ (F : SheafOfModules.{uModel} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{uModel} (moduleRings T.toRingedSpace))
    (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
    (_ : ∀ {M N} (a : M ⟶ N),
      F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
        eqToHom (hF N).symm)
    (_ : F.Additive) (mF : F.CoreMonoidal),
    (∀ M N, (mF.μIso M N).inv = eqToHom (hF _) ≫
      ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) M N).hom ≫
      (eqToHom (hF M).symm ⊗ₘ eqToHom (hF N).symm)) ∧
    ∃ ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh,
      (derivedPullback g).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)) ∧
      ∃ φ : ∀ P N : CochainComplex
          (SheafOfModules.{uModel} (moduleRings X.toRingedSpace)) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
          CochainComplex.mapBifunctor
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _),
        (∀ P N p q n (h : p + q = n),
          F.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor _)
              (ComplexShape.up ℤ) p q n h) ≫ (φ P N).hom.f n =
            (mF.μIso (P.X p) (N.X q)).inv ≫
              HomologicalComplex.ιMapBifunctor
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
                (curriedTensor _) (ComplexShape.up ℤ) p q n h) ∧
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
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)

private theorem reassoc_pinned {C : Type*} [Category C] {A B D E G : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E} {d : E ⟶ G}
    {t : A ⟶ E} {s : A ⟶ G} (ht : t = a ≫ b ≫ c)
    (hs : s = a ≫ b ≫ c ≫ d) : s = t ≫ d := by
  rw [ht]
  simpa only [Category.assoc] using hs

/-- The canonical module tensor comparison descends to a monoidal model of derived pullback.
Statements that use the model quantify over every `m` with
`IsDerivedPullbackMonoidalModel g m` rather than choosing one.
Source: Stacks Project, Cohomology, Tag 079U and Section 20.27
(blueprint: def-pc-derived-pullback-monoidal-model).
Proof: resolve both arguments by K-flat complexes using lem-pc-kflat-resolution.
Termwise pullback preserves K-flatness by lem-pc-kflat-pullback-preservation.
Use the degreewise module comparison of lem-pc-derived-pullback-tensor-product.
Its associativity and unit laws follow from the tensor formula for module pullback.
The left-derived universal property descends these comparisons and laws, and makes the
counit monoidal. The unit complex is K-flat, so its comparison is invertible too. -/
theorem exists_derivedPullbackMonoidalModel {T X : Scheme.{uModel}} (g : T ⟶ X)
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wModel} (SheafOfModules.{uModel} (moduleRings T.toRingedSpace))] :
    ∃ m : (derivedPullback g).CoreMonoidal, IsDerivedPullbackMonoidalModel g m := by
  classical
  obtain ⟨F, hF, hmap, hAdd, ε, hε, φ, hφ, hnatural, hiso⟩ :=
    derivedPullback_tensorProduct.{uModel, wModel} g
  have := hAdd
  obtain ⟨mF, hμ⟩ := modulePullback_tensor_coherent.{uModel} g F hF hmap
  obtain ⟨m, hm⟩ :=
    derivedPullback_monoidal_descent.{uModel, wModel}
      g F hF hmap mF ε hε φ (by
        intro P N p q n h
        exact reassoc_pinned (hμ (P.X p) (N.X q)) (hφ P N p q n h)) hnatural hiso
  refine ⟨m, F, hF, hmap, hAdd, mF, hμ, ε, hε, φ, ?_, hm⟩
  intro P N p q n h
  exact reassoc_pinned (hμ (P.X p) (N.X q)) (hφ P N p q n h)

end AlgebraicGeometry
