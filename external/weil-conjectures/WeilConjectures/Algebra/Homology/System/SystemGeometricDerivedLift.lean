/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.GeometricSystemOrdinaryData.SystemGeometricOrdinaryComparison
import WeilConjectures.Algebra.Homology.SmoothPurity.ExtensionEvaluationComparison
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Normalized derived lift of the geometric singleton comparison -/

set_option Elab.async false

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules
open MonoidalCategory
open scoped TensorProduct ChangeOfRings

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
  (u : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
  (I : ∀ n : ℕ, AlgebraicInverseImage u.inverse (BY.obj (op n)) (BX.obj (op n)))

variable {BY BX u I}
variable (SY : SystemScalarAssignment (J := J)) (TY : SystemTensorCoherence SY)
  (SX : SystemScalarAssignment (J := K)) (TX : SystemTensorCoherence SX)

/-- Lift an already specified ordinary singleton comparison to derived categories.
Source: Zheng, base-change sentence before Lemma 4.10, printed p. 23; Stacks 0FND.
(blueprint: lem-pur-system-geometric-derived-lift).

Proof: Localize the exact evaluation square using the exact-functor compositor.
Flat-term K-flat resolutions exist at each coefficient level, and geometric inverse
image preserves them by ringed-topos K-flat pullback followed by the identity scalar
unit. The normalized extension-evaluation comparison applied to the ordinary singleton
mate gives the derived isomorphism and its cochain representative. Apply the same
comparison to scalar restriction, with the good class restricted to flat-term K-flat
complexes, to obtain the scalar representative. The strict transition equation of F
localizes as an equation of whole-system natural transformations. Transpose through
the scalar and singleton derived adjunctions: their normalized below-level comparisons
give the lower-singleton square. At the selected level the ordinary multiplication
identity, the normalized derived tensor unit, and a resolving representative identify
the singleton adjunction unit with inverse multiplication. The mate unit identity
then gives derived multiplication. No detection of equality of derived maps by
evaluation is used. -/
theorem geometricSystemDerivedLift
    (F : GeometricSystemOrdinaryData BY BX u I)
    (ordinary : ∀ n : ℕ,
      systemSingleFunctor SY TY BY n ⋙ F.functor ≅
        F.levelInverseImage n ⋙ systemSingleFunctor SX TX BX n)
    (tensor : ∀ {j n : ℕ} (h : j ≤ n),
      systemTensor SY BY h ⋙ F.levelInverseImage j ≅
        F.levelInverseImage n ⋙ systemTensor SX BX h)
    (h_tensor_evaluation :
    (∀ {j n : ℕ} (h : j ≤ n) (P : systemLevel BY n),
    (F.evaluation j).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelInverseImage j).map ((systemSingleBelow SY TY BY n h).hom.app P) ≫
        (tensor h).hom.app P =
      ((ordinary n).hom.app P).app j ≫
        (systemSingleBelow SX TX BX n h).hom.app ((F.levelInverseImage n).obj P)))
    (h_tensor_generators :
    (∀ {j n : ℕ} (h : j ≤ n) (P : systemLevel BY n)
    (Z : Sheaf J (Type w))
    (b : Z ⟶ (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).obj (BY.obj (op j)))
    (x : Z ⟶ (geometricSystemUnderlying BY n).obj P)
    (z : Z ⟶ (geometricSystemUnderlying BY j).obj ((systemTensor SY BY h).obj P)),
    (∀ U t, z.hom.app U t =
      systemModelTmul (SY (BY.map (homOfLE h).op)).model P U
        (b.hom.app U t) (x.hom.app U t)) →
    ∀ (W : Dᵒᵖ) (t : (u.inverse.obj Z).obj.obj W),
      ((tensor h).hom.app P).val.app W
          (((u.inverse.map z) ≫
            (I j).moduleUnderlying.inv.app ((systemTensor SY BY h).obj P)).hom.app W t) =
        systemModelTmul (SX (BX.map (homOfLE h).op)).model
          ((F.levelInverseImage n).obj P) W
          (((u.inverse.map b) ≫ (I j).ringUnderlying.hom).hom.app W t)
          (((u.inverse.map x) ≫ (I n).moduleUnderlying.inv.app P).hom.app W t)))
    (h_above :
    (∀ (n j : ℕ) (h : n < j) (P : systemLevel BY n),
    ((ordinary n).hom.app P).app j = 0))
    (h_multiplication :
    (∀ (n : ℕ) (P : systemLevel BY n),
    ((ordinary n).hom.app P).app n ≫
        ((systemSingleBelow SX TX BX n (Nat.le_refl n) ≪≫ TX.ordinaryUnit BX n)).hom.app
          ((F.levelInverseImage n).obj P) =
      (F.evaluation n).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelInverseImage n).map
          ((systemSingleBelow SY TY BY n (Nat.le_refl n) ≪≫
            TY.ordinaryUnit BY n).hom.app P)))
    : ∃ (comparison : ∀ n : ℕ,
      (systemSingleDerivedExtension BY n SY TY).derived ⋙ F.functor.mapDerivedCategory ≅
        (F.levelInverseImage n).mapDerivedCategory ⋙
          (systemSingleDerivedExtension BX n SX TX).derived)
    (scalar : ∀ {n m : ℕ} (h : n ≤ m),
      systemDerivedTensor SY BY h ⋙ (F.levelInverseImage n).mapDerivedCategory ≅
        (F.levelInverseImage m).mapDerivedCategory ⋙ systemDerivedTensor SX BX h),
    (∀ (n : ℕ) (Q : CochainComplex (systemLevel BY n) ℤ),
    systemLevelKFlat BY n Q →
    (comparison n).hom.app (DerivedCategory.Q.obj Q) ≫
        (systemSingleDerivedExtension BX n SX TX).derived.map
          ((F.levelInverseImage n).mapDerivedCategoryFactors.hom.app Q) ≫
        (systemSingleDerivedExtension BX n SX TX).comparison.app
          (((F.levelInverseImage n).mapHomologicalComplex (.up ℤ)).obj Q) =
      F.functor.mapDerivedCategory.map
          ((systemSingleDerivedExtension BY n SY TY).comparison.app Q) ≫
        F.functor.mapDerivedCategoryFactors.hom.app
          (((systemSingleFunctor SY TY BY n).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (ordinary n) (.up ℤ)).hom.app Q)) ∧
    (∀ (n : ℕ) (P : DerivedCategory (systemLevel BY n)),
    (derivedSystemEvaluation BX n).map ((comparison n).hom.app P) ≫
        ((systemSingleDerivedBelow BX (Nat.le_refl n) SX TX ≪≫ TX.derivedUnit BX n)).hom.app
          ((F.levelInverseImage n).mapDerivedCategory.obj P) =
      (F.derivedEvaluation n).hom.app ((systemSingleDerivedExtension BY n SY TY).derived.obj P) ≫
        (F.levelInverseImage n).mapDerivedCategory.map
          ((systemSingleDerivedBelow BY (Nat.le_refl n) SY TY ≪≫
            TY.derivedUnit BY n).hom.app P)) ∧
    (∀ {n m : ℕ} (h : n ≤ m)
    (Q : CochainComplex (systemLevel BY m) ℤ), systemLevelKFlat BY m Q →
    (scalar h).hom.app (DerivedCategory.Q.obj Q) ≫
        (systemDerivedTensor SX BX h).map
          ((F.levelInverseImage m).mapDerivedCategoryFactors.hom.app Q) ≫
        (SX (BX.map (homOfLE h).op)).model.ε.app
          (((F.levelInverseImage m).mapHomologicalComplex (.up ℤ)).obj Q) =
      (F.levelInverseImage n).mapDerivedCategory.map
          ((SY (BY.map (homOfLE h).op)).model.ε.app Q) ≫
        (F.levelInverseImage n).mapDerivedCategoryFactors.hom.app
          (((systemTensor SY BY h).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (tensor h) (.up ℤ)).hom.app Q)) ∧
    (∀ {n m : ℕ} (h : n ≤ m)
    (P : DerivedCategory (systemLevel BY m)),
    F.functor.mapDerivedCategory.map
        (((systemSingleDerivedExtension BY n SY TY).adjunction.homEquiv _ _).symm
          ((systemSingleDerivedBelow BY h SY TY).inv.app P)) ≫
        (comparison m).hom.app P =
      (comparison n).hom.app ((systemDerivedTensor SY BY h).obj P) ≫
        (systemSingleDerivedExtension BX n SX TX).derived.map ((scalar h).hom.app P) ≫
        (((systemSingleDerivedExtension BX n SX TX).adjunction.homEquiv _ _).symm
          ((systemSingleDerivedBelow BX h SX TX).inv.app
            ((F.levelInverseImage m).mapDerivedCategory.obj P)))) := by
  sorry

end SheafOfModules
