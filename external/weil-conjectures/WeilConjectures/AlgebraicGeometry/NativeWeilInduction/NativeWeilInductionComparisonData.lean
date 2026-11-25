/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.CategoryTheory.Endofunctor.FreeDerivedWeilResolution
public import WeilConjectures.AlgebraicGeometry.Native.NativeAdicCompactSupportSums
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Native ordinary derived Weil induction and compact supports

All functors below are on ordinary unbounded derived categories. The localized structure
map is a natural transformation out of derived forgetting; no equivalence between derived
Weil objects and fixed pairs in the ordinary derived category is asserted.

## References

* Stacks Project, Tags 079P, 08BJ and 070Y
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

attribute [instance] AlgebraicGeometry.Compactification.over

namespace AlgebraicGeometry.NativeWeilInduction

section ExactComparisons

variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{w} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]

/-- Localize the actual termwise identity underlying an exact lifted functor. -/
def exactForgetComparison (P : C ⥤ C) (Q : D ⥤ D) [P.Additive] [Q.Additive]
    [P.IsEquivalence] [Q.IsEquivalence] (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [HasDerivedCategory.{w} (IsoAlgebra P)] [HasDerivedCategory.{w} (IsoAlgebra Q)]
    (e : L ⋙ Q ≅ P ⋙ L) :
    (IsoAlgebra.mapOfNatIso e).mapDerivedCategory ⋙
        (IsoAlgebra.forget Q).mapDerivedCategory ≅
      (IsoAlgebra.forget P).mapDerivedCategory ⋙ L.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (IsoAlgebra.mapOfNatIsoCompForgetIso e) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Derive the native exchange using exact Frobenius equivalences and the specified
right-derived units. -/
def rightExchange (P : C ⥤ C) (Q : D ⥤ D) [P.Additive] [Q.Additive]
    [P.IsEquivalence] [Q.IsEquivalence] [Abelian.HasKInjectiveResolutions C]
    (L : C ⥤ D) [L.Additive] (e : L ⋙ Q ≅ P ⋙ L) :
    L.rightDerivedFunctor ⋙ Q.mapDerivedCategory ≅
      P.mapDerivedCategory ⋙ L.rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso L Q).symm ≪≫
    Functor.rightDerivedFunctorNatIso e ≪≫ Functor.rightDerivedFunctorCompIso P L ≪≫
      Functor.isoWhiskerRight P.rightDerivedFunctorIsoMapDerivedCategory L.rightDerivedFunctor

/-- The normalization equation for localization of an exact native lifted square. -/
def exactForgetNormalization (P : C ⥤ C) (Q : D ⥤ D) [P.Additive] [Q.Additive]
    [P.IsEquivalence] [Q.IsEquivalence] (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [HasDerivedCategory.{w} (IsoAlgebra P)] [HasDerivedCategory.{w} (IsoAlgebra Q)]
    (e : L ⋙ Q ≅ P ⋙ L) : Prop :=
  ∀ K : CochainComplex (IsoAlgebra P) ℤ,
    (exactForgetComparison P Q L e).hom.app (_root_.DerivedCategory.Q.obj K) ≫
      L.mapDerivedCategory.map ((IsoAlgebra.forget P).mapDerivedCategoryFactors.hom.app K) ≫
      L.mapDerivedCategoryFactors.hom.app
        (((IsoAlgebra.forget P).mapHomologicalComplex (.up ℤ)).obj K) =
    (IsoAlgebra.forget Q).mapDerivedCategory.map
        ((IsoAlgebra.mapOfNatIso e).mapDerivedCategoryFactors.hom.app K) ≫
      (IsoAlgebra.forget Q).mapDerivedCategoryFactors.hom.app
        (((IsoAlgebra.mapOfNatIso e).mapHomologicalComplex (.up ℤ)).obj K)

/-- Exact localization preserves the literal underlying square. -/
theorem exactForgetNormalization_proof
    (P : C ⥤ C) (Q : D ⥤ D) [P.Additive] [Q.Additive]
    [P.IsEquivalence] [Q.IsEquivalence] (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [HasDerivedCategory.{w} (IsoAlgebra P)] [HasDerivedCategory.{w} (IsoAlgebra Q)]
    (e : L ⋙ Q ≅ P ⋙ L) : exactForgetNormalization P Q L e := by
  intro K
  dsimp only [exactForgetComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors]
  rw [Functor.mapDerivedCategoryNatIso_fac]
  have h : (_root_.DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex
        (IsoAlgebra.mapOfNatIsoCompForgetIso e).hom (.up ℤ)).app K)) = 𝟙 _ := by
    change _root_.DerivedCategory.Q.map (𝟙 _) = _
    exact CategoryTheory.Functor.map_id _ _
  erw [h, Category.comp_id]
  erw [← Functor.mapDerivedCategoryCompIso_hom_app_factors
    (IsoAlgebra.mapOfNatIso e) (IsoAlgebra.forget Q) K]
  simp only [Iso.hom_inv_id_app_assoc]

end ExactComparisons

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- The specified ordinary derived Frobenius pullback. -/
abbrev frobenius (T : Scheme.{u}) [T.Over (Spec (.of k₀))] :=
  (WeilSheaf.frobeniusPullback k₀ l T).mapDerivedCategory

/-- Ordinary derived forgetting. -/
abbrev forget (T : Scheme.{u}) [T.Over (Spec (.of k₀))] :=
  (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)).mapDerivedCategory

/-- Exact free induction from the recorded ordinary derived adjunction. -/
abbrev induction (T : Scheme.{u}) [T.Over (Spec (.of k₀))] :=
  (IsoAlgebra.Free.functor (WeilSheaf.frobeniusPullback k₀ l T)).mapDerivedCategory

/-- The localized structure isomorphism, natural on all derived Weil morphisms. -/
def structureIso (T : Scheme.{u}) [T.Over (Spec (.of k₀))] :
    forget k₀ l T ⋙ frobenius k₀ l T ≅ forget k₀ l T :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (IsoAlgebra.strNatIso (WeilSheaf.frobeniusPullback k₀ l T))

/-- The canonical integer coprojection: iterate the localized free structure on the
zeroth coprojection, the actual derived adjunction unit. This does not identify categories. -/
def inclusion (T : Scheme.{u}) [T.Over (Spec (.of k₀))]
    (A : _root_.DerivedCategory
      (ProEtale.AdicSheaf l (T ↘ Spec (.of k₀)).geometricFiber)) (n : ℤ) :
    IsoAlgebra.Free.obj (frobenius k₀ l T) A n ⟶
      (forget k₀ l T).obj ((induction k₀ l T).obj A) :=
  IsoAlgebra.Free.hom
    (IsoAlgebra.mk _ ((structureIso k₀ l T).app ((induction k₀ l T).obj A)))
    ((IsoAlgebra.freeWeilDerivedAdjunction
      (WeilSheaf.frobeniusPullback k₀ l T)).unit.app A) n

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k₀))] (c : Compactification f)

/-- The actual ordinary compact-support composite on geometric fibres, with native
coefficient maps. -/
abbrev ordinaryImage :=
  (ProEtale.adicOpenImmersionLowerShriek l
    (Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (.of k₀))))).mapDerivedCategory ⋙
  (ProEtale.adicLowerStar l
    (Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (.of k₀))))).rightDerivedFunctor

/-- The proper comparison is the canonical right-derived lifted-functor comparison. -/
def properComparison :
    (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor ⋙ forget k₀ l Y ≅
      forget k₀ l c.Z ⋙ (ProEtale.adicLowerStar l
        (Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (.of k₀))))).rightDerivedFunctor :=
  letI := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (.of k₀)).geometricFiber) ℤ
  letI := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (.of k₀)).geometricFiber) ℤ
  IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso
    (WeilSheaf.frobeniusPullback k₀ l c.Z)
    (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g (Spec (.of k₀))))

/-- The open comparison localizes the actual termwise identity on objects and maps. -/
def openComparison :
    (ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory ⋙ forget k₀ l c.Z ≅
      forget k₀ l X ⋙ (ProEtale.adicOpenImmersionLowerShriek l
        (Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (.of k₀))))).mapDerivedCategory :=
  exactForgetComparison _ _ _
    (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso
      l c.i (comp_over c.i (Spec (.of k₀))))

/-- The specified beta, the proper comparison whiskered by open extension and then
composed with the termwise open comparison. -/
def comparison :
    ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c ⋙ forget k₀ l Y ≅
      forget k₀ l X ⋙ ordinaryImage k₀ l f c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (properComparison k₀ l f c) ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (openComparison k₀ l f c) _ ≪≫
          Functor.associator _ _ _

/-- The native first Frobenius exchange, derived from the actual proper and open
sheaf exchanges. -/
def exchange :
    ordinaryImage k₀ l f c ⋙ frobenius k₀ l Y ≅
      frobenius k₀ l X ⋙ ordinaryImage k₀ l f c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (rightExchange _ _ _
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso
        l c.g (comp_over c.g (Spec (.of k₀))))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso
          (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso
            l c.i (comp_over c.i (Spec (.of k₀)))) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm) _ ≪≫
    Functor.associator _ _ _

/-- Structural clauses for each of the three native hearts and its derived forgetful
functor; constructibility uses the existing locally stratified finite-free predicate. -/
def HeartProperties (T : Scheme.{u}) [T.Over (Spec (.of k₀))] : Prop :=
  IsGrothendieckAbelian.{u + 1}
      (ProEtale.AdicSheaf l (T ↘ Spec (.of k₀)).geometricFiber) ∧
    IsGrothendieckAbelian.{u + 1} (ProEtaleWeilSheaf k₀ l T) ∧
    PreservesFiniteLimits (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)) ∧
    PreservesFiniteColimits (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)) ∧
    (forget k₀ l T).IsTriangulated ∧ (forget k₀ l T).ReflectsIsomorphisms ∧
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)).PreservesKInjectiveComplexes ∧
    (∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J) (forget k₀ l T)) ∧
    (∀ A, ProEtale.DerivedCategory.boundedAdicConstructible l
      (T ↘ Spec (.of k₀)).geometricFiber A →
      ProEtale.DerivedCategory.boundedAdicConstructible l
        (T ↘ Spec (.of k₀)).geometricFiber ((frobenius k₀ l T).obj A)) ∧
    (∀ A, ProEtale.nativeAdicConstructibleLocalizingHull l
      (T ↘ Spec (.of k₀)).geometricFiber A →
      ProEtale.nativeAdicConstructibleLocalizingHull l
        (T ↘ Spec (.of k₀)).geometricFiber ((frobenius k₀ l T).obj A)) ∧
    ∀ A : _root_.DerivedCategory
      (ProEtale.AdicSheaf l (T ↘ Spec (.of k₀)).geometricFiber),
      Nonempty (IsColimit (Cofan.mk
        ((forget k₀ l T).obj ((induction k₀ l T).obj A)) (inclusion k₀ l T A)))

/-- Identity on the common proper K-injective model, expressed with the actual units
and localization factors. The underlying sheaf square is literally equal on maps too. -/
def ProperNormalization : Prop :=
  ∀ J : CochainComplex (ProEtaleWeilSheaf k₀ l c.Z) ℤ, J.IsKInjective →
    (forget k₀ l Y).map
        ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) ≫
      (properComparison k₀ l f c).hom.app
        (_root_.DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) ≫
      (ProEtale.adicLowerStar l
        (Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (.of k₀))))).rightDerivedFunctor.map
        ((IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l c.Z)).mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) =
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategoryFactorsh.hom.app
        (((ProEtaleWeilSheaf.lowerStar k₀ l c.g).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) ≫
      (ProEtale.adicLowerStar l
        (Scheme.Hom.geometricFiberMap c.g
          (comp_over c.g (Spec (.of k₀))))).rightDerivedFunctorUnit.app
        (((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l c.Z)).mapHomotopyCategory
          (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj J))

/-- The open comparison is the termwise identity, expressed through the two exact
localization factorizations. -/
def OpenNormalization : Prop :=
  exactForgetNormalization _ _ _
    (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso
      l c.i (comp_over c.i (Spec (.of k₀))))

end AlgebraicGeometry.NativeWeilInduction
