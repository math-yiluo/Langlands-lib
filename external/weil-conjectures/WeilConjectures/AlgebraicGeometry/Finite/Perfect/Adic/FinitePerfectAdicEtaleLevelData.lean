/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerData
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Single finite-level etale descent and its algebraic geometric fibre

Source: Stacks Project, Tags 09C6, 09AL, 09B1 and 03PT.
(blueprint: def-weil-pbc-finite-perfect-adic-etale-level-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The exact derived geometric stalk in the finite coefficient universe.
Source: Stacks Tag 03Q3; exactness of geometric stalks and Tag 05RU.
(blueprint: def-weil-pbc-finite-perfect-adic-etale-level-data). -/
def finitePerfectAdicEtaleStalk (Y : Scheme.{t}) (B : Type (t + 1)) [CommRing B]
    (y : Y) : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} B)) ⥤
      DerivedCategory (ModuleCat.{t + 1} B) :=
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    ((Y.uliftPointSmallEtale y).sheafFiber (A := ModuleCat.{t + 1} B))
    (Functor.additive_of_preserves_binary_products _) _ _

/-- Lift the module universe and transport coefficients along the ULift ring equivalence.
This is an exact functor on the chosen derived localizations, constructed termwise.
Source: Stacks Tag 05RU and Mathlib's exact module-universe lift.
(blueprint: def-weil-pbc-finite-perfect-adic-etale-level-data). -/
def finitePerfectAdicAlgebraLift (B : Type t) [CommRing B] :
    DerivedCategory (ModuleCat.{t} B) ⥤
      DerivedCategory (ModuleCat.{t + 1} (ULift.{t + 1} B)) :=
  have : (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B)).isEquivalence_functor
  have : PreservesLimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom) :=
    Adjunction.isEquivalencePreservesLimits _
  have : PreservesColimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom) :=
    Adjunction.isEquivalence_preservesColimits _
  (ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).mapDerivedCategory

/-- A single descended finite quotient, with a perfect small-universe geometric fibre.

The comparison transports any supplied constant model, not merely the chosen fibre.
There are no comparisons between different coefficient levels in these data.
Source: Stacks Tags 09AL and 09B1; the single-level descent in Tag 09C6.
(blueprint: def-weil-pbc-finite-perfect-adic-etale-level-data). -/
structure FinitePerfectAdicEtaleLevelData (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale) (v : V.left)
    (n : ℕ) where
  level : DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))))
  bounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) q).obj level)
  lisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) q).obj level)
  algebra : DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1)))
  perfect : DerivedCategory.IsPerfect algebra
  stalk : Nonempty ((finitePerfectAdicEtaleStalk V.left _ v).obj level ≅
    (finitePerfectAdicAlgebraLift _).obj algebra)
  transport : ∀ (U : V.left.Etale)
    (F : DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1)))), Nonempty
      ((AlgebraicGeometry.Etale.upperStar
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) U.hom).mapDerivedCategory.obj
          level ≅
        (constantSheaf U.left.smallEtaleTopology
          (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))).mapDerivedCategory.obj
            ((finitePerfectAdicAlgebraLift _).obj F)) →
    ∀ (W : X.Etale), (W ⟶ Etale.mk (U.hom ≫ V.hom)) → Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicQuotientReduction X d n).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicDerivedChange X (φ n)).obj
            ((finitePerfectAdicDerivedConstant X (A ⧸ d.ideal ^ (n + 1))).obj F)))

end AlgebraicGeometry.Scheme
