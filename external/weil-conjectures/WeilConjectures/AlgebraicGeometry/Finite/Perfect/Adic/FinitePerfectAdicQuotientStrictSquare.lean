/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransition
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleModuleRestrictionConstantMap
public import WeilConjectures.SixFunctors.ProEtale.LocalizationRestrictionScalarMate

/-! # The strict square of the ordinary quotient arrows

Restriction along the finite quotient map `R_(n+1) → R_n` is compatible with the chart
coordinates of the two finite quotients, by a square which is the identity on sections. The
explicit quotient arrow is the chart image of the ring-level quotient transition followed by
this square.

Source: Stacks Project, Tags 03CY, 03DA and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Fixed scalar encoding of a module over a finite quotient ring: restriction to constant
scalars along `φ m`, followed by the constant-scalar encoding. -/
abbrev finitePerfectAdicFixedScalar (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n) (m : ℕ) :
    SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (completedAdicFiniteCommRing X d m)) ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (m + 1)))) :=
  SheafOfModules.restrictScalars.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (φ m)) ⋙
    proEtaleModuleRestriction X (A ⧸ d.ideal ^ (m + 1))

/-- The comparisons `φ` intertwine the constant and the actual quotient maps. -/
theorem finitePerfectAdic_constantQuotient_comm (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hcompat : FinitePerfectModelsCompatible X d φ) (n : ℕ) :
    (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (φ (n + 1)) ≫
      (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)) =
    (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (adicConstantMap X (adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _))) ≫
      (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (φ n) := by
  rw [← Functor.map_comp, ← Functor.map_comp, hcompat.1 n]

/-- The fixed scalar encodings of the two finite quotient rings are compatible with the
quotient maps; the comparison is the identity on sections. -/
def finitePerfectAdicFixedScalarStepIso (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hcompat : FinitePerfectModelsCompatible X d φ) (n : ℕ) :
    SheafOfModules.restrictScalars.{t + 1} ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
          (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))) ⋙
        finitePerfectAdicFixedScalar X d φ (n + 1) ≅
      finitePerfectAdicFixedScalar X d φ n ⋙ sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{t + 1}
          (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (SheafOfModules.restrictScalarsSquareIso _ _ _ _
      (finitePerfectAdic_constantQuotient_comm X d φ hcompat n))
        (proEtaleModuleRestriction X (A ⧸ d.ideal ^ (n + 1 + 1))) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (proEtaleModuleRestrictionConstantMapIso X
      (adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _))) ≪≫
    (Functor.associator _ _ _).symm

/-- The strict square comparing restriction along the quotient maps with the chart
coordinates of the two finite quotients. -/
def finitePerfectAdicQuotientStrictSquare (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hcompat : FinitePerfectModelsCompatible X d φ) (V : X.Etale) (n : ℕ) :
    TwoSquare (SheafOfModules.restrictScalars.{t + 1} ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
          (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))))
      (finitePerfectAdicFixedScalar X d φ n ⋙
        ProEtale.localizationRestriction (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))
          V.hom inferInstance)
      (finitePerfectAdicFixedScalar X d φ (n + 1) ⋙
        ProEtale.localizationRestriction
          (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))) V.hom inferInstance)
      (finitePerfectAdicStepRestrict X d V n) :=
  TwoSquare.vComp (finitePerfectAdicFixedScalarStepIso X d φ hcompat n).hom
    (ProEtale.localizationRestrictionRestrictScalarsSquare V.hom inferInstance
      (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))

/-- The explicit quotient arrow is the chart image of the ring-level quotient transition,
followed by the strict square. -/
theorem finitePerfectAdicQuotientStrictTransition_app (X : Scheme.{t}) {A : Type t}
    [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hcompat : FinitePerfectModelsCompatible X d φ) (V : X.Etale) (n : ℕ)
    (N : CompletedAdicModules X d) :
    (finitePerfectAdicQuotientStrictTransition X d φ hcompat V n).app N =
      (finitePerfectAdicFixedScalar X d φ (n + 1) ⋙
        ProEtale.localizationRestriction
          (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))) V.hom inferInstance).map
          ((completedAdicChangeQuotientTransition X d n).app N) ≫
        (finitePerfectAdicQuotientStrictSquare X d φ hcompat V n).app
          ((completedAdicChange X (completedAdicCommProjection X d n)).obj N) := by
  ext U x
  with_unfolding_all rfl


/-- The fixed scalar encoding is an equivalence when `φ m` is an isomorphism. -/
theorem finitePerfectAdicFixedScalar_isEquivalence (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (m : ℕ) :
    (finitePerfectAdicFixedScalar X d φ m).IsEquivalence := by
  have := SheafOfModules.restrictScalars_isEquivalence_of_isIso.{t + 1}
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map (φ m))
  have := proEtaleModuleRestriction_isEquivalence X (A ⧸ d.ideal ^ (m + 1))
  infer_instance

end AlgebraicGeometry.Scheme
