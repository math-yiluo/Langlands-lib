/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
import WeilConjectures.AlgebraicGeometry.ContinuousEtaleLocalLattices
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteEtaleLatticeDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor

/-! # Pullback systems for continuous lisse lattices

Source: Bhatt--Scholze, first paragraph of the proof of Lemma 6.8.13.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A system of pullback functors on integral (`Λ₀`) and rational (`Λ₁`) module objects along
maps of schemes, compatible with scalar extension along `φ` and preserving local freeness. -/
structure PullbackSystemCore
    (Λ₀ Λ₁ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    (φ : Λ₀ ⟶ Λ₁) [IsMonHom φ] where
  integral : ∀ {X Y : Scheme.{u}}, (Y ⟶ X) →
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Λ₀) X) ⥤
    Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Λ₀) Y)
  rational : ∀ {X Y : Scheme.{u}}, (Y ⟶ X) →
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Λ₁) X) ⥤
    Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Λ₁) Y)
  rationalIso : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
    rational f ≅ CondensedRing.upperStar (Λ₁) f
  scalar : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
    integral f ⋙ Mod.extendScalars (coefficientMap (φ) Y) ≅
      Mod.extendScalars (coefficientMap (φ) X) ⋙ rational f
  comp : ∀ {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X),
    rational (f ≫ g) ≅ rational g ⋙ rational f
  integralFree : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Λ₀) X)},
    IsLocallyFree _ M → IsLocallyFree _ ((integral f).obj M)
  rationalFree : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Λ₁) X)},
    IsLocallyFree _ P → IsLocallyFree _ ((rational f).obj P)

/-- The pullback system given by the pullbacks `f^*` of module objects. -/
noncomputable def canonicalPullbackSystemCore
    (Λ₀ Λ₁ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    (φ : Λ₀ ⟶ Λ₁) [IsMonHom φ] : PullbackSystemCore Λ₀ Λ₁ φ where
  integral := CondensedRing.upperStar Λ₀
  rational := CondensedRing.upperStar Λ₁
  rationalIso _ := Iso.refl _
  scalar := pullIso φ
  comp f g := upperStarComp Λ₁ f g
  integralFree := IsLocallyFree.upperStar Λ₀
  rationalFree := IsLocallyFree.upperStar Λ₁

/-- Along a commutative square `r ≫ p = q ≫ j`, an identification of the scalar extension of
`M` with `p^* P` transports to the pulled-back objects `M'` over `V` and `P'` over `W`. -/
noncomputable def pullbackSystem_scalarSquareIso
    (Λ₀ Λ₁ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    (φ : Λ₀ ⟶ Λ₁) [IsMonHom φ] (D : PullbackSystemCore Λ₀ Λ₁ φ)
    {X U V W : Scheme.{u}} (p : U ⟶ X) (j : W ⟶ X)
    (r : V ⟶ U) (q : V ⟶ W) (w : r ≫ p = q ≫ j)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₁ X))
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ₀ U))
    (P' : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ₁ W))
    (M' : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ₀ V))
    (iP : P' ≅ (D.rational j).obj P) (iM : M' ≅ (D.integral r).obj M)
    (e : (Mod.extendScalars (coefficientMap φ U)).obj M ≅
      (CondensedRing.upperStar Λ₁ p).obj P) :
    (Mod.extendScalars (coefficientMap φ V)).obj M' ≅ (D.rational q).obj P' :=
  (Mod.extendScalars (coefficientMap φ V)).mapIso iM ≪≫
    (D.scalar r).app M ≪≫
    (D.rational r).mapIso (e ≪≫ (D.rationalIso p).symm.app P) ≪≫
    (D.comp r p).symm.app P ≪≫
    eqToIso (congrArg (fun f ↦ (D.rational f).obj P) w) ≪≫
    (D.comp q j).app P ≪≫ (D.rational q).mapIso iP.symm

/-- Pullback systems for the coefficients `𝒪_E ⟶ E`. -/
abbrev PullbackSystem
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] :=
  PullbackSystemCore (integralCoeff ℓ E) (Profinite.continuousMapRingObj E)
    (integralScalarMap ℓ E)

/-- The pullback system given by the pullbacks `f^*` of module objects over `𝒪_E` and `E`. -/
noncomputable def canonicalPullbackSystem
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] :
    PullbackSystem.{u} ℓ E :=
  canonicalPullbackSystemCore _ _ (integralScalarMap ℓ E)

end AlgebraicGeometry.ProEtale.CondensedRing
