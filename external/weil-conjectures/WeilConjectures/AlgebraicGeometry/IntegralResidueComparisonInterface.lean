/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients

/-! # Interface for coherent integral residue comparisons

Source: Bhatt--Scholze, Lemma 6.5.9(3), and associativity of derived coefficient change.
(auxiliary; not a blueprint node)
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_algebraicGeometryIntegralResidueComparisonInterface
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Ambient derived category used by the coefficient-comparison interface. -/
abbrev residueExchangeDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X))

/-- Derived pullback with its domain and codomain exposed explicitly. -/
@[irreducible] noncomputable def residueExchangeUpperStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeDerived Λ Y ⥤ residueExchangeDerived Λ X :=
  L((f)^*⟦Λ⟧)

/-- The actual derived coefficient reduction with its two categories exposed. -/
@[irreducible] noncomputable def residueExchangeReduction (X : Scheme.{u}) :
    residueExchangeDerived (integralCoeff ℓ E) X ⥤
      residueExchangeDerived
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) X :=
  integralReduction ℓ E X

/-- The library's canonical composition comparison, with typed pull functors. -/
@[irreducible] noncomputable def residueExchangeUpperStarComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    residueExchangeUpperStar Λ (f ≫ g) ≅
      residueExchangeUpperStar Λ g ⋙ residueExchangeUpperStar Λ f :=
  by
    unfold residueExchangeUpperStar
    exact leftDerivedUpperStarComp Λ f g

/-- Pullback comparisons for actual derived reduction, compatible with composition.
The data concern arbitrary schemes and morphisms, without constructibility or base change.
Source: Bhatt--Scholze, Remark 6.8.15, and associativity of derived tensor.
(auxiliary; not a blueprint node). -/
structure IntegralResiduePullComparisons where
  pull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    residueExchangeUpperStar (integralCoeff ℓ E) f ⋙ residueExchangeReduction ℓ E X ≅
      residueExchangeReduction ℓ E Y ⋙
        residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f
  comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Z))),
    (residueExchangeReduction ℓ E X).map
        ((residueExchangeUpperStarComp (integralCoeff ℓ E) f g).hom.app K) ≫
        (pull f).hom.app ((residueExchangeUpperStar (integralCoeff ℓ E) g).obj K) ≫
        (residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((pull g).hom.app K) =
      (pull (f ≫ g)).hom.app K ≫
        (residueExchangeUpperStarComp
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f g).hom.app
            ((residueExchangeReduction ℓ E Z).obj K)

namespace IntegralResiduePullComparisons

variable {ℓ E} (c : IntegralResiduePullComparisons.{u} ℓ E)

end IntegralResiduePullComparisons

namespace IntegralResiduePullComparisons

variable {ℓ E}

end IntegralResiduePullComparisons

end AlgebraicGeometry.ProEtale.CondensedRing
