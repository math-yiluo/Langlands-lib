/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteProperQuotient.FiniteProperExceptionalQuotient
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FiniteCoefficients.Constant
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Hom

/-! # The full derived finite exceptional Hom comparison

Source: Zheng, Proposition 2.23; blueprint coherent-tower proof, step 5.
(blueprint: def-sfb-finite-exceptional-derived-hom).

The comparison is defined by closed transposition of the actual proper projection
map. Its isomorphism theorem does not define its data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.FiniteProperQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Full A_n-module valued global RHom, with the usual constant/sections adjunction.
Source: Stacks 0B6E (blueprint: def-sfb-finite-exceptional-derived-hom). -/
def finiteHom (T : Scheme.{u}) (n : ℕ)
    (M : DerivedCategoryModule (Ring l E n) T) :=
  (derivedHom (ModuleCat.{u + 1} (Ring l E n)) T).obj (op M) ⋙
    rightDerivedGlobalSections (ModuleCat.{u + 1} (Ring l E n)) T

/-- The scalar-test functor whose right adjoint is finiteHom.
Source: Stacks 08J9 (blueprint: def-sfb-finite-exceptional-derived-hom). -/
def finiteTensorTest (T : Scheme.{u}) (n : ℕ)
    (M : DerivedCategoryModule (Ring l E n) T) :=
  (constantSheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} (Ring l E n))).mapDerivedCategory ⋙
      (derivedTensor (ModuleCat.{u + 1} (Ring l E n)) T).obj M

/-- The canonical, fully derived scalar tensor/global Hom adjunction.
Source: Stacks 08J9 (blueprint: def-sfb-finite-exceptional-derived-hom). -/
def finiteHomAdjunction (T : Scheme.{u}) (n : ℕ)
    (M : DerivedCategoryModule (Ring l E n) T) :
    finiteTensorTest l E T n M ⊣ finiteHom l E T n M :=
  (derivedConstantSheafAdjunction (ModuleCat.{u + 1} (Ring l E n)) T).comp
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} (Ring l E n)) M)

/-- Proper projection tested on every derived scalar complex. All maps here
are the actual counit projection and the canonical pullback of constants.
Source: Zheng 2.23 (blueprint: def-sfb-finite-exceptional-derived-hom). -/
def finiteHomProjection {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ)
    (M : DerivedCategoryModule (Ring l E n) Z) :
    finiteTensorTest l E Y n ((F l E p n).obj M) ⟶
      finiteTensorTest l E Z n M ⋙ F l E p n :=
  Functor.whiskerLeft _ ((rightDerivedLowerStarProjectionMap
    (ModuleCat.{u + 1} (Ring l E n)) p).app M) ≫
  Functor.whiskerRight
    (Functor.whiskerRight
      (derivedConstantSheafCompLeftDerivedUpperStarIso
        (ModuleCat.{u + 1} (Ring l E n)) p).hom
      ((derivedTensor (ModuleCat.{u + 1} (Ring l E n)) Z).obj M))
    (F l E p n)

/-- The inverse-direction finite enriched adjunction map is a genuine mate.
It is defined for every chosen F_n ⊣ G_n, including a noncanonical presentation
of that same adjunction. Source: Zheng 2.23
(blueprint: def-sfb-finite-exceptional-derived-hom). -/
def finiteHomMate {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ)
    (G : DerivedCategoryModule (Ring l E n) Y ⥤
      DerivedCategoryModule (Ring l E n) Z) (adj : F l E p n ⊣ G)
    (M : DerivedCategoryModule (Ring l E n) Z) :
    G ⋙ finiteHom l E Z n M ⟶ finiteHom l E Y n ((F l E p n).obj M) :=
  conjugateEquiv ((finiteHomAdjunction l E Z n M).comp adj)
    (finiteHomAdjunction l E Y n ((F l E p n).obj M))
    (finiteHomProjection l E p n M)

/-- Finite global RHom with its original O-action, by the actual quotient map.
Source: Stacks 0B6E; Zheng, Construction 4.1
(blueprint: def-sfb-finite-exceptional-derived-hom). -/
def finiteHomScalars (T : Scheme.{u}) (n : ℕ)
    (M : DerivedCategoryModule (Ring l E n) T) :=
  finiteHom l E T n M ⋙
    (ModuleCat.restrictScalars.{u + 1}
      (Ideal.Quotient.mk (Ideal.span
        ({(l : Padic.coefficientExtensionIntegers l E) ^ (n + 1)} :
          Set (Padic.coefficientExtensionIntegers l E))))).mapDerivedCategory

/-- The full finite derived Hom bifunctor with the original O-action.
Source: Stacks 0B6E; Zheng, Proposition 2.23
(blueprint: def-sfb-finite-exceptional-derived-hom). -/
def finiteHomScalarsBifunctor (T : Scheme.{u}) (n : ℕ) :=
  Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} (Ring l E n)) T) ⋙
    rightDerivedGlobalSections (ModuleCat.{u + 1} (Ring l E n)) T ⋙
    (ModuleCat.restrictScalars.{u + 1}
      (Ideal.Quotient.mk (Ideal.span
        ({(l : Padic.coefficientExtensionIntegers l E) ^ (n + 1)} :
          Set (Padic.coefficientExtensionIntegers l E))))).mapDerivedCategory

/-- The same finite enriched adjunction mate with O-scalars retained.
Source: Zheng, Proposition 2.23 and Construction 4.1
(blueprint: def-sfb-finite-exceptional-derived-hom). -/
def finiteHomScalarsMate {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ)
    (G : DerivedCategoryModule (Ring l E n) Y ⥤
      DerivedCategoryModule (Ring l E n) Z) (adj : F l E p n ⊣ G)
    (M : DerivedCategoryModule (Ring l E n) Z) :
    G ⋙ finiteHomScalars l E Z n M ⟶
      finiteHomScalars l E Y n ((F l E p n).obj M) :=
  Functor.whiskerRight (finiteHomMate l E p n G adj M) _

end AlgebraicGeometry.Etale.FiniteProperQuotient
