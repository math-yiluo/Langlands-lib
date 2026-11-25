/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDg.RingedSiteDgModules
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Quotient
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.Monoidal

/-!
# Homotopy triangulation and quasi-isomorphism system for sheaf dg modules

Source: Stacks Project, `sdga.tex`, Tags 0FS7, 0FT2 and 0FT4, with the cone
convention of Tag 0FS5 (blueprint: lem-sfb-sheaf-dg-homotopy-system).

The declarations below record the right-module homotopy quotient, its signed
shifts and mapping-cone triangles, and the localization data used by the
sheaf dg scalar-adjunction theorem.  They use the canonical ringed-site dg
module and sheaf tensor declarations; no second module category is defined.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false

universe c v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalOpposite CategoryTheory.Pretriangulated

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (O : Sheaf J CommRingCat.{u})

variable {O}

/-- Right graded linearity of a degree `-1` homotopy. Source: Stacks `sdga.tex`,
section-homotopy (blueprint: lem-sfb-sheaf-dg-homotopy-system). -/
def homotopyRightLinear {A : Algebra O} {M N : Module A}
    {f g : M ⟶ N} (h : Homotopy ((underlying A).map f) ((underlying A).map g)) : Prop :=
  ∀ (p q : ℤ), HEq
    (actionDegree M p q (p + q) rfl ≫ h.hom (p + q) (p + q - 1))
    ((h.hom p (p - 1) ▷ A.X.X q) ≫
      actionDegree N (p - 1) q ((p - 1) + q) rfl)

/-- The action-preserving chain-homotopy relation on right dg modules. Source:
Stacks `sdga.tex`, definition-homotopy (blueprint: lem-sfb-sheaf-dg-homotopy-system). -/
def homotopyRel (A : Algebra O) : HomRel (Module A) :=
  fun _M _N f g ↦ ∃ h : Homotopy ((underlying A).map f) ((underlying A).map g),
    homotopyRightLinear h

/-- The right dg-module homotopy category `K(A)`. Source: Stacks `sdga.tex`,
section-homotopy (blueprint: lem-sfb-sheaf-dg-homotopy-system). -/
abbrev HomotopyCategory (A : Algebra O) :=
  CategoryTheory.Quotient (homotopyRel A)

/-- The quotient functor from right dg modules to `K(A)`. Source: Stacks `sdga.tex`,
section-homotopy (blueprint: lem-sfb-sheaf-dg-homotopy-system). -/
abbrev homotopyQuotient (A : Algebra O) : Module A ⥤ HomotopyCategory A :=
  CategoryTheory.Quotient.functor (homotopyRel A)

/-- Signed shifts and the specified mapping-cone triangles on `K(A)`. Source:
Stacks `sdga.tex`, Tags 0FRY, 0FS5 and 0FS7 (blueprint: lem-sfb-sheaf-dg-homotopy-system).
-/
class HomotopyStructure (A : Algebra O) where
  [preadditive : Preadditive (HomotopyCategory A)]
  [zero : HasZeroObject (HomotopyCategory A)]
  [shift : HasShift (HomotopyCategory A) ℤ]
  [shiftAdditive : ∀ n : ℤ, (shiftFunctor (HomotopyCategory A) n).Additive]
  [pretriangulated : Pretriangulated (HomotopyCategory A)]
  [triangulated : IsTriangulated (HomotopyCategory A)]
  shifts_exist (n : ℤ) (M : Module A) :
    ∃ S : Module A, Nonempty (ShiftComparison A n M S)
  cones_exist {M N : Module A} (f : M ⟶ N) :
    ∃ (K S : Module A) (s : ShiftComparison A 1 M S) (g : N ⟶ K) (h : K ⟶ S),
      Nonempty (ConeComparison A f K S s g h)
  shiftIso (n : ℤ) (M S : Module A) (e : ShiftComparison A n M S) :
    (homotopyQuotient A).obj S ≅ ((homotopyQuotient A).obj M)⟦n⟧
  shift_natural (n : ℤ) (M N S V : Module A)
      (eM : ShiftComparison A n M S) (eN : ShiftComparison A n N V)
      (f : M ⟶ N) (g : S ⟶ V)
      (comm : (underlying A).map g ≫ eN.iso.hom =
        eM.iso.hom ≫ ((underlying A).map f)⟦n⟧') :
    (homotopyQuotient A).map g ≫ (shiftIso n N V eN).hom =
      (shiftIso n M S eM).hom ≫ ((homotopyQuotient A).map f)⟦n⟧'
  distinguished_iff (t : Triangle (HomotopyCategory A)) : t ∈ distTriang (HomotopyCategory A) ↔
    ∃ (M N K S : Module A) (f : M ⟶ N) (s : ShiftComparison A 1 M S)
      (g : N ⟶ K) (h : K ⟶ S),
      Nonempty (ConeComparison A f K S s g h) ∧
      Nonempty (t ≅ Triangle.mk ((homotopyQuotient A).map f) ((homotopyQuotient A).map g)
        ((homotopyQuotient A).map h ≫ (shiftIso 1 M S s).hom))

attribute [instance_reducible] HomotopyStructure.preadditive HomotopyStructure.shift
  HomotopyStructure.pretriangulated

attribute [instance] HomotopyStructure.preadditive HomotopyStructure.zero
  HomotopyStructure.shift HomotopyStructure.shiftAdditive HomotopyStructure.pretriangulated
  HomotopyStructure.triangulated

/-- The complete sheaf dg homotopy/localization package. Its fields render the
cohomology, cone criterion, saturated triangulated calculus, and two-out-of-three
clauses of the node statement. Source: Stacks `sdga.tex`, Tags 0FS7, 0FT2 and
0FT4 (blueprint: lem-sfb-sheaf-dg-homotopy-system). -/
class HomotopySystem (A : Algebra O) extends HomotopyStructure A where
  cohomology (n : ℤ) : HomotopyCategory A ⥤ Coeff O
  cohomology_factors (n : ℤ) :
    homotopyQuotient A ⋙ cohomology n =
      underlying A ⋙ HomologicalComplex.homologyFunctor (Coeff O) (ComplexShape.up ℤ) n
  W : MorphismProperty (HomotopyCategory A)
  W_iff_cohomology (X Y : HomotopyCategory A) (f : X ⟶ Y) :
    W f ↔ ∀ n : ℤ, IsIso ((cohomology n).map f)
  W_saturated : W.IsSaturatedTriangulatedMultiplicativeSystem
  W_two_of_three {X Y Z : HomotopyCategory A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (W f ∧ W g → W (f ≫ g)) ∧
    (W f ∧ W (f ≫ g) → W g) ∧
    (W g ∧ W (f ≫ g) → W f)
  cone_criterion {M N : Module A} (f : M ⟶ N)
      (K S : Module A) (s : ShiftComparison A 1 M S)
      (g : N ⟶ K) (h : K ⟶ S) ( _hc : ConeComparison A f K S s g h) :
    W ((homotopyQuotient A).map f) ↔
      ∀ n : ℤ, IsZero ((cohomology n).obj ((homotopyQuotient A).obj K))

open ZeroObject

end CategoryTheory.RingedSiteDg
