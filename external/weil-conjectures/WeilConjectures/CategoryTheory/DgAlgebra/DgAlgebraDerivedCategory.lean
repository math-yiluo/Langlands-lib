/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!
# The derived category of a dg algebra

Source: Stacks Project, dga.tex, Definitions definition-dga, definition-dgm,
definition-shift, definition-cone, and section-derived
(blueprint: def-sfb-dg-derived-category).

The category is the actual Gabriel--Zisman localization of right dg modules at
quasi-isomorphisms. `DerivedStructure` specifies its standard triangulation by
shift comparisons and the precise mapping-cone triangles. It supplies no generation,
compactness or adjunction property. No object is chosen from an existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalOpposite CategoryTheory.Pretriangulated

namespace CategoryTheory.DgAlgebra

/-- Integer cochain complexes of abelian groups, expressed as modules over the integers.
Source: Stacks, dga.tex, definition-dga (blueprint: def-sfb-dg-derived-category). -/
abbrev Complex := CochainComplex (ModuleCat.{u} (ULift.{u} ℤ)) ℤ

/-- An associative unital dg algebra is a monoid in cochain complexes. The chain-map
condition on multiplication is precisely the signed Leibniz rule, and the complex
identity is d squared equals zero. No graded commutativity is required.
Source: Stacks, dga.tex, definition-dga (blueprint: def-sfb-dg-derived-category). -/
abbrev Algebra := Mon Complex.{u}

/-- A module object in the reversed tensor category has action M tensor A to M.
Thus these are right dg modules, with d(ma)=d(m)a+(-1)^degree(m)m d(a).
Source: Stacks, dga.tex, definition-dgm (blueprint: def-sfb-dg-derived-category). -/
abbrev RightModule (A : Algebra.{u}) := Mod Complex.{u}ᴹᵒᵖ (mop A.X)

/-- Forget the right action, retaining the actual differential.
Source: Stacks, dga.tex, definition-dgm (blueprint: def-sfb-dg-derived-category). -/
def underlying (A : Algebra.{u}) : RightModule A ⥤ Complex.{u} :=
  Mod.forget (mop A.X) ⋙ unmopFunctor _

/-- The homogeneous right action, evaluated on a pure tensor in the total tensor complex.
Source: Stacks, dga.tex, definition-dgm (blueprint: def-sfb-dg-derived-category). -/
def act (A : Algebra.{u}) (M : RightModule A) (p q : ℤ)
    (m : ((underlying A).obj M).X p) (a : A.X.X q) :
    ((underlying A).obj M).X (p + q) :=
  ((ModObj.smul (M := mop A.X) (X := M.X)).unmop.f (p + q))
    ((HomologicalComplex.ιTensorObj ((underlying A).obj M) A.X p q (p + q) rfl)
      (TensorProduct.tmul (ULift.{u} ℤ) m a))

/-- Quasi-isomorphisms are detected on every cohomology group of the underlying complex.
Source: Stacks, dga.tex, section-derived (blueprint: def-sfb-dg-derived-category). -/
def quasiIsomorphisms (A : Algebra.{u}) : MorphismProperty (RightModule A) :=
  fun _ _ f ↦ QuasiIso ((underlying A).map f)

/-- The actual localization, rather than an unspecified category with a generator.
Localizing dg modules directly at quasi-isomorphisms also identifies homotopic maps:
the usual cylinder projection is a quasi-isomorphism. Hence this is equivalently the
localization of the homotopy category used by Stacks.
Source: Stacks, dga.tex, section-derived (blueprint: def-sfb-dg-derived-category). -/
abbrev Derived (A : Algebra.{u}) := (quasiIsomorphisms A).Localization

/-- The canonical localization functor.
Source: Stacks, dga.tex, section-derived (blueprint: def-sfb-dg-derived-category). -/
abbrev Q (A : Algebra.{u}) : RightModule A ⥤ Derived A := (quasiIsomorphisms A).Q

/-- A comparison with the usual shift: a complex isomorphism whose degree maps
preserve the unchanged right action. The complex isomorphism includes the sign
(-1)^n on the differential. No boundedness is imposed.
Source: Stacks, dga.tex, definition-shift (blueprint: def-sfb-dg-derived-category). -/
structure ShiftComparison (A : Algebra.{u}) (n : ℤ) (M S : RightModule A) where
  iso : (underlying A).obj S ≅ ((underlying A).obj M)⟦n⟧
  action (p q : ℤ) (m : ((underlying A).obj S).X p) (a : A.X.X q) :
    HEq
      ((((underlying A).obj M).shiftFunctorObjXIso n (p + q) (p + q + n) rfl).hom
        (iso.hom.f (p + q) (act A S p q m a)))
      (act A M (p + n) q
        ((((underlying A).obj M).shiftFunctorObjXIso n p (p + n) rfl).hom
          (iso.hom.f p m)) a)

/-- A dg mapping-cone triangle. The two projection equations force the action on
the cone to be the componentwise action on M[1] plus N; the map equations force
its actual inclusion and signed connecting map. An arbitrary extension is excluded.
Source: Stacks, dga.tex, definition-cone and section-distinguished; Mathlib's
mapping-cone sign convention (blueprint: def-sfb-dg-derived-category). -/
structure ConeComparison (A : Algebra.{u}) {M N : RightModule A} (f : M ⟶ N)
    (K S : RightModule A) (s : ShiftComparison A 1 M S) (g : N ⟶ K) (h : K ⟶ S) where
  iso : (underlying A).obj K ≅ CochainComplex.mappingCone ((underlying A).map f)
  snd_action (p q : ℤ) (m : ((underlying A).obj K).X p) (a : A.X.X q) :
    HEq
      ((CochainComplex.mappingCone.snd ((underlying A).map f)).v
        (p + q) (p + q) (add_zero _) (iso.hom.f (p + q) (act A K p q m a)))
      (act A N p q
        ((CochainComplex.mappingCone.snd ((underlying A).map f)).v p p
          (add_zero _) (iso.hom.f p m)) a)
  fst_action (p q : ℤ) (m : ((underlying A).obj K).X p) (a : A.X.X q) :
    HEq
      ((CochainComplex.mappingCone.fst ((underlying A).map f)).val.v
        (p + q) (p + q + 1) rfl (iso.hom.f (p + q) (act A K p q m a)))
      (act A M (p + 1) q
        ((CochainComplex.mappingCone.fst ((underlying A).map f)).val.v
          p (p + 1) rfl (iso.hom.f p m)) a)
  inclusion : (underlying A).map g ≫ iso.hom =
    CochainComplex.mappingCone.inr ((underlying A).map f)
  connecting : (underlying A).map h ≫ s.iso.hom =
    iso.hom ≫ (CochainComplex.mappingCone.triangle ((underlying A).map f)).mor₃

/-- The standard triangulated structure on the specified localization. Its comparisons
are natural for every map of shifted dg modules, and the distinguished-triangle
predicate is fixed by an iff with the actual dg mapping cones. The coproduct universe
is the universe of the component modules. This is structural data of D(A,d), not an
assumption of generation or of a theorem about an adjunction.
Source: Stacks, dga.tex, section-derived, definition-shift, definition-cone and
section-distinguished (blueprint: def-sfb-dg-derived-category). -/
class DerivedStructure (A : Algebra.{u}) where
  [preadditive : Preadditive (Derived A)]
  [zero : HasZeroObject (Derived A)]
  [shift : HasShift (Derived A) ℤ]
  [shiftAdditive : ∀ n : ℤ, (shiftFunctor (Derived A) n).Additive]
  [pretriangulated : Pretriangulated (Derived A)]
  [triangulated : IsTriangulated (Derived A)]
  [coproducts : HasCoproducts.{u} (Derived A)]
  shifts_exist (n : ℤ) (M : RightModule A) :
    ∃ S : RightModule A, Nonempty (ShiftComparison A n M S)
  cones_exist {M N : RightModule A} (f : M ⟶ N) :
    ∃ (K S : RightModule A) (s : ShiftComparison A 1 M S) (g : N ⟶ K) (h : K ⟶ S),
      Nonempty (ConeComparison A f K S s g h)
  shiftIso (n : ℤ) (M S : RightModule A) (e : ShiftComparison A n M S) :
    (Q A).obj S ≅ ((Q A).obj M)⟦n⟧
  shift_natural (n : ℤ) (M N S V : RightModule A)
      (eM : ShiftComparison A n M S) (eN : ShiftComparison A n N V)
      (f : M ⟶ N) (g : S ⟶ V)
      (comm : (underlying A).map g ≫ eN.iso.hom =
        eM.iso.hom ≫ ((underlying A).map f)⟦n⟧') :
    (Q A).map g ≫ (shiftIso n N V eN).hom =
      (shiftIso n M S eM).hom ≫ ((Q A).map f)⟦n⟧'
  distinguished_iff (t : Triangle (Derived A)) : t ∈ distTriang (Derived A) ↔
    ∃ (M N K S : RightModule A) (f : M ⟶ N) (s : ShiftComparison A 1 M S)
      (g : N ⟶ K) (h : K ⟶ S),
      Nonempty (ConeComparison A f K S s g h) ∧
      Nonempty (t ≅ Triangle.mk ((Q A).map f) ((Q A).map g)
        ((Q A).map h ≫ (shiftIso 1 M S s).hom))

attribute [instance_reducible] DerivedStructure.preadditive DerivedStructure.shift
  DerivedStructure.pretriangulated

attribute [instance] DerivedStructure.preadditive DerivedStructure.zero
  DerivedStructure.shift DerivedStructure.shiftAdditive DerivedStructure.pretriangulated
  DerivedStructure.triangulated DerivedStructure.coproducts

end CategoryTheory.DgAlgebra
