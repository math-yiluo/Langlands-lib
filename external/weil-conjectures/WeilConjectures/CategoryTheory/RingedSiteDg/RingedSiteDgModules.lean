/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-! # Sheaf dg algebras and modules on a ringed site

Source: Stacks Project, sdga.tex, Tags 0FRF, 0FRI, 0FS5 and 0FT5
(blueprint: def-sfb-ringed-site-dg-modules).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe c v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalOpposite CategoryTheory.Pretriangulated

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (O : Sheaf J CommRingCat.{u})

/-- The coefficient module sheaves. Source: Stacks 0FRF
(blueprint: def-sfb-ringed-site-dg-modules). -/
abbrev Coeff := SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)

/-- Countable coproducts of coefficient sheaves, via the existing small-colimits instance
(a direct path avoiding a typeclass-search timeout). -/
instance coeffHasCountableCoproducts : HasCountableCoproducts (Coeff O) :=
  haveI : HasColimitsOfSize.{0, 0} (Coeff O) := inferInstance
  ⟨fun _ _ ↦ HasColimitsOfSize.has_colimits_of_shape _⟩

/-- Unbounded integer cochain complexes with their signed direct-sum tensor.
Source: Stacks 0FRF (blueprint: def-sfb-ringed-site-dg-modules). -/
abbrev Complex := CochainComplex (Coeff O) ℤ

/-- Monoid objects are associative unital sheaf dg O-algebras. The differential
of the total tensor enforces the Leibniz sign; no commutativity is imposed.
Source: Stacks 0FRF (blueprint: def-sfb-ringed-site-dg-modules). -/
abbrev Algebra := Mon (Complex O)

variable {O}

/-- Right dg modules are left module objects in the reversed tensor category.
Source: Stacks 0FRI (blueprint: def-sfb-ringed-site-dg-modules). -/
abbrev Module (A : Algebra O) := Mod (Complex O)ᴹᵒᵖ (mop A.X)

/-- Forget only the right action. Source: Stacks 0FRI
(blueprint: def-sfb-ringed-site-dg-modules). -/
def underlying (A : Algebra O) : Module A ⥤ Complex O :=
  Mod.forget (mop A.X) ⋙ unmopFunctor _

/-- The chain-level action M tensor A to M. Source: Stacks 0FRI
(blueprint: def-sfb-ringed-site-dg-modules). -/
abbrev action {A : Algebra O} (M : Module A) :
    (underlying A).obj M ⊗ A.X ⟶ (underlying A).obj M :=
  (ModObj.smul (M := mop A.X) (X := M.X)).unmop

/-- Degreewise action. Source: Stacks 0FRI
(blueprint: def-sfb-ringed-site-dg-modules). -/
def actionDegree {A : Algebra O} (M : Module A) (p q n : ℤ) (h : p + q = n) :
    ((underlying A).obj M).X p ⊗ A.X.X q ⟶ ((underlying A).obj M).X n :=
  HomologicalComplex.ιTensorObj _ _ p q n h ≫ (action M).f n

/-- Restriction changes the action by phi and keeps the whole complex.
Source: Stacks sdga, section-dg-bimodules
(blueprint: def-sfb-ringed-site-dg-modules). -/
def restriction {A B : Algebra O} (φ : A ⟶ B) : Module B ⥤ Module A :=
  Mod.comap φ.hom.mop

/-- Quasi-isomorphisms detected on underlying cohomology sheaves.
Source: Stacks 0FT4 (blueprint: def-sfb-ringed-site-dg-modules). -/
def quasiIsomorphisms (A : Algebra O) : MorphismProperty (Module A) :=
  fun _ _ f ↦ QuasiIso ((underlying A).map f)

/-- Formal-inverse localization of dg modules. Localizing directly also identifies
homotopic maps via the cylinder quasi-isomorphism, hence gives the homotopy localization.
Source: Stacks 0FT5 (blueprint: def-sfb-ringed-site-dg-modules). -/
abbrev Derived (A : Algebra O) := (quasiIsomorphisms A).Localization

/-- The canonical localization functor. Source: Stacks 0FT5
(blueprint: def-sfb-ringed-site-dg-modules). -/
abbrev Q (A : Algebra O) : Module A ⥤ Derived A := (quasiIsomorphisms A).Q

/-- Standard shift comparison, including the unchanged right action.
Source: Stacks sdga, section-shift (blueprint: def-sfb-ringed-site-dg-modules). -/
structure ShiftComparison (A : Algebra O) (n : ℤ) (M S : Module A) where
  iso : (underlying A).obj S ≅ ((underlying A).obj M)⟦n⟧
  action_eq : action S ≫ iso.hom = (iso.hom ▷ A.X) ≫
    (CochainComplex.mapBifunctorShift₁Iso ((underlying A).obj M) A.X
      (curriedTensor (Coeff O)) n).hom ≫ (action M)⟦n⟧'

/-- Cone comparison fixes both actions by their projections and fixes the signed
connecting map. Source: Stacks 0FS5
(blueprint: def-sfb-ringed-site-dg-modules). -/
structure ConeComparison (A : Algebra O) {M N : Module A} (f : M ⟶ N)
    (K S : Module A) (s : ShiftComparison A 1 M S) (g : N ⟶ K) (h : K ⟶ S) where
  iso : (underlying A).obj K ≅ CochainComplex.mappingCone ((underlying A).map f)
  snd_action (p q : ℤ) :
    actionDegree K p q (p + q) rfl ≫ iso.hom.f (p + q) ≫
      (CochainComplex.mappingCone.snd ((underlying A).map f)).v
        (p + q) (p + q) (add_zero _) =
    ((iso.hom.f p ≫ (CochainComplex.mappingCone.snd ((underlying A).map f)).v
      p p (add_zero _)) ▷ A.X.X q) ≫ actionDegree N p q (p + q) rfl
  fst_action (p q : ℤ) :
    HEq (actionDegree K p q (p + q) rfl ≫ iso.hom.f (p + q) ≫
      (CochainComplex.mappingCone.fst ((underlying A).map f)).val.v
        (p + q) (p + q + 1) rfl)
    (((iso.hom.f p ≫ (CochainComplex.mappingCone.fst ((underlying A).map f)).val.v
      p (p + 1) rfl) ▷ A.X.X q) ≫ actionDegree M (p + 1) q ((p + 1) + q) rfl)
  inclusion : (underlying A).map g ≫ iso.hom =
    CochainComplex.mappingCone.inr ((underlying A).map f)
  connecting : (underlying A).map h ≫ s.iso.hom =
    iso.hom ≫ (CochainComplex.mappingCone.triangle ((underlying A).map f)).mor₃

/-- A standard triangulation of the fixed localization, characterized by all actual
shifts and cone triangles, without an adjunction or existence assumption.
Source: Stacks 0FT5 (blueprint: def-sfb-ringed-site-dg-modules). -/
class DerivedStructure (A : Algebra O) where
  [preadditive : Preadditive (Derived A)]
  [zero : HasZeroObject (Derived A)]
  [shift : HasShift (Derived A) ℤ]
  [shiftAdditive : ∀ n : ℤ, (shiftFunctor (Derived A) n).Additive]
  [pretriangulated : Pretriangulated (Derived A)]
  [triangulated : IsTriangulated (Derived A)]
  shifts_exist (n : ℤ) (M : Module A) :
    ∃ S : Module A, Nonempty (ShiftComparison A n M S)
  cones_exist {M N : Module A} (f : M ⟶ N) :
    ∃ (K S : Module A) (s : ShiftComparison A 1 M S) (g : N ⟶ K) (h : K ⟶ S),
      Nonempty (ConeComparison A f K S s g h)
  shiftIso (n : ℤ) (M S : Module A) (e : ShiftComparison A n M S) :
    (Q A).obj S ≅ ((Q A).obj M)⟦n⟧
  shift_natural (n : ℤ) (M N S V : Module A)
      (eM : ShiftComparison A n M S) (eN : ShiftComparison A n N V)
      (f : M ⟶ N) (g : S ⟶ V)
      (comm : (underlying A).map g ≫ eN.iso.hom =
        eM.iso.hom ≫ ((underlying A).map f)⟦n⟧') :
    (Q A).map g ≫ (shiftIso n N V eN).hom =
      (shiftIso n M S eM).hom ≫ ((Q A).map f)⟦n⟧'
  distinguished_iff (t : Triangle (Derived A)) : t ∈ distTriang (Derived A) ↔
    ∃ (M N K S : Module A) (f : M ⟶ N) (s : ShiftComparison A 1 M S)
      (g : N ⟶ K) (h : K ⟶ S), Nonempty (ConeComparison A f K S s g h) ∧
      Nonempty (t ≅ Triangle.mk ((Q A).map f) ((Q A).map g)
        ((Q A).map h ≫ (shiftIso 1 M S s).hom))

attribute [instance_reducible] DerivedStructure.preadditive DerivedStructure.shift
  DerivedStructure.pretriangulated
attribute [instance] DerivedStructure.preadditive DerivedStructure.zero DerivedStructure.shift
  DerivedStructure.shiftAdditive DerivedStructure.pretriangulated DerivedStructure.triangulated

/-- The balanced and right-linear chain maps out of the ordinary total tensor.
Source: Stacks sdga, section-dg-bimodules
(blueprint: def-sfb-ringed-site-dg-modules). -/
def IsBalanced {A B : Algebra O} (φ : A ⟶ B) (M : Module A) (N : Module B)
    (t : (underlying A).obj M ⊗ B.X ⟶ (underlying B).obj N) : Prop :=
  (action M ▷ B.X) ≫ t =
    (α_ ((underlying A).obj M) A.X B.X).hom ≫
      ((underlying A).obj M ◁ ((φ.hom ▷ B.X) ≫ MonObj.mul)) ≫ t ∧
  (t ▷ B.X) ≫ action N =
    (α_ ((underlying A).obj M) B.X B.X).hom ≫
      ((underlying A).obj M ◁ MonObj.mul) ≫ t

/-- The ordinary balanced tensor, specified by its representing universal property.
The universal map is part of the data and determines its object uniquely up to unique iso.
Source: Stacks sdga, section-dg-bimodules
(blueprint: def-sfb-ringed-site-dg-modules). -/
structure TensorPresentation {A B : Algebra O} (φ : A ⟶ B) (M : Module A)
    (T : Module B) where
  tensor : (underlying A).obj M ⊗ B.X ⟶ (underlying B).obj T
  balanced : IsBalanced φ M T tensor
  universal (N : Module B)
      (t : (underlying A).obj M ⊗ B.X ⟶ (underlying B).obj N)
      (ht : IsBalanced φ M N t) :
    ∃! f : T ⟶ N, tensor ≫ (underlying B).map f = t

/-- Ordinary extension and its action-normalized adjunction. This defines a presentation,
not an assertion of its existence. Source: Stacks sdga, section-dg-bimodules
(blueprint: def-sfb-ringed-site-dg-modules). -/
structure OrdinaryExtension {A B : Algebra O} (φ : A ⟶ B) where
  functor : Module A ⥤ Module B
  tensor (M : Module A) : TensorPresentation φ M (functor.obj M)
  naturality {M N : Module A} (f : M ⟶ N) :
    ((underlying A).map f ▷ B.X) ≫ (tensor N).tensor =
      (tensor M).tensor ≫ (underlying B).map (functor.map f)
  adjunction : functor ⊣ restriction φ
  unit (M : Module A) :
    (underlying A).map (adjunction.unit.app M) =
      (ρ_ ((underlying A).obj M)).inv ≫
        ((underlying A).obj M ◁ MonObj.one) ≫ (tensor M).tensor
  counit (N : Module B) :
    (tensor ((restriction φ).obj N)).tensor ≫
      (underlying B).map (adjunction.counit.app N) = action N

end CategoryTheory.RingedSiteDg
