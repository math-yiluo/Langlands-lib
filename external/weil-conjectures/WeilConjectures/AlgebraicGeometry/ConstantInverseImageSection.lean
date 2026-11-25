/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData

/-! # Transporting global coefficient sections

Source: Stacks Project, Sites Tag 00YV and Modules on Sites Tag 03D2
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ConstantCompletion

/-- A global section viewed as a constant-valued map on a test sheaf.
Source: Stacks 00YV (auxiliary; not a blueprint node). -/
def sectionMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (a : (R.obj ⋙ forget CommRingCat).sections)
    (T : Sheaf J (Type u)) : T ⟶ (sheafCompose J (forget CommRingCat)).obj R :=
  ⟨{ app := fun U ↦ ↾(fun _ ↦ a.val U)
     naturality := by
       intro U V f
       ext x
       exact (a.property f).symm }⟩

/-- A constant coefficient as a map on any test sheaf.
Source: Stacks 093M (auxiliary; not a blueprint node). -/
def constantSectionMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Type u) [CommRing A] (a : A) (T : Sheaf J (Type u)) :
    T ⟶ (sheafCompose J (forget CommRingCat)).obj (constant J A) :=
  sectionMap (constant J A) (constantSection (J := J) a) T

/-- Transport a global ring section using preservation of the terminal sheaf.
Source: Stacks 00YV, 03D2 (auxiliary; not a blueprint node). -/
def inverseImageSection
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)} [PreservesFiniteLimits L]
    (F : InverseImageData L) (R : Sheaf JC CommRingCat.{u})
    (a : (R.obj ⋙ forget CommRingCat).sections) :
    ((F.rings.obj R).obj ⋙ forget CommRingCat).sections :=
  let T := Sheaf.terminal JC Types.isTerminalPUnit
  let T' := Sheaf.terminal JD Types.isTerminalPUnit
  let h := (Sheaf.isTerminalTerminal JC Types.isTerminalPUnit).isTerminalObj L T
  let f := h.from T' ≫ L.map (sectionMap R a T) ≫ (F.algebra R).ringUnderlying.hom
  (((F.rings.obj R).obj ⋙ forget CommRingCat).sectionsEquivHom PUnit).symm f.hom

/-- The transported global section computes inverse image on every test sheaf.
Source: Stacks 00YV, 03D2 (auxiliary; not a blueprint node).
Proof: factor the section map through the terminal sheaf. Both maps from L(T) to
L(1) are equal because L preserves terminal objects. Evaluate this equality. -/
theorem inverseImageSection_map
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)} [PreservesFiniteLimits L]
    (F : InverseImageData L) (R : Sheaf JC CommRingCat.{u})
    (a : (R.obj ⋙ forget CommRingCat).sections) (T : Sheaf JC (Type u)) :
    L.map (sectionMap R a T) ≫ (F.algebra R).ringUnderlying.hom =
      sectionMap (F.rings.obj R) (inverseImageSection F R a) (L.obj T) := by
  let S := Sheaf.terminal JC Types.isTerminalPUnit
  let S' := Sheaf.terminal JD Types.isTerminalPUnit
  let hS := Sheaf.isTerminalTerminal JC Types.isTerminalPUnit
  let hS' := Sheaf.isTerminalTerminal JD Types.isTerminalPUnit
  let h := hS.isTerminalObj L S
  have hf : sectionMap R a T = hS.from T ≫ sectionMap R a S := by
    ext U x
    rfl
  have ht : L.map (hS.from T) = hS'.from (L.obj T) ≫ h.from S' := h.hom_ext _ _
  rw [hf, L.map_comp, ht, Category.assoc, Category.assoc]
  ext U x
  rfl

/-- The structural image of a transported constant coefficient.
Source: Stacks 03D2, 093M (auxiliary; not a blueprint node). -/
def transportedConstantSection
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)} [PreservesFiniteLimits L]
    (F : InverseImageData L) (A : Type u) [CommRing A] (a : A) :
    ((constant JD A).obj ⋙ forget CommRingCat).sections :=
  ⟨fun U ↦ (constantMap F A).hom.app U
      ((inverseImageSection F (constant JC A) (constantSection (J := JC) a)).val U),
    fun f ↦ (ConcreteCategory.congr_hom ((constantMap F A).hom.naturality f) _).symm.trans
      (congrArg ((constantMap F A).hom.app _)
        ((inverseImageSection F (constant JC A) (constantSection (J := JC) a)).property f))⟩

end CategoryTheory.ConstantCompletion
