/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictPerfectRelativeTensorComplex
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.RelativeFlatOpenScalarRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarRestrictedTensorRetractFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Relative flatness of local tensor terms

Source: Stacks Project, Tags 0DJQ and 08CI, local tensor calculation.
(blueprint: lem-pc-strict-perfect-relative-tensor-terms-flat).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace AlgebraicGeometry.Scheme

private theorem restrictScalars_preservesColimits
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R A : Sheaf J RingCat.{u}} (α : R ⟶ A)
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    PreservesColimitsOfSize.{u, u} (SheafOfModules.restrictScalars.{u} α) := by
  have h (B : Sheaf J RingCat.{u}) :
      PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} B) := by
    constructor
    intro K _
    exact ((moduleSheaves_colimits_forgetful B).2.2.2.2.2 K).2.1
  have := h R
  have := h A
  have : ReflectsColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R) :=
    reflectsColimits_of_reflectsIsomorphisms
  have : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.restrictScalars.{u} α ⋙ SheafOfModules.toSheaf.{u} R) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} A))
  exact preservesColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{u} R)


/-- Each term of the explicitly scalar-restricted local total tensor is flat over
f inverse-image O_S on the open site. Source: Stacks Project, Tags 0DJQ and 08CI,
local relative Tor calculation; Tag 05NE, flatness detected on stalks.

Proof: at x in U choose an affine neighbourhood of f(x). Affine neighbourhoods of x
inside its preimage form a filtered basis. The hypothesis IsFlatOver makes every
G-term section module flat over this base section ring. Their filtered colimit is
the stalk and remains flat. Localizing the base ring gives flatness over O_S,f(x),
which is the stalk of the inverse-image ring. The stalks of L terms are retracts
of finite free O_X,x-modules, so tensoring with them gives retracts of finite sums
of these flat base modules. The degreewise total is a direct sum of these tensors;
stalks commute with the tensor sheafification and this sum. Sums and retracts of
flat modules are flat. Exactness of tensor is detected on stalks, giving flatness
of the scalar-restricted term as a sheaf on the localized site. The empty open,
zero summands and a zero complex satisfy the same stalkwise argument.
(blueprint: lem-pc-strict-perfect-relative-tensor-terms-flat). -/
theorem strictPerfect_relativeTensor_terms_flat
    {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (L : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hL : IsStrictlyPerfect X U L)
    (hGflat : ∀ n : ℤ, Modules.IsFlatOver (G.X n) f) :
    ∀ n : ℤ, SheafOfModules.IsFlat
      ((strictPerfectRelativeTensorComplex f U L G).X n) := by
  let : MonoidalCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    SheafOfModules.monoidalCategory (X.sheaf.over U)
  let : (curriedTensor
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor (X.sheaf.over U)
  let (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj (X.sheaf.over U) M
  let GU := ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapHomologicalComplex
     (.up ℤ)).obj G
  let α := ((Opens.grothendieckTopology X).overPullback CommRingCat.{u} U).map
    (Modules.tensorPullbackRingMap f)
  let B := (sheafCompose ((Opens.grothendieckTopology X).over U)
    (forget₂ CommRingCat.{u} RingCat.{u})).map α
  let F := SheafOfModules.restrictScalars B
  have hF : PreservesColimitsOfSize.{u, u} F := restrictScalars_preservesColimits B
  have hGU (q : ℤ) : SheafOfModules.IsFlat (F.obj (GU.X q)) :=
    relativeFlat_open_scalarRestriction f U (G.X q) (hGflat q)
  let : MonoidalCategory (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X).over U)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (X.sheaf.over U))) :=
    SheafOfModules.monoidalCategory (X.sheaf.over U)
  have hPQ (p q : ℤ) : SheafOfModules.IsFlat (F.obj (L.X p ⊗ GU.X q)) := by
    obtain ⟨m, ι, π, h⟩ := hL.2 p
    exact SheafOfModules.isFlat_scalarRestricted_tensor_retract α
      (L.X p) (GU.X q) m ι π h (hGU q)
  let D := ((Functor.mapBifunctorHomologicalComplex (curriedTensor _) (.up ℤ) (.up ℤ)).obj
    L).obj GU
  let R := (TopCat.Sheaf.inverseImageRing f.base S.sheaf).over U
  intro n
  let M := D.toGradedObject.mapObjFun
    (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ)) n
  have hM : ∀ j, SheafOfModules.IsFlat (F.obj (M j)) := by
    intro j
    exact hPQ j.1.1 j.1.2
  let I := (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ)) ⁻¹' {n}
  let M' := fun j : ULift.{u} I ↦ M j.down
  have hf := SheafOfModules.isFlat_coproduct R
    (fun j : ULift.{u} I ↦ F.obj (M' j)) (fun j ↦ hM j.down)
  let e := (PreservesCoproduct.iso F M').symm ≪≫
    F.mapIso (Sigma.whiskerEquiv Equiv.ulift (fun _ ↦ Iso.refl _))
  let := SheafOfModules.monoidalCategory R
  exact (exactFunctor _ _).prop_of_iso ((tensoringRight _).mapIso e) hf


end AlgebraicGeometry.Scheme
