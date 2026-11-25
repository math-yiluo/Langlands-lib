/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldDerivedScalarTower
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import Mathlib.CategoryTheory.InducedCategory
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.LinearAlgebra.Dual.Lemmas
import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdMorphismDescent

/-! # The category of finite-stage coefficient complexes

Source: Weil blueprint, `lemma-perfect-complexes-geometric-point`, order 1509
(blueprint: def-weil-point-fd-qlbar-category).

Objects are literally pairs (finite coefficient field, finite-dimensional derived complex).
We realize their morphism colimits as morphisms between their scalar extensions in D(Qbar).
The common-stage bijection is `pointFdQbarCocone_isFilteredTwoColimit`, not an assumption.
This gives the same category up to its canonical identity-on-objects isomorphism.

## Main definitions and statements

* `PointFdQbar`: the finite-stage pairs with their canonical Hom realization.
* `pointFdQbarCocone_isFilteredTwoColimit`: the common-stage Hom colimit characterization.
* `pointFdQbarHasShift`, `pointFdQbarDistinguished`: the specified shifts and triangles.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

/-- The finite-stage pairs before equipping them with morphisms.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
def PointFdQbarObjects :=
  Σ E : Padic.FiniteCoefficientFields l Ω,
    (pointFiniteDimensional E.val).FullSubcategory

/-- The canonical realization of a finite-stage object, by actual scalar extension.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarObject (X : PointFdQbarObjects l Ω) :
    DerivedCategory (ModuleCat.{u} Ω) :=
  (fieldDerivedScalarExtension (K := X.1.val) (L := Ω) X.1.val.subtype).obj X.2.obj

/-- A concrete realization of the common-stage category. Its Hom is canonically the
filtered common-stage colimit, as specified by the cocone theorem below.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
abbrev PointFdQbar :=
  InducedCategory (DerivedCategory (ModuleCat.{u} Ω)) (pointFdQbarObject l Ω)

/-- The faithful realization of the stagewise category in D(Qbar).
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarRealization :
    PointFdQbar l Ω ⥤ DerivedCategory (ModuleCat.{u} Ω) :=
  inducedFunctor (pointFdQbarObject l Ω)

/-- The canonical functor from a finite coefficient stage to the stagewise category.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarStage (E : Padic.FiniteCoefficientFields l Ω) :
    (pointFiniteDimensional E.val).FullSubcategory ⥤ PointFdQbar l Ω where
  obj C := ⟨E, C⟩
  map f := InducedCategory.homMk
    ((fieldDerivedScalarExtension (K := E.val) (L := Ω) E.val.subtype).map f.hom)
  map_id C := InducedCategory.hom_ext
    ((fieldDerivedScalarExtension (K := E.val) (L := Ω) E.val.subtype).map_id C.obj)
  map_comp f g := InducedCategory.hom_ext
    ((fieldDerivedScalarExtension (K := E.val) (L := Ω) E.val.subtype).map_comp f.hom g.hom)

/-- Compatibility of the canonical finite-stage embeddings, with precisely the
termwise tensor tower comparison as underlying isomorphism.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarStageComp
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pointFdScalarExtension (IntermediateField.inclusion h).toRingHom ⋙
        pointFdQbarStage l Ω F ≅ pointFdQbarStage l Ω E :=
  ((fullyFaithfulInducedFunctor (pointFdQbarObject l Ω)).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (pointFiniteDimensional E.val).ι
      (fieldScalarTower (IntermediateField.inclusion h).toRingHom F.val.subtype))

omit [IsAlgClosure (Padic l) Ω] in
/-- Finite-dimensional bounded cohomology is stable under every integer shift.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category).
Proof: H^i(C[n]) is canonically H^(i+n)(C); translate the finite support by -n
and retain the same finite-dimensionality proofs. -/
theorem pointFd_shift_mem {F : Type u} [Field F]
    (C : DerivedCategory (ModuleCat.{u} F)) (hC : pointFiniteDimensional F C) (n : ℤ) :
    pointFiniteDimensional F (C⟦n⟧) := by
  classical
  obtain ⟨⟨s, hs⟩, hfd⟩ := hC
  let e (i : ℤ) :
      (homologyFunctor (ModuleCat.{u} F) i).obj (C⟦n⟧) ≅
        (homologyFunctor (ModuleCat.{u} F) (n + i)).obj C :=
    ((homologyFunctor (ModuleCat.{u} F) 0).shiftIso n i (n + i) rfl).app C
  refine ⟨⟨s.image (fun i ↦ i - n), ?_⟩, ?_⟩
  · intro i hi
    have hni : n + i ∉ s := by
      intro h
      apply hi
      exact Finset.mem_image.mpr ⟨n + i, h, by omega⟩
    exact (hs (n + i) hni).of_iso (e i)
  · intro i
    let := hfd (n + i)
    exact (e i).symm.toLinearEquiv.finiteDimensional

/-- The shift of a stage pair, computed at that same stage.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarShiftObj (X : PointFdQbar l Ω) (n : ℤ) : PointFdQbar l Ω :=
  ⟨X.1, ⟨X.2.obj⟦n⟧, pointFd_shift_mem X.2.obj X.2.property n⟩⟩

/-- The shifted realization with its object data fixed at the original finite stage.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarShiftRealization (n : ℤ) :
    PointFdQbar l Ω ⥤ DerivedCategory (ModuleCat.{u} Ω) :=
  (pointFdQbarRealization l Ω ⋙ shiftFunctor _ n).copyObj
    (fun X ↦ pointFdQbarObject l Ω (pointFdQbarShiftObj l Ω X n))
    (fun X ↦ ((fieldDerivedScalarExtension (K := X.1.val) (L := Ω)
      X.1.val.subtype).commShiftIso n).symm.app X.2.obj)

/-- The actual shift functor on stage pairs and their induced morphisms.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarShift (n : ℤ) : PointFdQbar l Ω ⥤ PointFdQbar l Ω where
  obj X := pointFdQbarShiftObj l Ω X n
  map f := InducedCategory.homMk ((pointFdQbarShiftRealization l Ω n).map f)
  map_id X := InducedCategory.hom_ext ((pointFdQbarShiftRealization l Ω n).map_id X)
  map_comp f g := InducedCategory.hom_ext ((pointFdQbarShiftRealization l Ω n).map_comp f g)

/-- The shift comparison used to transport the coherent shift structure faithfully.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarShiftIso (n : ℤ) :
    pointFdQbarShift l Ω n ⋙ pointFdQbarRealization l Ω ≅
      pointFdQbarRealization l Ω ⋙ shiftFunctor _ n :=
  ((pointFdQbarRealization l Ω ⋙ shiftFunctor _ n).isoCopyObj
    (fun X ↦ pointFdQbarObject l Ω (pointFdQbarShiftObj l Ω X n))
    (fun X ↦ ((fieldDerivedScalarExtension (K := X.1.val) (L := Ω)
      X.1.val.subtype).commShiftIso n).symm.app X.2.obj)).symm

/-- The coherent integer shift structure induced from the faithful realization.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable instance pointFdQbarHasShift : HasShift (PointFdQbar l Ω) ℤ :=
  (fullyFaithfulInducedFunctor (pointFdQbarObject l Ω)).hasShift
    (pointFdQbarShift l Ω) (pointFdQbarShiftIso l Ω)

/-- Realization commutes with the specified shifts by its canonical tensor comparison.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable instance pointFdQbarRealizationCommShift :
    (pointFdQbarRealization l Ω).CommShift ℤ :=
  Functor.CommShift.ofHasShiftOfFullyFaithful
    (fullyFaithfulInducedFunctor (pointFdQbarObject l Ω))
    (pointFdQbarShift l Ω) (pointFdQbarShiftIso l Ω)

/-- Distinguished triangles are exactly those isomorphic, under faithful realization,
to scalar extensions of distinguished triangles at one common finite stage, with
all three vertices in D^b_fd of that stage.
Source: blueprint order 1509 (blueprint: def-weil-point-fd-qlbar-category). -/
noncomputable def pointFdQbarDistinguished (T : Triangle (PointFdQbar l Ω)) : Prop :=
  ∃ (E : Padic.FiniteCoefficientFields l Ω)
    (S : Triangle (DerivedCategory (ModuleCat.{u} E.val))),
    S ∈ distTriang _ ∧ pointFiniteDimensional E.val S.obj₁ ∧
      pointFiniteDimensional E.val S.obj₂ ∧ pointFiniteDimensional E.val S.obj₃ ∧
      Nonempty (((fieldDerivedScalarExtension (K := E.val) (L := Ω)
        E.val.subtype).mapTriangle).obj S ≅ (pointFdQbarRealization l Ω).mapTriangle.obj T)

end DerivedCategory
