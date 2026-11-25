/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.AlgebraicGeometry.Picard.CanonicalDirectImageH0Unit
import WeilConjectures.AlgebraicGeometry.Flat.FlatDerivedStructureUnitProperties

/-! # The derived structure unit and its degree-zero and fibre comparisons

Source: Stacks Project, Tags 0E62, 0A1D, and 0096.
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The structure unit admits a derived lift with the canonical degree-zero comparison.
For quasi-compact separated flat morphisms its derived fibres have no negative
cohomology, and the residue-field H0 condition makes the fibre of this lift invertible
in degree zero. No surjectivity or injectivity of the ordinary stalk map is asserted.
Source: Stacks Project, Tag 0E62, first paragraph, Tag 0A1D (base change), and Tag 0096.
(blueprint: lem-sc-flat-derived-structure-unit).

Proof: Place O_X in degree zero and compute its derived direct image by a K-injective
resolution. The ordinary structure map followed by the resolution augmentation
induces a morphism a from O_S[0] into that derived image. An injective resolution of a
sheaf can be taken in nonnegative degrees. Left exactness of direct image identifies
its zeroth cohomology with f_*O_X; the zeroth cohomology of O_S[0] is O_S. Naturality
of the augmentation gives the displayed equality with unitToPushforwardObjUnit.
Since O_X is relatively flat, canonical base change to Spec k(s) is invertible.
Identify the pulled-back structure sheaf with O on the fibre using the canonical
adjoint tensor-unit isomorphism. The mate definition of base change carries a to
the ordinary structure map on that fibre. Derived direct image of a sheaf has no
negative cohomology. On the affine one-point scheme Spec k(s), evaluation at the
whole space detects isomorphisms of quasi-coherent sheaves. Thus an isomorphism on
global functions of the fibre gives the asserted degree-zero fibre isomorphism.
The construction and its comparisons do not use that isomorphism hypothesis; it
is needed only for the last implication. -/
theorem exists_flat_derived_structure_unit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsSeparated f] [Flat f] :
    let O := SheafOfModules.unit S.ringCatSheaf
    let J := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj O
    let E := (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
        (SheafOfModules.unit X.ringCatSheaf))
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0
    ∃ (a : J ⟶ E) (e₀ : H.obj J ≅ O)
      (e₁ : H.obj E ≅ (Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)),
      H.map a ≫ e₁.hom = e₀.hom ≫
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ∧
      (∀ (s : S) (i : ℤ), i < 0 → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
          ((derivedPullback (S.fromSpecResidueField s)).obj E))) ∧
      (∀ s : S, IsIso (f.fiberToSpecResidueField s).appTop →
        IsIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
            ((derivedPullback (S.fromSpecResidueField s)).map a))) := by
  classical
  dsimp only
  have : HasInjectiveResolutions X.Modules :=
    inferInstanceAs (HasInjectiveResolutions
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let M := SheafOfModules.unit X.ringCatSheaf
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0
  let k := DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0
  let a := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        Scheme.Modules.canonicalSingleDirectImageMap f M
  let e₀ := k.app (SheafOfModules.unit S.ringCatSheaf)
  let e₁ := F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
    (Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf.app M
  obtain ⟨hnegative, hfibre⟩ := flat_derived_structure_unit_properties f
  refine ⟨a, e₀, e₁, ?_, hnegative, hfibre⟩
  dsimp only [a, e₀, e₁, H, F, M]
  rw [Functor.map_comp, Category.assoc, Scheme.Modules.canonicalDirectImageH0Unit]
  exact k.hom.naturality (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

end AlgebraicGeometry
