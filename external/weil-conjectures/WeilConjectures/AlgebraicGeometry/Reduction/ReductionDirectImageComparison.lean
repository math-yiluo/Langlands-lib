/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageScalarExchange
public import WeilConjectures.AlgebraicGeometry.Open.OpenScalarExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact

/-!
# The canonical compact-support coefficient comparison

This definition interface reexports the existing constant direct image, scalar/pullback
comparison and its counit mate (`directImageConstantPush`, `directImageScalarPullbackIso`,
`directImageScalarComparison`), and `openExtension`, `openScalarIso`.
It uses their definitions, without invoking either scalar-exchange theorem.

The reexported `Scheme.openSquarePullbackModel_existsUnique` fixes
`Scheme.openSquarePullbackModel` uniquely: for every module M, site object V and
section s, its component at the base change of V sends the tensor-pullback unit
of s to the intrinsic-pullback unit of s. Explicitly, the equation is
`(e.hom.app M).val.app (op ((proEtaleBaseChange f).obj V))
  (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (op V) s) =
  ((sfIntrinsicConstantModuleAdjunction f A).unit.app M).val.app (op V) s`.
Its source and proof are in the declaration's docstring (Stacks 03D3, 00YV).
The unique normalized object, rather than a choice from bare existence, supplies the
change of coordinates used below. No existing definition is duplicated or renamed.

The four definitions below are: the open coordinate identification,
the transported open scalar isomorphism, Rp_* j_!, and its actual scalar comparison.

## References

* Stacks Tags 03DI and 03DJ
* Stacks Tags 03DI and 06YY
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Identify the recorded sheafified extension by zero with the normalized left adjoint
used by the open scalar comparison. The pullback coordinate change preserves the actual
constant-section unit. Uniqueness of left adjoints therefore fixes this identification. -/
def reductionOpenModel (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory ≅ openExtension (A := A) j :=
  mapDerivedCategoryNatIso
    (((sfIntrinsicOpenAdjunction A j).ofNatIsoRight
      (openSquarePullbackModel A j).symm).leftAdjointUniq
        (Adjunction.ofIsRightAdjoint (proEtaleConstantRingPullback A j)))

/-- The canonical B-linear open tensor comparison for the recorded extension by zero.
The outside factors only change its adjunction coordinates; the middle comparison is
fixed by the identity on restricted sections, hence by the usual balanced tensor map. -/
def reductionOpenScalarIso {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory ⋙ scalarExtensionFunctor φ Z ≅
      scalarExtensionFunctor φ X ⋙ (sfIntrinsicExtensionByZero j B).mapDerivedCategory :=
  isoWhiskerRight (reductionOpenModel A j) (scalarExtensionFunctor φ Z) ≪≫
    openScalarIso φ j ≪≫
      isoWhiskerLeft (scalarExtensionFunctor φ X) (reductionOpenModel B j).symm

/-- Compact support for the given open/proper factorization, exactly Rp_* j_!.
The open factor is the recorded sectionwise extension by zero, descended termwise. -/
abbrev reductionCompactSupport (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) :
    proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory Y A :=
  (sfIntrinsicExtensionByZero j A).mapDerivedCategory ⋙ directImageConstantPush A p

/-- The actual B-linear coefficient comparison b, natural on the entire ambient category.
Its proper factor is the mate of the canonical tensor/pullback comparison under the
specified derived geometric adjunctions; its open factor is the canonical tensor map. -/
def reductionDirectImageComparison {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B)
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) :
    reductionCompactSupport A j p ⋙ scalarExtensionFunctor φ Y ⟶
      scalarExtensionFunctor φ X ⋙ reductionCompactSupport B j p :=
  whiskerLeft (sfIntrinsicExtensionByZero j A).mapDerivedCategory
      (directImageScalarComparison φ p) ≫
    whiskerRight (reductionOpenScalarIso φ j).hom (directImageConstantPush B p)

end AlgebraicGeometry.ProEtale
