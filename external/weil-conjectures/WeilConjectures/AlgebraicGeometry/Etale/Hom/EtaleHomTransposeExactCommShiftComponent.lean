/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarTensorShiftCancellation
import WeilConjectures.AlgebraicGeometry.Tensor.TensorHomShiftComparisonComponent
import WeilConjectures.Tactic.TransportExact

/-! # Fixed-degree étale Hom shift component

Source: Stacks Project, Tags 08JC and 08J9; blueprint
`lem-coef-etale-hom-transpose-exact-comm-shift-core`, proof steps 3--4.
This is the fixed-degree component equation, strictly simpler than the assembled
`NatTrans.CommShiftCore` because it has no extensional wrapper or composite shift
structures. The proof is the tensor--Hom diagram chase from the parent module.
(blueprint: lem-coef-etale-hom-transpose-exact-comm-shift-component) -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] _root_.DerivedCategory.monoidalClosed
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  _root_.DerivedCategory.instMonoidalCategory
  _root_.DerivedCategory.commShift₂CurriedTensor

private theorem comparison_natural_second
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (K : DerivedCategoryModule A X)
    {L L' : DerivedCategoryModule A X} (g : L ⟶ L') :
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj ((scalarExtension φ X).obj K)).map
        ((scalarExtension φ X).map g) ≫ (etaleHomTensorComparison X φ K L').hom =
      (etaleHomTensorComparison X φ K L).hom ≫ (scalarExtension φ X).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).map g) := by
  exact (etaleHomTensorComparison_existsUnique X φ).choose_spec.1.2.1 K g

/-- The evaluation transpose commutes, in a fixed degree `n` and at a fixed object `K`, with
the normalized shifts: those of `EtaleHomLeft` (`F(sA)` followed by the scalar shift) and of
`EtaleHomRight` (Hom of the inverse scalar shift followed by `sB`).
Source: Stacks Project, Tags 08JC and 08J9; blueprint `lemma-change-coefficients-internal-hom--1`,
proof paragraph 2.

Proof. Postcompose both sides with the inverse of the `sB` shift and transpose through the
tensor--Hom adjunction; the evaluation normalization `hB` turns the transposed right side
into signed tensor evaluation, i.e. tensor cancellation followed by evaluation. Tensor
cancellation is natural in its second variable (the `CommShift` compatibility of the
tensor bifunctor maps and naturality of `shiftFunctorCompIsoId`), so the shifted map can be
moved through it. Precompose with the tensor image of the scalar shift, an isomorphism;
replace the unshifted evaluation by the transpose equation `hv`; apply
`etaleHomTensorComparison_shiftCancellation` and the naturality of the binary tensor
comparison in its second variable. The composite obtained is the image under scalar
extension of the `sA` evaluation normalization `hA`, which is the transposed left side.
Cancelling the tensor image of the scalar shift and using injectivity of the adjunction's
`homEquiv` gives the equation.
(blueprint: lem-coef-etale-hom-transpose-exact-comm-shift-component) -/
theorem etaleHomComparison_reversedExact_commShift_component
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M)
    (hv : IsEtaleHomTranspose X φ M v)
    (sA : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ)
    (sB : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
      ((scalarExtension φ X).obj M)).CommShift ℤ)
    (hA : EtaleHomShiftNormalization (ModuleCat.{u + 1} A) X M sA)
    (hB : EtaleHomShiftNormalization (ModuleCat.{u + 1} B) X
      ((scalarExtension φ X).obj M) sB)
    (K : DerivedCategoryModule A X) (n : ℤ) :
    letI := etaleHomScalarCommShift X φ
    ((scalarExtension φ X).map ((sA.commShiftIso n).hom.app (op K)) ≫
      ((scalarExtension φ X).commShiftIso n).hom.app
        (((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).obj (op K))) ≫
      (v.app (op K))⟦n⟧' =
    v.app (op (K⟦-n⟧)) ≫
      ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
        ((scalarExtension φ X).obj M)).map
          ((((scalarExtension φ X).commShiftIso (-n)).inv.app K).op) ≫
      (sB.commShiftIso n).hom.app (op ((scalarExtension φ X).obj K)) := by
  let : (scalarExtension φ X).Additive := (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).left_adjoint_additive
  have h := @derivedTensorHomShiftComparison_component (ModuleCat.{u + 1} A)
    _ _ _ _
    _ _ _ _
    (ModuleCat.{u + 1} B)
    _ _ _ _
    _ _ _ _ X
    (scalarExtension φ X) inferInstance (etaleHomScalarCommShift X φ)
    (etaleHomTensorComparison X φ) M v (fun K ↦ by transport_exact hv K) sA sB hA hB
    (fun K L L' g ↦ comparison_natural_second X φ K g)
    (fun K L n ↦ etaleHomTensorComparison_shiftCancellation X φ K L n) K n
  -- `h` is the goal with the categories spelled as `DerivedCategory (Sheaf …)`; `exact h` makes
  -- the kernel unfold `derivedHom` under `Functor.map` (9 GB), so transport along small leaves.
  transport_exact h

end AlgebraicGeometry.Etale
