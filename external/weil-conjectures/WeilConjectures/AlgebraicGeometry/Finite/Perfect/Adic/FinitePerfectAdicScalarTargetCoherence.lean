/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryScalarModelBase
public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarFiniteCoherence
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarFiniteComparison
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantPresentation
import all WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulFiniteQuotientComparison
import WeilConjectures.AlgebraicGeometry.CompletedConstantProjection.CompletedConstantResidueData

/-! # Transition compatibility of the completed finite comparison

Source: Stacks Project, Tags 093J and 093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] completedAdicChangeData completedAdicRing
  directCoefficientMap overDirectMap directCoefficientIso

private def restrictIdentity
    {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{t + 1}) :
    SheafOfModules.restrictScalars (𝟙 R) ≅ 𝟭 (SheafOfModules.{t + 1} R) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk
        (fun Z ↦ (ModuleCat.restrictScalarsId (R.obj.obj Z)).app (M.val.obj Z))
        (fun {Z Y} f ↦ by ext x; rfl))) (fun _ ↦ by ext Z x; rfl)

private lemma realization_ext
    (X : Scheme.{t}) {B : Type (t + 1)} [CommRing B]
    {S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (φ : adicLisseConstantRing X B ⟶ S) (N : ModuleCat.{t + 1} B)
    (T : SheafOfModules.{t + 1} ((adicLisseForget X).obj S))
    (f g : (completedAdicChange X φ).obj ((adicLisseConstantModules X B).obj N) ⟶ T)
    (h : ∀ (Z : X.ProEtᵒᵖ) (s : S.obj.obj Z) (x : N),
      f.val.app Z (completedAdicChangeTensor X φ ((adicLisseConstantModules X B).obj N)
        Z s (completedConstantGenerator X B N Z x)) =
      g.val.app Z (completedAdicChangeTensor X φ ((adicLisseConstantModules X B).obj N)
        Z s (completedConstantGenerator X B N Z x))) : f = g := by
  let e := (restrictIdentity ((adicLisseForget X).obj S)).app
    ((completedAdicChange X φ).obj ((adicLisseConstantModules X B).obj N))
  apply (cancel_epi e.hom).1
  apply CompletedConstantProjection.realization_hom_ext X φ (𝟙 S) N T
  intro Z s x
  exact h Z s x

private def targetStep
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc d.ideal (n + 1)) ⋙
        ModuleCat.restrictScalars (Ideal.Quotient.mk (d.ideal ^ (n + 1 + 1))) ⋙
        finitePerfectAdicScalarModelOrdinary X d ≅
      ModuleCat.restrictScalars (Ideal.Quotient.mk (d.ideal ^ (n + 1))) ⋙
        finitePerfectAdicScalarModelOrdinary X d :=
  isoWhiskerRight (ModuleCat.restrictScalarsComp'
    (Ideal.Quotient.mk (d.ideal ^ (n + 1 + 1)))
    (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
    (Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).symm).symm
    (finitePerfectAdicScalarModelOrdinary X d)

/-- Scalar tensors of constant generators determine an ordinary realization map.

Source: Stacks Project, Tags 06YY and 093J.
(blueprint: new-s3-finite-perfect-adic-scalar-target-coherence)

Proof: precompose with the identity restriction isomorphism and apply scalar-tensor
extensionality. Pure tensors generate the tensor presheaf, and constant generators
locally generate its module argument; sheafification extends the equality to all
sections. -/
theorem finitePerfectAdicScalarOrdinary_hom_ext
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : ModuleCat.{t} A) (T : CompletedAdicModules X d)
    (f g : (finitePerfectAdicScalarModelOrdinary X d).obj M ⟶ T)
    (h : ∀ (Z : X.ProEtᵒᵖ) (s : (completedAdicCommRing X d).obj.obj Z)
      (x : (finitePerfectAdicScalarModelLift A).obj M),
      f.val.app Z (completedAdicScalarTensor X d ((finitePerfectAdicConstant X A).obj M)
        Z s (completedConstantGenerator X (ULift.{t + 1} A)
          ((finitePerfectAdicScalarModelLift A).obj M) Z x)) =
      g.val.app Z (completedAdicScalarTensor X d ((finitePerfectAdicConstant X A).obj M)
        Z s (completedConstantGenerator X (ULift.{t + 1} A)
          ((finitePerfectAdicScalarModelLift A).obj M) Z x))) : f = g := by
  exact realization_ext X (completedAdicScalar X d)
    ((finitePerfectAdicScalarModelLift A).obj M) T f g h

private lemma ordinary_tensor_map
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    {M N : ModuleCat.{t} A} (f : M ⟶ N) (Z : X.ProEtᵒᵖ)
    (s : (completedAdicCommRing X d).obj.obj Z)
    (x : (finitePerfectAdicScalarModelLift A).obj M) :
    ((finitePerfectAdicScalarModelOrdinary X d).map f).val.app Z
      (completedAdicScalarTensor X d ((finitePerfectAdicConstant X A).obj M)
        Z s (completedConstantGenerator X (ULift.{t + 1} A)
          ((finitePerfectAdicScalarModelLift A).obj M) Z x)) =
    completedAdicScalarTensor X d ((finitePerfectAdicConstant X A).obj N)
      Z s (completedConstantGenerator X (ULift.{t + 1} A)
        ((finitePerfectAdicScalarModelLift A).obj N) Z
        ((finitePerfectAdicScalarModelLift A).map f x)) := by
  change ((completedAdicScalarExtension X d).map
    ((koszulConstantFunctor X A).map ((finitePerfectAdicScalarModelLift A).map f))).val.app Z
      _ = _
  erw [comparisonScalarTensor_map, CompletedConstantProjection.constant_map_generator]
  rfl

private lemma targetDirectIso_step
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) (n : ℕ)
    (N : ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))) :
    (targetDirectIso X d r a ha (n + 1)).hom.app
        ((ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).obj N) ≫
      (directFiniteStep X d n).hom.app N =
    (targetStep X d n).hom.app N ≫ (targetDirectIso X d r a ha n).hom.app N := by
  let Q := ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
  let L := ModuleCat.restrictScalars (Ideal.Quotient.mk (d.ideal ^ (n + 1 + 1)))
  let M := (finitePerfectAdicScalarModelLift A).obj (L.obj (Q.obj N))
  apply finitePerfectAdicScalarOrdinary_hom_ext X d (L.obj (Q.obj N)) ((directFinite X d n).obj N)
  intro Z s x
  change ((directFiniteStep X d n).hom.app N).val.app Z
      (((targetDirectIso X d r a ha (n + 1)).hom.app (Q.obj N)).val.app Z
        (completedAdicScalarTensor X d ((adicLisseConstantModules X (ULift.{t + 1} A)).obj M)
          Z s (completedConstantGenerator X (ULift.{t + 1} A) M Z x))) =
    ((targetDirectIso X d r a ha n).hom.app N).val.app Z
      (((targetStep X d n).hom.app N).val.app Z
        (completedAdicScalarTensor X d ((adicLisseConstantModules X (ULift.{t + 1} A)).obj M)
          Z s (completedConstantGenerator X (ULift.{t + 1} A) M Z x)))
  have hstep := ordinary_tensor_map X d
    ((ModuleCat.restrictScalarsComp'
      (Ideal.Quotient.mk (d.ideal ^ (n + 1 + 1)))
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
      (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
      (Ideal.Quotient.factor_comp_mk
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).symm).inv.app N) Z s x
  erw [hstep, targetDirectIso_tensor X d r a ha n N Z s x,
    targetDirectIso_tensor X d r a ha (n + 1) (Q.obj N) Z s x]
  let y : ((directFinite X d (n + 1)).obj (Q.obj N)).val.obj Z :=
    (directConstantUnit (ProEtale.finiteCoefficientScalarMap X
      (completedAdicQuotient d (n + 1)))
      ((finitePerfectAdicScalarModelLift (A ⧸ d.ideal ^ (n + 1 + 1))).obj
        (Q.obj N))).app Z x
  change ((directFiniteStep X d n).hom.app N).val.app Z (s • y) = _
  rw [(((directFiniteStep X d n).hom.app N).val.app Z).hom.map_smul]
  erw [(finiteTransition X d n).unit N Z x]
  rfl

end AlgebraicGeometry.Scheme
