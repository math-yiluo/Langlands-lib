/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicSourcePresentation

/-! # Underlying abelian map of the ordinary scalar compositor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] completedAdicChangeData completedAdicRing

private lemma restrictedIso_forget
    {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{t + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    {M : SheafOfModules.{t + 1} S} (N : SheafOfModules.{t + 1} T)
    (e : M ≅ (SheafOfModules.restrictScalars b).obj N) :
    (SheafOfModules.toSheaf R).map
        (((SheafOfModules.restrictScalars a).mapIso e ≪≫
          finitePerfectAdicRestrictComp a b c h N).hom) =
      (SheafOfModules.toSheaf S).map e.hom := by
  simp only [Iso.trans_hom, Functor.map_comp, Functor.mapIso_hom, forget_restrict,
    finitePerfectAdicRestriction_forget_compositor]
  exact Category.comp_id _

/-- After forgetting scalars, the scalar compositor is its finite associated-sheaf map.

Source: Stacks Project, Tags 03CY and 06YY.
(blueprint: new-s3-finite-perfect-adic-scalar-component-underlying)

Proof: expand the scalar component into restriction of the finite associated-sheaf
comparison followed by the restriction compositor. Forgetting scalars removes the
first restriction, and the restriction compositor becomes the identity abelian
sheaf map. Functoriality and composition with the identity give the formula. -/
theorem finitePerfectAdicScalarComponent_forget
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ)
    (N : Sheaf (ProEt.topology U.left)
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) :
    have := ProEt.sliceDense X W
    have := finitePerfectAdicSliceScalar_injective X d W (n + 1)
    have := finitePerfectAdicSliceScalar_surjective X d W (n + 1)
    have := finitePerfectAdicSliceScalar_injective X d W n
    have := finitePerfectAdicSliceScalar_surjective X d W n
    let Q := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))
    let P := (((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
      (ProEt.topology W.left) (ModuleCat.{t + 1} Q)).inverse).obj
        ((ProEtale.localizationRestriction (ModuleCat.{t + 1} Q) f.left
          (finitePerfectAdicChartArrow_weaklyEtale V U W f)).obj N)
    let π := ((ProEt.topology X).overPullback RingCat.{t + 1} W)
    (SheafOfModules.toSheaf ((completedAdicRing X d).over W)).map
        (finitePerfectAdicScalarComponent X d V U W f n N).hom =
      (SheafOfModules.toSheaf ((completedAdicFiniteRing X d (n + 1)).over W)).map
        ((finitePerfectAdicAssociatedCoherence
          (finitePerfectAdicSliceScalar X d W (n + 1))
          (finitePerfectAdicSliceScalar X d W n)
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
          (π.map (completedAdicFiniteStep X d n))
          (finitePerfectAdicSliceScalar_step X d W n)).hom.app P) := by
  dsimp only
  unfold finitePerfectAdicScalarComponent
  exact restrictedIso_forget _ _ _ _ _ _

end AlgebraicGeometry.Scheme
