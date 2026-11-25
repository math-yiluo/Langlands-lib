/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryScalarModelBase
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarFiniteComparison
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarTargetCoherence
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarFiniteCoherence
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicSourcePresentation
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarSourceComparison
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarComponentUnderlying

/-! # Rank-one ordinary scalar comparisons

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
  directCoefficientMap overDirectMap sourceDirectIso targetDirectIso directFiniteStep targetStep
  finiteTransition chartConstantsIso constantAssociatedIso overDirectIso directConstant
  directCoefficientIso finitePerfectAdicAssociatedCoherence sourceChartMap SourceChartSquare

private lemma sourceDirectIso_step
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ)
    (N : ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))) :
    (sourceDirectIso X d V U W f (n + 1)).hom.app
        ((ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).obj N) ≫
      (SheafOfModules.overFunctor (completedAdicRing X d) W).map
        ((directFiniteStep X d n).hom.app N) =
    (finitePerfectAdicOrdinaryScalarSourceStep X d V U W f n).hom.app N ≫
      (sourceDirectIso X d V U W f n).hom.app N := by
  have := finitePerfectAdicSliceScalar_injective X d W (n + 1)
  have := finitePerfectAdicSliceScalar_surjective X d W (n + 1)
  have := finitePerfectAdicSliceScalar_injective X d W n
  have := finitePerfectAdicSliceScalar_surjective X d W n
  have : Presheaf.IsLocallyInjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op
        (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d (n + 1)))) :=
    finitePerfectAdicSliceScalar_injective X d W (n + 1)
  have : Presheaf.IsLocallySurjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op
        (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d (n + 1)))) :=
    finitePerfectAdicSliceScalar_surjective X d W (n + 1)
  have : Presheaf.IsLocallyInjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op
        (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d n))) :=
    finitePerfectAdicSliceScalar_injective X d W n
  have : Presheaf.IsLocallySurjective ((ProEt.topology X).over W)
      (whiskerLeft (Over.forget W).op
        (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d n))) :=
    finitePerfectAdicSliceScalar_surjective X d W n
  have hs := sourcePastedStep_forget
    (R := (completedAdicFiniteRing X d (n + 1)).over W)
    (S := (completedAdicFiniteRing X d n).over W)
    (T := (completedAdicRing X d).over W) X V U W f
    (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    (finitePerfectAdicSliceScalar X d W (n + 1)) (finitePerfectAdicSliceScalar X d W n)
    (((ProEt.topology X).overPullback RingCat.{t + 1} W).map
      (completedAdicProjection X d (n + 1)))
    (((ProEt.topology X).overPullback RingCat.{t + 1} W).map
      (completedAdicFiniteStep X d n))
    (((ProEt.topology X).overPullback RingCat.{t + 1} W).map
      (completedAdicProjection X d n))
    (finitePerfectAdicSliceScalar_step X d W n)
    (finitePerfectAdicScalarModulesCoherence X d V U W f n)
    (fun L ↦ finitePerfectAdicScalarComponent_forget X d V U W f n L) N
  apply (SheafOfModules.toSheaf ((completedAdicRing X d).over W)).map_injective
  simp only [Functor.map_comp, sourceDirectIso_forget, forget_over,
    directFiniteStep, liftedConstantTransition_forget]
  delta finitePerfectAdicOrdinaryScalarSourceStep finitePerfectAdicScalarModelLiftStep
  erw [hs]
  simp only [Functor.map_comp, Category.assoc]
  ext Z x
  exact sourceChart_lifted_section X V U W f
    (R := completedAdicFiniteRing X d (n + 1)) (S := completedAdicFiniteRing X d n)
    (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d (n + 1)))
    (ProEtale.finiteCoefficientScalarMap X (completedAdicQuotient d n))
    (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    (completedAdicFiniteStep X d n) (finiteScalar_step X d n) N Z x

private lemma comparison_square
    {C : Type*} [Category C] {A₁ A₀ B₁ B₀ C₁ C₀ : C}
    (s₁ : A₁ ≅ B₁) (s₀ : A₀ ≅ B₀) (t₁ : C₁ ≅ B₁) (t₀ : C₀ ≅ B₀)
    (a : A₁ ⟶ A₀) (b : B₁ ⟶ B₀) (c : C₁ ⟶ C₀)
    (hs : s₁.hom ≫ b = a ≫ s₀.hom) (ht : t₁.hom ≫ b = c ≫ t₀.hom) :
    (s₁ ≪≫ t₁.symm).hom ≫ c = a ≫ (s₀ ≪≫ t₀.symm).hom := by
  apply (cancel_mono t₀.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [← ht, t₁.inv_hom_id_assoc]
  exact hs

/-- The ordinary comparison has a coherent rank-one quotient component.

Source: Stacks Project, Tags 093J and 093M; Tag 03CY for the associated module
sheaf.
(blueprint: new-s3-finite-perfect-adic-ordinary-scalar-components)

Proof: identify the constant sections after the etale and pro-etale inverse-image
maps, then use the completed finite-reduction comparison on the free rank-one
quotient.  Restriction along the next quotient is compatible with the two
projection maps, so the resulting family of component isomorphisms commutes on
the rank-one quotient object.  The construction is natural in the chart and
covers zero rings and empty charts.
-/
theorem finitePerfectAdicOrdinaryScalar_components
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) :
    ∃ e : ∀ n : ℕ, finitePerfectAdicOrdinaryScalarSource X d V U W f n ≅
        finitePerfectAdicOrdinaryScalarTarget X d W n,
      ∀ (n : ℕ),
        (e (n + 1)).hom.app
            ((ModuleCat.restrictScalars
              (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).obj
              (ModuleCat.of (A ⧸ d.ideal ^ (n + 1))
                (A ⧸ d.ideal ^ (n + 1)))) ≫
          (finitePerfectAdicOrdinaryScalarTargetStep X d W n).hom.app
            (ModuleCat.of (A ⧸ d.ideal ^ (n + 1))
              (A ⧸ d.ideal ^ (n + 1))) =
        (finitePerfectAdicOrdinaryScalarSourceStep X d V U W f n).hom.app
            (ModuleCat.of (A ⧸ d.ideal ^ (n + 1))
              (A ⧸ d.ideal ^ (n + 1))) ≫
          (e n).hom.app
            (ModuleCat.of (A ⧸ d.ideal ^ (n + 1))
              (A ⧸ d.ideal ^ (n + 1))) := by
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  let O := SheafOfModules.overFunctor (completedAdicRing X d) W
  let s := sourceDirectIso X d V U W f
  let t := fun n ↦ isoWhiskerRight (targetDirectIso X d r a ha n) O
  refine ⟨fun n ↦ s n ≪≫ (t n).symm, ?_⟩
  intro n
  let N := ModuleCat.of (A ⧸ d.ideal ^ (n + 1)) (A ⧸ d.ideal ^ (n + 1))
  let Q := ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
  have ht : (t (n + 1)).hom.app (Q.obj N) ≫
        O.map ((directFiniteStep X d n).hom.app N) =
      (finitePerfectAdicOrdinaryScalarTargetStep X d W n).hom.app N ≫
        (t n).hom.app N := by
    delta finitePerfectAdicOrdinaryScalarTargetStep
    simpa only [t, Q, targetStep,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.comp_map,
      Functor.map_comp] using
      congrArg O.map (targetDirectIso_step X d r a ha n N)
  have hs := sourceDirectIso_step X d V U W f n N
  apply comparison_square ((s (n + 1)).app (Q.obj N)) ((s n).app N)
    ((t (n + 1)).app (Q.obj N)) ((t n).app N)
    ((finitePerfectAdicOrdinaryScalarSourceStep X d V U W f n).hom.app N)
    (O.map ((directFiniteStep X d n).hom.app N))
    ((finitePerfectAdicOrdinaryScalarTargetStep X d W n).hom.app N)
  · exact hs
  · exact ht

end AlgebraicGeometry.Scheme
