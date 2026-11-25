/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueStratumInput
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueStratumScalar
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # Ordinary constant modules under normalized stratum coefficient transport

## References

* Bhatt--Scholze, Lemma 6.5.8(1) and Proposition 6.6.11
* Bhatt--Scholze, Lemma 6.5.8(1), Proposition 6.6.11, and the normalized coefficient presentations
  in Definition 6.5.1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

namespace IntegralResidueOrdinaryProof

private def constantPF (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))

private def constantPresheafHomEquiv (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) (M : ModuleCat.{u + 1} A)
    (F : _root_.PresheafOfModules.{u + 1} ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))) :
    ((constantPF X A).obj M ⟶ F) ≃ (M ⟶ F.obj (op T)) where
  toFun f := f.app (op T)
  invFun q :=
    { app U := q ≫ F.map (hT.from U.unop).op
      naturality := by
        intro U V a
        ext x
        symm
        change F.map a (F.map (hT.from U.unop).op (q x)) =
          F.map (hT.from V.unop).op (q x)
        rw [← F.map_comp_apply]
        have h : (hT.from U.unop).op ≫ a = (hT.from V.unop).op := by
          exact congrArg Quiver.Hom.op (hT.hom_ext _ _)
        rw [h] }
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact (PresheafOfModules.naturality_apply f (hT.from U.unop).op x).symm
  right_inv q := by
    have h : hT.from T = 𝟙 T := hT.hom_ext _ _
    ext x
    change F.map (hT.from T).op (q x) = q x
    rw [h]
    simp
    rfl

private def constantPFAdj (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) :
    constantPF X A ⊣ PresheafOfModules.evaluation _ (op T) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantPresheafHomEquiv X A T hT
      homEquiv_naturality_left_symm := by
        intros
        apply PresheafOfModules.hom_ext
        intro U
        rfl
      homEquiv_naturality_right := by intros; rfl }

private def constantGlobal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) :=
  SheafOfModules.forget (adicLisseRing X A) ⋙
    PresheafOfModules.restrictScalars (adicLisseConstantUnit X A) ⋙
      PresheafOfModules.evaluation _ (op T)

private def constantAdj (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (T : X.ProEt) (hT : IsTerminal T) :
    adicLisseConstantModules X A ⊣ constantGlobal X A T :=
  (constantPFAdj X A T hT).comp
    (PresheafOfModules.sheafificationAdjunction (adicLisseConstantUnit X A))

private def integralGlobal {A : Type (u + 1)} [CommRing A]
    (X : Scheme.{u}) (d : AdicCoefficientDatum A) (T : X.ProEt) :=
  pbcRestrict (exchangeScalar d X) ⋙ constantGlobal X A T

private def integralAdj {A : Type (u + 1)} [CommRing A]
    (X : Scheme.{u}) (d : AdicCoefficientDatum A) (T : X.ProEt) (hT : IsTerminal T) :
    integralConstantModule X d ⊣ integralGlobal X d T := by
  let pd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let e := proEtaleScalarEquivalence X
    ((adicLisseForget X).mapIso (pbcCompletedComparison X d).symm)
  let adj := ((constantAdj X A T hT).comp
    (adicDatumOrdinaryAdjunction X (adicDatumScalar X pd))).comp e.toAdjunction
  exact adj

end IntegralResidueOrdinaryProof

attribute [local irreducible] integralConstantModule completedAdicChange

/-- The ordinary constant-module realization commutes with normalized coefficient
transport and inverse image. This concerns modules, without complexes or perfectness. -/
theorem integralResidueStratum_ordinary
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{u}) (g : S ⟶ T)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hd : d.ideal = Ideal.span {Padic.coefficientExtensionUniformizer l E})
    (c : IntegralResidueCoefficientModel l E d S) :
    Nonempty
      ((integralConstantModule T (pbcIntegralDatum l E) ⋙
          proEtaleRingModulePullback g (pbcAdicCompletion T (pbcIntegralDatum l E))
            ((adicTowerInverseImage g).obj (pbcAdicCompletion T (pbcIntegralDatum l E)))
            (Iso.refl _) ⋙
          pbcRestrict (integralResidueStratumCoefficient T l E S g d c).inv) ≅
        koszulConstantFunctor S (Padic.coefficientExtensionIntegers l E) ⋙
          completedAdicChange S (completedAdicScalar S d)) := by
  let A := PbcIntegralRing l E
  let D := pbcIntegralDatum l E
  let R := pbcAdicCompletion T D
  let R' := (adicTowerInverseImage g).obj R
  let e := integralResidueStratumCoefficient T l E S g d c
  let U := ⊤_ T.ProEt
  let hU := terminalIsTerminal (C := T.ProEt)
  let V := (proEtaleBaseChange g).obj U
  let hV := hU.isTerminalObj (proEtaleBaseChange g)
  let E' := proEtaleScalarEquivalence S ((adicLisseForget S).mapIso e.symm)
  let aL := ((IntegralResidueOrdinaryProof.integralAdj T D U hU).comp
    (proEtaleRingModuleAdjunction g R R' (Iso.refl _))).comp E'.toAdjunction
  obtain ⟨aX, _⟩ := completedAdjunction S (completedAdicScalar S d)
  let aR := (IntegralResidueOrdinaryProof.constantAdj S A V hV).comp aX
  let rightIso : E'.inverse ⋙
      proEtaleRingModuleDirectImage g R R' (Iso.refl _) ⋙
        IntegralResidueOrdinaryProof.integralGlobal T D U ≅
      completedRestriction S (completedAdicScalar S d) ⋙
        IntegralResidueOrdinaryProof.constantGlobal S A V :=
    NatIso.ofComponents (fun M ↦ by
      let z : ((E'.inverse ⋙
          proEtaleRingModuleDirectImage g R R' (Iso.refl _) ⋙
            IntegralResidueOrdinaryProof.integralGlobal T D U).obj M) ≃ₗ[A]
          ((completedRestriction S (completedAdicScalar S d) ⋙
            IntegralResidueOrdinaryProof.constantGlobal S A V).obj M) :=
        { toFun := id
          invFun := id
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro a x
            let x' : M.val.obj (op V) := x
            change
              (e.hom.hom.app (op V)
                ((proEtaleRingDirectImageMap g R R' (Iso.refl _)).hom.app (op U)
                  ((exchangeScalar D T).hom.app (op U)
                    ((adicLisseConstantUnit T A).app (op U) a)))) • x' =
                ((completedAdicScalar S d).hom.app (op V)
                  ((adicLisseConstantUnit S A).app (op V) a)) • x'
            exact congrArg (fun b : (completedAdicCommRing S d).obj.obj (op V) ↦ b • x')
              (integralResidueStratum_scalar T l E S g d hd c (op U) a) }
      exact z.toModuleIso) (by intros; ext x; rfl)
  exact ⟨(aL.ofNatIsoRight rightIso).leftAdjointUniq aR⟩

end AlgebraicGeometry.Scheme
