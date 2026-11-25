/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulFiniteQuotientComparison
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Exactness of completed constant realization

The finite quotient diagrams identify the concrete completed coefficient ring with
completion of the constant ring in the coefficient universe. Stacks Tag 093M then
supplies exact scalar extension, and Tag 093J supplies exact constant realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

private abbrev liftedIdeal {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    Ideal (ULift.{t + 1} A) :=
  d.ideal.comap (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom

private def liftedQuotientEquiv {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    (ULift.{t + 1} A) ⧸ liftedIdeal d ^ (n + 1) ≃+* completedAdicQuotient d n :=
  (Ideal.quotientEquiv _ _ (ULift.ringEquiv : ULift.{t + 1} A ≃+* A) (by
    rw [Ideal.map_pow]
    congr 1
    exact (Ideal.map_comap_of_surjective
      (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom
      ULift.down_surjective d.ideal).symm)).trans
      ULift.ringEquiv.symm

private theorem liftedQuotientEquiv_mk {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) (a : ULift.{t + 1} A) :
    liftedQuotientEquiv d n (Ideal.Quotient.mk (liftedIdeal d ^ (n + 1)) a) =
      ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a.down) := rfl

private def finiteConstantsIso (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    (adicLisseForget T).obj (adicLisseConstantRing T (completedAdicQuotient d n)) ≅
      completedAdicFiniteRing T d n := by
  have := CompletedConstantReduction.constantComparison_isIso T (completedAdicQuotient d n)
  exact (adicLisseForget T).mapIso (asIso
    (AdicCoefficients.constantComparison T (completedAdicQuotient d n))) ≪≫
      AdicCoefficients.finiteRingComparison T (completedAdicQuotient d n)

private theorem finiteConstantsIso_unit (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    Functor.whiskerRight (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (completedAdicQuotient d n))))
      (forget₂ CommRingCat RingCat) ≫ (finiteConstantsIso T d n).hom.hom =
        ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n) := by
  let J := ProEt.topology T
  let F := forget₂ CommRingCat.{t + 1} RingCat.{t + 1}
  change Functor.whiskerRight (toSheafify J _) F ≫
    (Functor.whiskerRight (AdicCoefficients.constantComparison T _).hom F ≫
      (AdicCoefficients.finiteRingComparison T _).hom.hom) = _
  rw [← Category.assoc, ← Functor.whiskerRight_comp]
  change Functor.whiskerRight (toSheafify J _ ≫
    sheafifyMap J (AdicCoefficients.constants T _)) F ≫ _ = _
  rw [← toSheafify_naturality, Functor.whiskerRight_comp, Category.assoc]
  have h := (AdicCoefficients.finiteRingComparison_exists T
    (completedAdicQuotient d n)).choose_spec.1.2
  change Functor.whiskerRight (AdicCoefficients.constants T _) F ≫
    (Functor.whiskerRight (toSheafify J _) F ≫
      (AdicCoefficients.finiteRingComparison_exists T _).choose.hom) = _
  rw [h]
  rfl

private def quotientComparisonIso (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    (adicLisseForget T).obj ((adicLisseRingSystem T (liftedIdeal d)).obj (op n)) ≅
      completedAdicFiniteRing T d n :=
  (adicLisseForget T).mapIso
    ((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).mapIso
      ((liftedQuotientEquiv d n).toCommRingCatIso)) ≪≫ finiteConstantsIso T d n

private theorem quotientComparisonIso_unit (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) (U : T.ProEtᵒᵖ)
    (a : (ULift.{t + 1} A) ⧸ liftedIdeal d ^ (n + 1)) :
    (quotientComparisonIso T d n).hom.hom.app U
      ((adicLisseConstantUnit T _).app U a) =
        (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app U
          (liftedQuotientEquiv d n a) := by
  have h := congrArg (fun k ↦ (k.app U).hom a)
    (toSheafify_naturality (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).map
        (CommRingCat.ofHom (liftedQuotientEquiv d n).toRingHom)))
  change (adicLisseConstantUnit T _).app U (liftedQuotientEquiv d n a) =
    ((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
      (CommRingCat.ofHom (liftedQuotientEquiv d n).toRingHom)).hom.app U
        ((adicLisseConstantUnit T _).app U a) at h
  change (finiteConstantsIso T d n).hom.hom.app U
    (((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
      (CommRingCat.ofHom (liftedQuotientEquiv d n).toRingHom)).hom.app U
        ((adicLisseConstantUnit T _).app U a)) = _
  rw [← h]
  exact congrArg (fun k ↦ (k.app U).hom (liftedQuotientEquiv d n a))
    (finiteConstantsIso_unit T d n)

private def quotientCommIso (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    (adicLisseRingSystem T (liftedIdeal d)).obj (op n) ≅
      completedAdicFiniteCommRing T d n :=
  (adicLisseForget T).preimageIso (quotientComparisonIso T d n)

private theorem quotientCommIso_unit (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) (U : T.ProEtᵒᵖ)
    (a : (ULift.{t + 1} A) ⧸ liftedIdeal d ^ (n + 1)) :
    (quotientCommIso T d n).hom.hom.app U
      ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of ((ULift.{t + 1} A) ⧸ liftedIdeal d ^ (n + 1))))).app U a) =
      (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app U
        (liftedQuotientEquiv d n a) := by
  have h := congrArg (fun k ↦ k.hom.app U ((adicLisseConstantUnit T _).app U a))
    ((adicLisseForget T).map_preimage
      (Y := completedAdicFiniteCommRing T d n) (quotientComparisonIso T d n).hom)
  exact h.trans (quotientComparisonIso_unit T d n U a)

private theorem quotientCommIso_step (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    (adicLisseRingSystem T (liftedIdeal d)).map (homOfLE (Nat.le_succ n)).op ≫
        (quotientCommIso T d n).hom =
      (quotientCommIso T d (n + 1)).hom ≫
        completedAdicQuotientCommMap T d (n + 1) n (Nat.le_succ n) := by
  let J := ProEt.topology T
  let q := Ideal.Quotient.factorPowSucc (liftedIdeal d) (n + 1)
  have hstep : (adicLisseRingSystem T (liftedIdeal d)).map
      (homOfLE (Nat.le_succ n)).op =
      (constantSheaf J CommRingCat.{t + 1}).map (CommRingCat.ofHom q) :=
    Functor.ofOpSequence_map_homOfLE_succ _ n
  rw [hstep]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (completedAdicFiniteCommRing T d n).property
  ext U x
  have hq := congrArg (fun k ↦ (k.app U).hom x)
    (toSheafify_naturality J ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom q)))
  change (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of ((ULift.{t + 1} A) ⧸ liftedIdeal d ^ (n + 1))))).app U (q x) =
    (((constantSheaf J CommRingCat.{t + 1}).map (CommRingCat.ofHom q)).hom.app U)
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of ((ULift.{t + 1} A) ⧸ liftedIdeal d ^ (n + 1 + 1))))).app U x) at hq
  change (quotientCommIso T d n).hom.hom.app U
    ((((constantSheaf J CommRingCat.{t + 1}).map (CommRingCat.ofHom q)).hom.app U)
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of ((ULift.{t + 1} A) ⧸ liftedIdeal d ^ (n + 1 + 1))))).app U x)) =
    (completedAdicQuotientCommMap T d (n + 1) n (Nat.le_succ n)).hom.app U
      ((quotientCommIso T d (n + 1)).hom.hom.app U ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of ((ULift.{t + 1} A) ⧸ liftedIdeal d ^ (n + 1 + 1))))).app U x))
  rw [← hq, quotientCommIso_unit, quotientCommIso_unit]
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app U
    (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a.down)) = _
  have hs := congrArg (fun k ↦ (k.app U).hom
    ((ProEtale.finiteCoefficientConstants T (completedAdicQuotient d (n + 1))).app U
      (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1 + 1)) a.down))))
    (toSheafify_naturality J (completedAdicFinitePresheafStep T d n))
  have hc : (completedAdicFinitePresheafStep T d n).app U
      ((ProEtale.finiteCoefficientConstants T (completedAdicQuotient d (n + 1))).app U
        (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1 + 1)) a.down))) =
      (ProEtale.finiteCoefficientConstants T (completedAdicQuotient d n)).app U
        (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a.down)) := by
    apply ContinuousMap.ext
    intro c
    rfl
  simp only [NatTrans.comp_app, RingCat.comp_apply] at hs
  rw [hc] at hs
  simpa only [completedAdicQuotientCommMap, completedAdicRingSystem,
    Functor.ofOpSequence_map_homOfLE_succ, completedAdicFiniteStep,
    ProEtale.finiteCoefficientScalarMap, NatTrans.comp_app, RingCat.comp_apply,
    CommRingCat.hom_ofHom, RingCat.Hom.hom, sheafifyMap, J,
    liftedQuotientEquiv_mk] using! hs

private theorem quotientComparisonIso_step (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    (adicLisseForget T).map
      ((adicLisseRingSystem T (liftedIdeal d)).map (homOfLE (Nat.le_succ n)).op) ≫
        (quotientComparisonIso T d n).hom =
      (quotientComparisonIso T d (n + 1)).hom ≫ completedAdicFiniteStep T d n := by
  have h := congrArg ((adicLisseForget T).map) (quotientCommIso_step T d n)
  have hs : (adicLisseForget T).map
      (completedAdicQuotientCommMap T d (n + 1) n (Nat.le_succ n)) =
        completedAdicFiniteStep T d n := by
    change (completedAdicRingSystem T d).map (homOfLE (Nat.le_succ n)).op = _
    exact Functor.ofOpSequence_map_homOfLE_succ (completedAdicFiniteStep T d) n
  simpa only [Functor.map_comp, quotientCommIso, Functor.preimageIso_hom,
    Functor.map_preimage, hs] using h

private instance completionForget_preservesLimits (T : Scheme.{t}) :
    PreservesLimitsOfShape ℕᵒᵖ (adicLisseForget T) := by
  have : PreservesLimitsOfShape ℕᵒᵖ
      (adicLisseForget T ⋙ sheafToPresheaf (ProEt.topology T) RingCat.{t + 1}) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (ProEt.topology T) CommRingCat.{t + 1} ⋙
        (Functor.whiskeringRight T.ProEtᵒᵖ CommRingCat.{t + 1} RingCat.{t + 1}).obj
          (forget₂ CommRingCat RingCat)))
  exact preservesLimitsOfShape_of_reflects_of_preserves (adicLisseForget T)
    (sheafToPresheaf (ProEt.topology T) RingCat.{t + 1})

private def quotientSystemIso (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) :
    adicLisseRingSystem T (liftedIdeal d) ⋙ adicLisseForget T ≅
      completedAdicRingSystem T d := by
  let η : adicLisseRingSystem T (liftedIdeal d) ⋙ adicLisseForget T ⟶
      completedAdicRingSystem T d :=
    NatTrans.ofOpSequence (fun n ↦ (quotientComparisonIso T d n).hom) (fun n ↦ by
      simpa only [Functor.comp_map, completedAdicRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ] using quotientComparisonIso_step T d n)
  have (j : ℕᵒᵖ) : IsIso (η.app j) := (quotientComparisonIso T d j.unop).isIso_hom
  have : IsIso η := NatIso.isIso_of_isIso_app η
  exact asIso η

private def completionComparisonIso (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) :
    adicLisseCompletedRing T (liftedIdeal d) ≅ completedAdicCommRing T d :=
  (adicLisseForget T).preimageIso
    (preservesLimitIso (adicLisseForget T) (adicLisseRingSystem T (liftedIdeal d)) ≪≫
      lim.mapIso (quotientSystemIso T d))

private theorem completionComparisonIso_projection (T : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (adicLisseForget T).map (completionComparisonIso T d).hom ≫
      completedAdicProjection T d n =
    (adicLisseForget T).map (limit.π (adicLisseRingSystem T (liftedIdeal d)) (op n)) ≫
      (quotientComparisonIso T d n).hom := by
  unfold completionComparisonIso
  rw [Functor.preimageIso_hom, Functor.map_preimage]
  change ((preservesLimitIso (adicLisseForget T)
    (adicLisseRingSystem T (liftedIdeal d))).hom ≫
      limMap (quotientSystemIso T d).hom) ≫ _ = _
  unfold completedAdicProjection
  rw [Category.assoc, limMap_π, ← Category.assoc, preservesLimitIso_hom_π]
  rfl

private theorem scalar_projection (T : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    completedAdicScalar T d ≫ completedAdicCommProjection T d n =
    (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (liftedIdeal d ^ (n + 1)))) ≫
        (quotientCommIso T d n).hom := by
  let J := ProEt.topology T
  let q := Ideal.Quotient.mk (liftedIdeal d ^ (n + 1))
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (completedAdicFiniteCommRing T d n).property
  ext U a
  have hq := congrArg (fun k ↦ (k.app U).hom a)
    (toSheafify_naturality J ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom q)))
  change (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of ((ULift.{t + 1} A) ⧸ liftedIdeal d ^ (n + 1))))).app U (q a) =
    (((constantSheaf J CommRingCat.{t + 1}).map (CommRingCat.ofHom q)).hom.app U)
      ((koszulConstantUnit T A).app U a) at hq
  change (completedAdicProjection T d n).hom.app U
    (((adicLisseForget T).map (completedAdicScalar T d)).hom.app U
      ((koszulConstantUnit T A).app U a)) =
    (quotientCommIso T d n).hom.hom.app U
      ((((constantSheaf J CommRingCat.{t + 1}).map (CommRingCat.ofHom q)).hom.app U)
        ((koszulConstantUnit T A).app U a))
  rw [← hq, quotientCommIso_unit, liftedQuotientEquiv_mk]
  exact (completedAdicScalar_exists T d).exists.choose_spec n U a

private theorem completionComparisonIso_scalar (T : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    completedAdicScalar T d ≫ (completionComparisonIso T d).inv ≫
      limit.π (adicLisseRingSystem T (liftedIdeal d)) (op n) =
    (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (liftedIdeal d ^ (n + 1)))) := by
  let F := adicLisseForget T
  let e := completionComparisonIso T d
  let π := limit.π (adicLisseRingSystem T (liftedIdeal d)) (op n)
  let q := (quotientComparisonIso T d n).hom
  have hπ : F.map e.hom ≫ completedAdicProjection T d n = F.map π ≫ q :=
    completionComparisonIso_projection T d n
  have hi : F.map e.inv ≫ F.map π ≫ q = completedAdicProjection T d n := by
    rw [← hπ, ← Category.assoc, ← Functor.map_comp, e.inv_hom_id,
      F.map_id, Category.id_comp]
  apply F.map_injective
  apply (cancel_mono q).1
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hi]
  have h := congrArg F.map (scalar_projection T d n)
  have hp : F.map (completedAdicCommProjection T d n) = completedAdicProjection T d n := by
    rfl
  rw [F.map_comp, F.map_comp, hp] at h
  dsimp only [F] at h ⊢
  simpa only [quotientCommIso, Functor.preimageIso_hom, Functor.map_preimage] using h

/-- Exactness of the concrete completed coefficient realization.
Source: Stacks Project, Tags 093J--093M.
(blueprint: new-s3-completed-koszul-finite-quotient-exactness).
Proof: identify the lifted quotient diagram with the concrete finite-function diagram.
The limit isomorphism preserves the prescribed scalar map, as checked on every residue.
Noetherian completed constant coefficients are flat, so scalar extension is exact.
Compose with exact constant module sheafification. -/
theorem completedKoszulFiniteQuotientExactness
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    let E := koszulConstantFunctor T A ⋙ completedAdicScalarExtension T d
    E.Additive ∧ PreservesFiniteLimits E ∧ PreservesFiniteColimits E := by
  have : IsNoetherianRing A := d.noetherian
  have : IsNoetherianRing (ULift.{t + 1} A) :=
    isNoetherianRing_of_ringEquiv A ULift.ringEquiv.symm
  have h := completed_constant_algebra_flat_quotients T (liftedIdeal d)
    (completedAdicCommRing T d) (completionComparisonIso T d) (completedAdicScalar T d)
    (completionComparisonIso_scalar T d)
  have he := (exactFunctor_iff (completedAdicScalarExtension T d)).1 h.2.1
  have : PreservesFiniteLimits (completedAdicScalarExtension T d) := he.1
  have : PreservesFiniteColimits (completedAdicScalarExtension T d) := he.2
  have hk : (koszulConstantFunctor T A).Additive ∧
      PreservesFiniteLimits (koszulConstantFunctor T A) ∧
      PreservesFiniteColimits (koszulConstantFunctor T A) :=
    commutativeSiteConstantModuleFunctor_exact (ProEt.topology T) (ULift.{t + 1} A)
  have := hk.1
  have := hk.2.1
  have := hk.2.2
  exact ⟨inferInstance, comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

end AlgebraicGeometry.Scheme
