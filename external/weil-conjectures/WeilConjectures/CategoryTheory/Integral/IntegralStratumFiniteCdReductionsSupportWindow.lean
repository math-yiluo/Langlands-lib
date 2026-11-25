/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension

import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteQuotientSupportedClassicalWindow
import all WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientConstructible
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralPositiveReductionConstructible
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Supported cohomology of a finite integral reduction

Source: blueprint latest, `sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
the first two finite-reduction steps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- The continuous coefficient map, with both rings retained for dependent transport.
Source: actual quotient projection in the item node. -/
private def coefficientArrow (A B : Type u) [CommRing A] [CommRing B]
    (tA : TopologicalSpace A) (tB : TopologicalSpace B)
    (hA : @IsTopologicalRing A tA _) (hB : @IsTopologicalRing B tB _)
    (f : A →+* B) (hf : @Continuous A B tA tB f) :
    Arrow (Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :=
  letI := tA
  letI := tB
  letI := hA
  letI := hB
  letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A
  letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} B
  letI := Profinite.isMonHom_continuousMapRingObjMapOfUniverse.{u, u} f hf
  Arrow.mk (Mon.ofHom (Profinite.continuousMapRingObjMapOfUniverse f hf))

/-- Changing topologies by equality changes none of the bundled coefficient data. -/
private theorem coefficientArrow_eq (A B : Type u) [CommRing A] [CommRing B]
    (tA tA' : TopologicalSpace A) (tB tB' : TopologicalSpace B)
    (hA : @IsTopologicalRing A tA _) (hA' : @IsTopologicalRing A tA' _)
    (hB : @IsTopologicalRing B tB _) (hB' : @IsTopologicalRing B tB' _)
    (f : A →+* B) (hf : @Continuous A B tA tB f)
    (hf' : @Continuous A B tA' tB' f) (ha : tA = tA') (hb : tB = tB') :
    coefficientArrow A B tA tB hA hB f hf =
      coefficientArrow A B tA' tB' hA' hB' f hf' := by
  subst tA'
  subst tB'
  rfl

/-- The two norm presentations give the same actual positive quotient arrow.
Source: the spectral-norm coefficient comparison and the finite quotient calculation. -/
private theorem reductionArrow_eq (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    Arrow.mk (Mon.ofHom (DerivedNakayama.reductionRing l E (n + 1))) =
      Arrow.mk (Mon.ofHom (IntegralQuotient.reduction l E n)) := by
  have hm : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have ht := congrArg (fun m : PseudoMetricSpace E ↦
    m.toUniformSpace.toTopologicalSpace) hm.symm
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  have hd : AdicCompletion.finiteTopology l E (n + 1) =
      IntegralQuotient.quotientTopology l E n := by
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let := FiniteModelQuotient.finiteTopology_discrete l E n
    exact DiscreteTopology.eq_bot
  exact coefficientArrow_eq _ _ _ _ _ _ _ _ _ _ _ _ _ hti hd

-- The generalized coefficient arrow needs the exact module-derived functor instances.
-- Generalizing the coefficient arrow requires the module-derived category instances.
/-- The open restriction of supported sections of a finite reduction has cohomology
in `[-1,c+1]`, and its underlying cohomology sheaves are classical local torsion.

Source: blueprint latest, `sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
first two finite-reduction steps; Stacks Tags 0A45, 09B1 and 09AA.
(blueprint: lem-sfb-integral-stratum-finite-cd-reductions-support-window).

Proof: use the length-one uniformizer resolution to identify the scalar restriction
of the positive quotient reduction with the cone of the uniformizer power on N[0].
Its cohomology is the kernel in degree -1 and the cokernel in degree 0. Positive
reduction constructibility and finite-coefficient comparison show these sheaves
are classical, even when N has torsion. Identify the continuous integral and quotient
coefficient presentations with those of the supported-window theorem, transporting
the reduction map and restriction functor as well. The unit assumption on ell gives
invertibility in every residue field. Apply finite_quotient_supported_classical_window
with a=-1, b=0 and exponent n+1. It gives the claimed bound and classical local torsion
before restriction to S. Exact open inverse image commutes with homology; the
etale/pro-etale inverse-image comparison preserves classicality, and inverse image
preserves the filtered union of prime-power kernels. This gives both conclusions
on S. Zero N and empty strata give zero complexes, so require no extra hypotheses. -/
theorem integralStratumFiniteCdReductions_support_window
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X Z S V : Scheme.{u}) [IsNoetherian X]
    (hl : IsUnit (l : Γ(X, ⊤)))
    (i : Z ⟶ X) (v : S ⟶ Z) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion v] [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range j.base = (Set.range i.base)ᶜ)
    (c : ℕ)
    (hc : relativeCohomologicalDimension l (Fact.out : l.Prime) j ≤ c)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) X))
    (hN : IsConstantModelConstructible (IntegralQuotient.integral l E) X N)
    (n : ℕ) :
    let B := (IntegralQuotient.restrict l E X n).obj
      ((IntegralQuotient.scalar l E X n).obj ((DerivedCategory.singleFunctor _ 0).obj N))
    let K := (CondensedRing.upperStar (IntegralQuotient.integral l E) v).mapDerivedCategory.obj
      ((CondensedRing.closedSupport (IntegralQuotient.integral l E) i j).rightDerivedFunctor.obj B)
    (∀ q : ℤ, q < -1 ∨ (c : ℤ) + 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
    (∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K).X ∧
      IsEllPowerTorsionLocal l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj K).X) := by
  classical
  have : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    GrothendieckTopology.hasSheafify_of_essentiallySmall.{u + 2, u, u, u + 1} _ _
  let P : Arrow (Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) → Prop := fun f ↦
    ∀ (hA : IsCommMonObj f.left.X) (hB : IsCommMonObj f.right.X),
    letI := hA
    letI := hB
    ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj f.left.X X)),
    IsConstantModelConstructible f.left.X X M →
    let C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj f.right.X X)) :=
      (Mod.extendScalars (coefficientMap f.hom.hom X)).leftDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj M)
    let B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj f.left.X X)) :=
      (Mod.comap (coefficientMap f.hom.hom X)).mapDerivedCategory.obj C
    let K := (CondensedRing.upperStar f.left.X v).mapDerivedCategory.obj
      ((CondensedRing.closedSupport f.left.X i j).rightDerivedFunctor.obj B)
    (∀ q : ℤ, q < -1 ∨ (c : ℤ) + 1 < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
    (∀ q : ℤ,
      IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K).X ∧
      IsEllPowerTorsionLocal l (Fact.out : l.Prime)
        ((DerivedCategory.homologyFunctor _ q).obj K).X)
  have hP : P (Arrow.mk (Mon.ofHom (DerivedNakayama.reductionRing l E (n + 1)))) := by
    intro hA hB M hM
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) :=
      AdicCompletion.finiteTopology l E (n + 1)
    obtain ⟨hf, hd, hbound, hbc, _⟩ :=
      FiniteModelQuotient.finite_model_sheaf_quotient_constructible l E X M hM n
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let : Finite A := hf
    let : DiscreteTopology A := hd
    obtain ⟨e, _⟩ := FiniteDiscreteOrdinary.finiteCoefficientModelComparison A X
    let Q := (AdicCompletion.derivedReduction l E X n).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)
    let F := e.ordinary.functor ⋙ e.fixed.functor
    let U := sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1})
    have underlying (L : FiniteDiscreteOrdinary.Internal A X) :
        U.obj (F.obj L) ≅ L.X := by
      dsimp only [F, Functor.comp_obj]
      rw [e.ordinary_functor, e.fixed_functor]
      exact ObjectProperty.isoMk _
        (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl))
    have hclass (q : ℤ) :
        IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj Q).X := by
      have hfixed := (fixedCriterion A X e Q).mp hbc
      obtain ⟨L, hL, ⟨eL⟩⟩ := hfixed
      let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
      let H := (DerivedCategory.homologyFunctor _ q).obj L
      let eH := (C.mapDerivedCategoryHomologyFunctorIso q).app L ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso eL
      have hfixedclass : IsClassicalAbelian
          (U.obj ((DerivedCategory.homologyFunctor _ q).obj (F.mapDerivedCategory.obj Q))) :=
        CondensedRing.ab_classical_iso
          ((sheafComposeForget₂CompComparisonUpperStarIso (ULift.{u + 1} A) X).app H ≪≫
            U.mapIso eH) (CondensedRing.ab_classical_image X _)
      let eQ :
          U.obj ((DerivedCategory.homologyFunctor _ q).obj (F.mapDerivedCategory.obj Q)) ≅
            ((DerivedCategory.homologyFunctor _ q).obj Q).X :=
        U.mapIso ((F.mapDerivedCategoryHomologyFunctorIso q).app Q).symm ≪≫
          underlying ((DerivedCategory.homologyFunctor _ q).obj Q)
      apply CondensedRing.ab_classical_iso eQ
      exact @hfixedclass
    let (x : X) : Invertible (l : X.residueField x) :=
      (show IsUnit (l : X.residueField x) by
        simpa only [map_natCast] using hl.map
          ((X.presheaf.germ ⊤ x (by trivial)) ≫ X.residue x).hom).invertible
    have hij : Set.range i.base = (Set.range j.base)ᶜ := by rw [hcomp, compl_compl]
    have hs := CondensedRing.finite_quotient_supported_classical_window
      l E (n + 1) (by omega) X i j hij (-1) 0 (by omega) c hc Q
      (fun q hq ↦ hbound q (by rcases hq with hq | hq <;> omega)
        (by rcases hq with hq | hq <;> omega)) hclass
    let R := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap (DerivedNakayama.reductionRing l E (n + 1)) X)
    let B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (DerivedNakayama.integerRing l E) X)) := R.mapDerivedCategory.obj Q
    let K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (DerivedNakayama.integerRing l E) Z)) :=
      (CondensedRing.closedSupport (DerivedNakayama.integerRing l E) i j).rightDerivedFunctor.obj B
    have hKclass (q : ℤ) :
        IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj K).X := by
      intro I _ _ T
      exact (hs.2 q).1 T
    have hk : (l ^ (n + 1)) • 𝟙 K = 0 :=
      CondensedRing.functor_annihilator
        (CondensedRing.closedSupport (DerivedNakayama.integerRing l E) i j).rightDerivedFunctor
        B _ (CondensedRing.functor_annihilator R.mapDerivedCategory Q _
          (CondensedRing.window_quotient_annihilator l E X (n + 1) Q))
    refine ⟨?_, fun q ↦ ⟨?_, ?_⟩⟩
    · intro q hq
      apply Functor.isZero_homologyFunctor_mapDerivedCategory_obj
        (CondensedRing.upperStar (DerivedNakayama.integerRing l E) v)
      exact hs.1 q (by simpa using hq)
    · exact CondensedRing.module_classical_derived_pullback
        (DerivedNakayama.integerRing l E) v K hKclass q
    · let := CondensedRing.abSheafNatColimits S
      let H := DerivedCategory.homologyFunctor
        (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (DerivedNakayama.integerRing l E) S)) q
      have : H.Additive := by
        dsimp only [H]
        infer_instance
      apply (isEllPowerTorsion_iff_local l (Fact.out : l.Prime) _).mp
      apply CondensedRing.ell_torsion_of_annihilated l (Fact.out : l.Prime) _ (n + 1)
      exact CondensedRing.functor_annihilator
        (Mod.forget (D := Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (DerivedNakayama.integerRing l E) S)) _ _
        (CondensedRing.functor_annihilator H _ _
          (CondensedRing.functor_annihilator
            (CondensedRing.upperStar (DerivedNakayama.integerRing l E) v).mapDerivedCategory
            K _ hk))
  have h := congrArg P (reductionArrow_eq l E n)
  exact (h ▸ hP) (IntegralQuotient.integral_comm l E)
    (IntegralQuotient.finite_comm l E n) N hN

end CategoryTheory
