/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryReductions
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.CategoryTheory.HomCongr
public import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryKProjective
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleSelf
import WeilConjectures.AlgebraicGeometry.InternalPerfectIntegralKFlat
import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryReductions
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryTermsFree

/-! # Canonical levelwise comparison with ordinary homotopy endomorphisms -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual derived extension counit is invertible on the integral scalar complex.
Source: Stacks Tag 06YY.
(blueprint: def-pe-internal-perfect-reduction-hom-equiv).
Proof: the integral complex is K-flat, so the defining left derived functor computes
ordinary extension on this complex. Apply the K-flat counit criterion. -/
theorem internalPerfectReductionCounit_isIso (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) (n : ℕ) :
    IsIso ((Mod.extendScalars (AdicCompletion.quotient l E W n)).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (internalPerfectIntegralComplex l E W P))) :=
  CategoryTheory.Functor.isIso_leftDerivedFunctorCounit_app_of_kFlat
    (Mod.extendScalars (AdicCompletion.quotient l E W n)) _
      (internalPerfectIntegralComplex_kflat l E W P a b ha hb hfree)

/-- Canonical comparison of actual derived reduction with the localized ordinary model.
It is the derived counit, preceded by the quotient factorization of the integral complex.
Source: Stacks Tag 06YY.
(blueprint: def-pe-internal-perfect-reduction-hom-equiv). -/
def internalPerfectReductionOrdinaryIso (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) (n : ℕ) :
    (AdicCompletion.derivedReduction l E W n).obj (internalPerfectScalarModel l E W P) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (internalPerfectOrdinaryReduction l E W P n)) :=
  letI := internalPerfectReductionCounit_isIso l E W P a b ha hb hfree n
  (AdicCompletion.derivedReduction l E W n).mapIso
    ((DerivedCategory.quotientCompQhIso _).app
      (internalPerfectIntegralComplex l E W P)).symm ≪≫
    asIso ((Mod.extendScalars (AdicCompletion.quotient l E W n)).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (internalPerfectIntegralComplex l E W P)))

/-- Endomorphism comparison fixed by the derived counit and K-projective localization.
The inverse of localization is uniquely determined by the localization bijection.
Source: Stacks Tags 06YY and 064B.
(blueprint: def-pe-internal-perfect-reduction-hom-equiv). -/
def internalPerfectReductionHomEquiv (X : Scheme.{u}) (W : X.ProEt)
    (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) (n : ℕ) :
    internalReductionHom l E W.left (internalPerfectScalarModel l E W.left P)
        (internalPerfectScalarModel l E W.left P) n ≃
      internalPerfectOrdinaryHom l E W.left P n :=
  letI := internalPerfectOrdinaryReduction_kprojective l E W.left
    (Scheme.ProEt.isWeaklyContractible_self_of_object X W hW) P b hb hfree n
  let e := internalPerfectReductionOrdinaryIso l E W.left P a b ha hb hfree n
  (e.homCongr e).trans
    (Equiv.ofBijective DerivedCategory.Qh.map
      (CochainComplex.IsKProjective.Qh_map_bijective
        (internalPerfectOrdinaryReduction l E W.left P n) _)).symm

/-- Localization of the canonical Hom comparison is conjugation by the model isomorphism.
Source: the uniquely determined inverse of K-projective localization.
(blueprint: def-pe-internal-perfect-reduction-hom-equiv).
Proof: localization and its inverse cancel; the Hom congruence is conjugation. -/
theorem internalPerfectReductionHomEquiv_localize (X : Scheme.{u}) (W : X.ProEt)
    (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) (n : ℕ)
    (f : internalReductionHom l E W.left (internalPerfectScalarModel l E W.left P)
      (internalPerfectScalarModel l E W.left P) n) :
    DerivedCategory.Qh.map (internalPerfectReductionHomEquiv l E X W hW P a b ha hb hfree n f) =
      (internalPerfectReductionOrdinaryIso l E W.left P a b ha hb hfree n).inv ≫ f ≫
        (internalPerfectReductionOrdinaryIso l E W.left P a b ha hb hfree n).hom := by
  let := internalPerfectOrdinaryReduction_kprojective l E W.left
    (Scheme.ProEt.isWeaklyContractible_self_of_object X W hW) P b hb hfree n
  let q := Equiv.ofBijective DerivedCategory.Qh.map
    (CochainComplex.IsKProjective.Qh_map_bijective
      (internalPerfectOrdinaryReduction l E W.left P n)
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (internalPerfectOrdinaryReduction l E W.left P n)))
  change q (q.symm _) = _
  exact q.apply_symm_apply _

/-- The successor derived counit intertwines ordinary reduction of endomorphisms.
Source: naturality of the universal derived counit and ordinary balancing.
(blueprint: def-pe-internal-perfect-reduction-hom-equiv).
Proof: apply counit naturality to the homotopy endomorphism, then cancel the ordinary
balancing isomorphism with its inverse. No flatness assumption is needed for this identity. -/
theorem internalPerfectOrdinaryStepCounit_naturality (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (n : ℕ) (f : internalPerfectOrdinaryHom l E W P (n + 1)) :
    let F := Mod.extendScalars (AdicCompletion.transition l E W n)
    let a := internalPerfectOrdinaryReductionStep l E W P n
    F.leftDerivedFunctor.map (DerivedCategory.Qh.map f) ≫
        F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (internalPerfectOrdinaryReduction l E W P (n + 1))) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map a.hom) =
      F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (internalPerfectOrdinaryReduction l E W P (n + 1))) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map a.hom) ≫
        DerivedCategory.Qh.map (internalPerfectOrdinaryHomStep l E W P n f) := by
  let F := Mod.extendScalars (AdicCompletion.transition l E W n)
  let H := HomotopyCategory.quotient
    (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (AdicCompletion.finiteRing l E W n)) (.up ℤ)
  let a := internalPerfectOrdinaryReductionStep l E W P n
  have hb : H.map a.hom ≫ internalPerfectOrdinaryHomStep l E W P n f =
      (F.mapHomotopyCategory (.up ℤ)).map f ≫ H.map a.hom := by
    simp [internalPerfectOrdinaryHomStep, a, H, F, ← Functor.map_comp_assoc]
  have hn := F.leftDerivedFunctorCounit.naturality f
  dsimp only [Functor.comp_map] at hn
  change F.leftDerivedFunctor.map (DerivedCategory.Qh.map f) ≫
      F.leftDerivedFunctorCounit.app _ ≫ DerivedCategory.Qh.map (H.map a.hom) = _
  rw [reassoc_of% hn, ← DerivedCategory.Qh.map_comp, ← hb,
    DerivedCategory.Qh.map_comp]

end AlgebraicGeometry.ProEtale
