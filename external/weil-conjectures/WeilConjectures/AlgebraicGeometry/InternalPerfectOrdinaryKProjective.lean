/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryReductions
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryTermsFree
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective

/-! # K-projectivity of ordinary reductions on a contractible final object -/

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

/-- On a scheme with weakly contractible final object, the explicit ordinary reductions
of a bounded-above finite-free scalar complex are K-projective.
Source: Stacks Tags 064B and 09C5.
(blueprint: lem-pe-internal-perfect-ordinary-kprojective).

Proof: exact final-object evaluation makes the sheafified constant integers projective.
Its canonical tensor-unit isomorphism makes the abelian tensor unit projective, hence
so is the regular module over every internal coefficient ring. The finite-free term
comparison makes every ordinary quotient term projective. The termwise additive
functors preserve the upper bound, so the bounded-above projective-complex criterion
applies. Rank zero and the empty scheme are covered by the same argument. -/
theorem internalPerfectOrdinaryReduction_kprojective (W : Scheme.{u})
    (hW : (Scheme.ProEt.topology W).IsWeaklyContractible.{u + 1}
      (Scheme.ProEt.mk (𝟙 W)))
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (b : ℤ) (hb : P.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) (n : ℕ) :
    CochainComplex.IsKProjective (internalPerfectOrdinaryReduction l E W P n) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : Projective (𝟙_ (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})) :=
    Projective.of_iso
      (asIso (Functor.LaxMonoidal.ε
        (presheafToSheaf (Scheme.ProEt.topology W) Ab.{u + 1}))).symm
      (projective_presheafToSheaf_const (Scheme.ProEt.isTerminalMkId W) hW)
  let : Projective (Mod.regular (AdicCompletion.finiteRing l E W n)) :=
    Mod.projective_regular
  have : ∀ i : ℤ, Projective ((internalPerfectOrdinaryReduction l E W P n).X i) := by
    intro i
    obtain ⟨r, ⟨e⟩⟩ := internalPerfectOrdinaryReduction_terms_free l E W P hfree n i
    apply Projective.of_iso e.symm
    unfold Mod.finiteFree
    constructor
    intro M N f e he
    refine ⟨biproduct.desc (fun j ↦ Projective.factorThru
      (biproduct.ι (fun _ : Fin r ↦
        Mod.regular (AdicCompletion.finiteRing l E W n)) j ≫ f) e), ?_⟩
    apply biproduct.hom_ext'
    intro j
    simp
  let := hb
  have : CochainComplex.IsStrictlyLE (internalPerfectOrdinaryReduction l E W P n) b := by
    unfold internalPerfectOrdinaryReduction internalPerfectIntegralComplex
    infer_instance
  exact CochainComplex.isKProjective_of_projective _ b

end AlgebraicGeometry.ProEtale
