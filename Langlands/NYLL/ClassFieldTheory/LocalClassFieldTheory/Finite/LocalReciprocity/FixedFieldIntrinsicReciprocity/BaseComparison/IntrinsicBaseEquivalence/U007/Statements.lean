/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Extract the statements of M273.007 and M273.008 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean
at fbd320cd8b1b06487c58227e92eb135794267709 as closed Prop-valued
definitions without their proofs. Add the Langlands.NYLL namespace prefix and
the suffix Statement. Import the Library modules that publish the
declarations used instead of the source imports. Omit the noncomputable
section, the open lines LocalFieldTheory and KummerTheory, which these
statements do not use, and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U004.Definitions

/-!
# Intrinsic-to-ambient embedded base equivalence: application statements

Two closed propositions describing the value of
`intrinsicBaseEquivAmbientEmbeddedField` on an element `tau` of the intrinsic
base subgroup: it is the ambient subgroup element that corresponds to the
conjugate `e ∘ tau ∘ e⁻¹`, and it acts on `SeparableClosure K` by that
conjugate.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology
open ClassFormation

/-- The intrinsic-to-ambient equivalence is the fixed-field subgroup element
obtained by conjugating the intrinsic automorphism through the chosen
separable-closure equivalence. -/
def intrinsicBaseEquivAmbientEmbeddedField_applyStatement : Prop :=
  ∀ (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (i : F →ₐ[K] SeparableClosure K),
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (tau : (intrinsicAbstractBase F).toSubgroup),
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      letI hHabsolute : Finite
          ((baseField
            Gal(SeparableClosure K / K)).toSubgroup ⧸
            extensionSubgroup
              (baseField Gal(SeparableClosure K / K))
              H₀ (le_baseField H₀)) := by
        exact ambientEmbeddedAbsoluteQuotientFinite K F i
      let _H : FiniteAbstractField
          Gal(SeparableClosure K / K) :=
        ⟨H₀, hHabsolute⟩
      let F₀ :=
        abstractFixedField K (SeparableClosure K) H₀
      let hfixed :
          F₀ = AlgHom.fieldRange i :=
        InfiniteGalois.fixedField_fixingSubgroup
          (AlgHom.fieldRange i)
      let phi : F ≃+* F₀ :=
        ((i.equivFieldRange).trans
          (IntermediateField.equivOfEq hfixed.symm)).toRingEquiv
      let rho : Gal(SeparableClosure K / F₀) :=
        { e.symm.toRingEquiv.trans
            (tau.1.toRingEquiv.trans e.toRingEquiv) with
          commutes' := fun x => by
            change e (tau.1 (e.symm
              (algebraMap F₀ (SeparableClosure K) x))) =
                algebraMap F₀ (SeparableClosure K) x
            have hpre :
                e.symm
                    (algebraMap F₀ (SeparableClosure K) x) =
                  algebraMap F (SeparableClosure F) (phi.symm x) := by
              apply e.injective
              rw [e.apply_symm_apply, e.commutes]
              change (x : SeparableClosure K) =
                i (phi.symm x)
              rw [← show
                ((phi (phi.symm x) : F₀) :
                    SeparableClosure K) =
                  i (phi.symm x) by rfl,
                phi.apply_symm_apply]
            rw [hpre, tau.1.commutes, e.commutes]
            change i (phi.symm x) = (x : SeparableClosure K)
            rw [← show
              ((phi (phi.symm x) : F₀) :
                  SeparableClosure K) =
                i (phi.symm x) by rfl,
              phi.apply_symm_apply] }
      intrinsicBaseEquivAmbientEmbeddedField K F i e tau =
        (abstractSubgroupEquivGaloisGroup
          K (SeparableClosure K) H₀).symm rho

/-- The embedded-field base equivalence acts on the ambient separable closure
by conjugating the intrinsic automorphism through the chosen equivalence. -/
def intrinsicBaseEquivAmbientEmbeddedField_apply_valStatement : Prop :=
  ∀ (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (i : F →ₐ[K] SeparableClosure K),
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (tau : (intrinsicAbstractBase F).toSubgroup)
      (x : SeparableClosure K),
      (intrinsicBaseEquivAmbientEmbeddedField
        K F i e tau).1.1 x =
        e (tau.1 (e.symm x))

end Langlands.NYLL.LocalClassFieldTheory
