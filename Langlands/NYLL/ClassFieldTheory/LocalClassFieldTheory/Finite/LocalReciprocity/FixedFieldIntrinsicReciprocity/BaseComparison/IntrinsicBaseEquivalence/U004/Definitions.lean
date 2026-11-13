/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.U004.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U001.Proofs

/-!
# Intrinsic-to-ambient base equivalences

Adapted by Worker 57 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology
open ClassFormation

/-- A separable-closure equivalence identifies the intrinsic base subgroup of a
finite fixed field with its defining subgroup in the ambient Galois group. -/
noncomputable def intrinsicBaseEquivAmbientFixedField
    (K : Type) [Field K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K/K)) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) →
      (intrinsicAbstractBase F).toSubgroup ≃*
        H.field.toSubgroup := by
  dsimp only
  let F := abstractFixedField K (SeparableClosure K) H.field
  letI : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  intro e
  let φ :
      Gal(SeparableClosure F / F) ≃*
        H.field.toSubgroup :=
    (AlgEquiv.autCongr e).trans
      (abstractSubgroupEquivGaloisGroup
        K (SeparableClosure K) H.field).symm
  exact (intrinsicAbstractBaseEquivAbsolute F).trans φ

/-- For an embedded finite separable extension, transport through a
separable-closure equivalence identifies its intrinsic base subgroup with the
ambient subgroup fixing the embedding's field range. -/
noncomputable def
    intrinsicBaseEquivAmbientEmbeddedField
    (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) →
      (intrinsicAbstractBase F).toSubgroup ≃*
        (closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)).toSubgroup := by
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
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
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, hHabsolute⟩
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  letI : FiniteDimensional K F₀ :=
    ((AlgEquiv.ofInjectiveField i).trans
      (IntermediateField.equivOfEq
        (InfiniteGalois.fixedField_fixingSubgroup
          (AlgHom.fieldRange i)).symm)).toLinearEquiv.finiteDimensional
  letI : Algebra.IsSeparable F₀ (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F₀ (SeparableClosure K)
  letI : IsSepClosure F₀ (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  letI : Algebra F₀ (SeparableClosure F₀) :=
    (separableClosure F₀ (AlgebraicClosure F₀)).algebra
  let e₀ : SeparableClosure F₀ ≃ₐ[F₀] SeparableClosure K :=
    IsSepClosure.equiv F₀
      (SeparableClosure F₀) (SeparableClosure K)
  have hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiAlg : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let phi : F ≃+* F₀ := phiAlg.toRingEquiv
  let c : SeparableClosure F ≃+* SeparableClosure F₀ :=
    e.toRingEquiv.trans e₀.symm.toRingEquiv
  have hc (x : F) :
      c (algebraMap F (SeparableClosure F) x) =
        algebraMap F₀ (SeparableClosure F₀) (phi x) := by
    change e₀.symm
        (e (algebraMap F (SeparableClosure F) x)) =
      algebraMap F₀ (SeparableClosure F₀) (phi x)
    apply e₀.injective
    rw [e₀.apply_symm_apply, e.commutes, e₀.commutes]
    rfl
  let theta :
      Gal(SeparableClosure F / F) ≃*
        Gal(SeparableClosure F₀ / F₀) := {
    toFun := fun sigma =>
      { c.symm.trans (sigma.toRingEquiv.trans c) with
        commutes' := fun x => by
          change c (sigma (c.symm
            (algebraMap F₀ (SeparableClosure F₀) x))) =
              algebraMap F₀ (SeparableClosure F₀) x
          have hpre :
              c.symm
                  (algebraMap F₀ (SeparableClosure F₀) x) =
                algebraMap F (SeparableClosure F) (phi.symm x) := by
            apply c.injective
            rw [c.apply_symm_apply, hc, phi.apply_symm_apply]
          rw [hpre, sigma.commutes, hc, phi.apply_symm_apply] }
    invFun := fun tau =>
      { c.trans (tau.toRingEquiv.trans c.symm) with
        commutes' := fun x => by
          change c.symm (tau (c
            (algebraMap F (SeparableClosure F) x))) =
              algebraMap F (SeparableClosure F) x
          rw [hc, tau.commutes]
          apply c.injective
          rw [c.apply_symm_apply, hc] }
    left_inv := fun sigma => by
      apply AlgEquiv.ext
      intro x
      change c.symm
          (c (sigma (c.symm (c x)))) = sigma x
      rw [c.symm_apply_apply, c.symm_apply_apply]
    right_inv := fun tau => by
      apply AlgEquiv.ext
      intro x
      change c
          (c.symm (tau (c (c.symm x)))) = tau x
      rw [c.apply_symm_apply, c.apply_symm_apply]
    map_mul' := fun sigma tau => by
      apply AlgEquiv.ext
      intro x
      change c (sigma (tau (c.symm x))) =
        c (sigma (c.symm (c (tau (c.symm x)))))
      rw [c.symm_apply_apply] }
  let psi₀ :=
    intrinsicBaseEquivAmbientFixedField K H e₀
  exact
    (intrinsicAbstractBaseEquivAbsolute F).trans
      (theta.trans
        ((intrinsicAbstractBaseEquivAbsolute F₀).symm.trans psi₀))

end Langlands.NYLL.LocalClassFieldTheory
