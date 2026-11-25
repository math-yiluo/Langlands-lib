/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleResidueTorTest

/-!
# The residue test on the small pro-etale site, without auxiliary hypotheses

`proEtale_torAmplitude_iff_residue_tensor` carries a finite-field datum, an invertibility
assumption on `l` and a constructibility assumption which its proof never uses. This file
records the same statement without them, so that it applies over an arbitrary scheme.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
/-- Tor amplitude over `A = A_{E,n}` is detected by derived tensor with `A/(ϖ_E)`, for an
arbitrary cochain complex `K` on the pro-etale site of an arbitrary scheme `T` and any
K-flat resolution `f: P ⟶ K`. This is `proEtale_torAmplitude_iff_residue_tensor` without
its unused finite-field, invertibility and constructibility hypotheses. -/
theorem proEtale_torAmplitude_iff_residue_tensor'
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    (K P : CochainComplex (proEtaleRingModules T
      (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) ℤ)
    (f : P ⟶ K) (hf : QuasiIso f)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)) P)
    (a b : ℤ) (hab : a ≤ b) :
    HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E n)
      (DerivedCategory.Q.obj K) a b ↔
      ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor (proEtaleRingModules T
          (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) i).obj
            (derivedTensorRing T (Padic.coefficientExtensionRing l E n)
              (Padic.coefficientExtensionRing l E n ⧸ Ideal.span
                {Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
                  (Padic.coefficientExtensionUniformizer l E)})
              (Ideal.Quotient.mk _) K P f hf hP)) := by
  constructor
  · intro h
    exact h.2 K P ⟨Iso.refl _⟩ f hf hP _
  · intro h
    let A := Padic.coefficientExtensionRing l E n
    let R := proEtaleConstantRing T A
    let 𝒜 := proEtaleRingModules T R
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.tensorPreadditive.{u + 1, u, u + 1} R
    let r : A := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
      (Padic.coefficientExtensionUniformizer l E)
    let B := A ⧸ Ideal.span {r}
    let RB := proEtaleConstantRing T B
    let SB := (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RB
    let α : ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶ SB :=
      (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk (Ideal.span {r})))))
    let N : 𝒜 := (SheafOfModules.restrictScalars.{u + 1} α).obj (SheafOfModules.unit SB)
    obtain ⟨Q, g, hQ, hflat, hg, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
    have hQ : Q.IsAcyclicTensorKFlat := hQ
    have := hf
    have := hg
    let ePQ : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q :=
      asIso (DerivedCategory.Q.map f) ≪≫ (asIso (DerivedCategory.Q.map g)).symm
    have hres (i : ℤ) (hi : i < a ∨ b < i) :
        IsZero ((((tensorRight N).mapHomologicalComplex (.up ℤ)).obj Q).homology i) := by
      have hz := h i hi
      have hzP := hz.of_iso
        (ResidueTensor.derivedTensor_module_homology_iso T A K P f hf hP N i).symm
      obtain ⟨e⟩ := ResidueTensor.termwise_tensor_homology_iso R P Q N hP hQ ePQ i
      exact hzP.of_iso e.symm
    have hall (M : 𝒜) (i : ℤ) (hi : i < a ∨ b < i) :
        IsZero ((((tensorRight M).mapHomologicalComplex (.up ℤ)).obj Q).homology i) := by
      apply ResidueTensor.property_of_nilpotent (ResidueTensor.scalarNatTrans T A r)
        (fun M ↦ IsZero ((((tensorRight M).mapHomologicalComplex (.up ℤ)).obj Q).homology i))
        ?_ ?_ ?_ n M
        (ResidueTensor.scalarNatTrans_nilpotent T A r n
          (ResidueTensor.uniformizer_nilpotent l E n) M)
      · intro M hM
        apply HomologicalComplex.ExactAt.isZero_homology
        apply HomologicalComplex.ExactAt.of_isZero
        exact (tensorLeft (Q.X i)).map_isZero hM
      · intro S hS h₁ h₃
        exact ResidueTensor.tensor_homology_extension R Q hflat S hS i h₁ h₃
      · intro M hM
        apply proEtale_residue_module_tensor_homology T A r
          (ResidueTensor.residue_isMaximal l E n hn) Q M ?_ i (hres i hi)
        intro U x
        exact congrArg (fun z ↦ z.val.app U x) hM
    refine ⟨hab, ?_⟩
    intro L P' e f' hf' hP' M i hi
    obtain ⟨e⟩ := e
    have := hf'
    let eQP' : DerivedCategory.Q.obj Q ≅ DerivedCategory.Q.obj P' :=
      asIso (DerivedCategory.Q.map g) ≪≫ e.symm ≪≫
        (asIso (DerivedCategory.Q.map f')).symm
    obtain ⟨c⟩ := ResidueTensor.termwise_tensor_homology_iso R Q P' M hQ hP' eQP' i
    exact ((hall M i hi).of_iso c.symm).of_iso
      (ResidueTensor.derivedTensor_module_homology_iso T A L P' f' hf' hP' M i)

end AlgebraicGeometry.Scheme
