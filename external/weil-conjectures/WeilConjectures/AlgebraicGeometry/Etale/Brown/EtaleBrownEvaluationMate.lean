/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemBrownConstruction
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison

/-! # Canonical Brown comparison normalization

Source: Zheng, Construction 4.1, (5.16.2), and Lemma 5.22.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SheafOfModules
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry
attribute [instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O t c}
  (B : StrictEtaleBrownConstruction O t c S)

private theorem open_evaluation_mate (n : ℕ) :
    ((mateEquiv S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n)).symm
      (.mk _ _ _ _ (S.openDerived.inverseEvaluation n).hom)) =
    (S.openDerivedEvaluation n).inv := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro P
  have h := derivedMate_comparison
    (S.val.openAdjunction.mapHomologicalComplex (.up ℤ))
    ((S.val.levelOpenAdjunction n).mapHomologicalComplex (.up ℤ))
    S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n)
    S.val.openFactors.hom (S.val.levelOpenFactors n).hom
    S.openDerived.system.inverseFactors (S.openDerived.level n).inverseFactors
    (S.PX.evaluationFactors n) (S.PZ.evaluationFactors n)
    S.property.2.2.1 (S.property.2.2.2.1 n)
    (.mk _ _ _ _
      ((S.openImage.inverseEvaluation n).hom.mapHomologicalComplex (.up ℤ)))
    (.mk _ _ _ _ (S.openDerived.inverseEvaluation n).hom)
    (S.openDerived.inverseEvaluation_rep n)
    ((S.val.openEvaluation n).inv.mapHomologicalComplex (.up ℤ))
    (by
      intro K
      ext1 i
      change (S.val.levelOpenAdjunction n).homEquiv _ _
        ((S.val.openEvaluation n).inv.app (K.X i)) = _
      have hh := unit_mateEquiv S.val.openAdjunction (S.val.levelOpenAdjunction n)
        (.mk _ _ _ _ (S.val.openEvaluation n).inv) (K.X i)
      change _ ≫ ((mateEquiv S.val.openAdjunction (S.val.levelOpenAdjunction n)
        (.mk _ _ _ _ (S.val.openEvaluation n).inv))).app _ = _ at hh
      rw [← S.property.2.1 n] at hh
      exact hh.symm) P
  let U := (S.PZ.evaluation n).map (S.val.openFactors.hom.app P) ≫
    (S.PZ.evaluationFactors n).hom.app
      ((S.val.openExtension.mapHomologicalComplex (.up ℤ)).obj P)
  apply (cancel_epi ((S.openDerivedEvaluation n).hom.app (DerivedCategory.Q.obj P))).1
  apply (cancel_mono U).1
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_app_assoc]
  change (S.openDerivedEvaluation n).hom.app (DerivedCategory.Q.obj P) ≫
    (((mateEquiv S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n)).symm
      (.mk _ _ _ _ (S.openDerived.inverseEvaluation n).hom)).app
        (DerivedCategory.Q.obj P) ≫ U) = U
  dsimp only [U]
  rw [h]
  have hr := S.property.2.2.2.2 n P
  rw [← Category.assoc] at hr
  erw [reassoc_of% hr]
  change _ ≫ _ ≫ DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex (S.val.openEvaluation n) (.up ℤ)).hom.app P) ≫
    DerivedCategory.Q.map
    ((NatIso.mapHomologicalComplex (S.val.openEvaluation n) (.up ℤ)).inv.app P) = _
  rw [← DerivedCategory.Q.map_comp, Iso.hom_inv_id_app]
  erw [DerivedCategory.Q.map_id, Category.comp_id]

private theorem proper_evaluation_mate (n : ℕ) :
    (mateEquiv (S.PZ.derivedAdj n) (S.PY.derivedAdj n)
      (.mk _ _ _ _ (B.properInsertionMate n).hom)) =
    (S.properDerived.directEvaluation n).inv := by
  rw [B.properInsertionMate_def]
  rw [iterated_mateEquiv_conjugateEquiv
    (S.properDerived.level n).adjunction S.properDerived.system.adjunction
    (S.PY.derivedAdj n) (S.PZ.derivedAdj n)]
  have hi : conjugateIsoEquiv
      ((S.PY.derivedAdj n).comp S.properDerived.system.adjunction)
      ((S.properDerived.level n).adjunction.comp (S.PZ.derivedAdj n))
      (B.properInsertion n).symm = S.properDerived.directEvaluation n := by
    apply Iso.ext
    exact B.properInsertion_conjugate n
  exact congrArg Iso.inv hi

/-- The insertion comparison and evaluation comparison are adjunction mates.
Source: Zheng, (5.16.2), Construction 5.15, printed pp. 34--35
(blueprint: lem-pur-etale-brown-evaluation-mate).

Proof: decompose the insertion into its open and proper factors using
`leftExtension_def`. For the open factor, transpose the normalized termwise
open-extension comparison through its derived adjunctions. The representative
transpose equations identify its mate with the recorded inverse-image evaluation;
`openInsertion_conjugate` identifies the conjugate insertion with the same map.
For the proper factor, use `properInsertionMate_def` and the iterated-mate identity.
`properInsertion_conjugate` identifies its double transpose with proper direct-image
evaluation. Inverse isomorphisms give the inverse evaluation comparison. Paste the
open and proper squares using the mate-pasting identity. Functor associators cancel,
and the defining composite is precisely `S.evaluation n`. This proves equality of
natural transformations on all derived inputs, without a boundedness restriction. -/
theorem etaleBrownEvaluationMate (n : ℕ) :
    (mateEquiv S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n)
      (.mk _ _ _ _ (S.openDerivedEvaluation n).inv)) =
        (S.openDerived.inverseEvaluation n).hom ∧
    (mateEquiv (S.PX.derivedAdj n) (S.PY.derivedAdj n)
      (.mk _ _ _ _ (B.leftExtension n).inv)) = (S.evaluation n).inv := by
  constructor
  · apply (mateEquiv S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n)).symm.injective
    rw [Equiv.symm_apply_apply]
    exact (open_evaluation_mate (S := S) n).symm
  · have ho : (mateEquiv (S.PX.derivedAdj n) (S.PZ.derivedAdj n)
        (.mk _ _ _ _ (B.openInsertion n).inv)) =
        (S.openDerivedEvaluation n).inv := by
      have hh := B.openInsertion_conjugate n
      rw [← iterated_mateEquiv_conjugateEquiv (S.PX.derivedAdj n)
        (S.PZ.derivedAdj n) (S.levelDerivedOpenAdjunction n) S.derivedOpenAdjunction] at hh
      have he := congrArg (fun z ↦
        ((mateEquiv S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n)).symm
          (.mk _ _ _ _ z))) hh
      simpa only [Equiv.symm_apply_apply] using he.trans (open_evaluation_mate n)
    let α := TwoSquare.mk _ _ _ _ (B.openInsertion n).inv
    let β := TwoSquare.mk _ _ _ _ (B.properInsertionMate n).hom
    have hh := 
      (mateEquiv_vcomp (S.PX.derivedAdj n) (S.PZ.derivedAdj n) (S.PY.derivedAdj n) α β)
    have he : (B.leftExtension n).inv = (α ≫ₕ β) := by
      rw [B.leftExtension_def]
      simp [TwoSquare.hComp, α, β]
    rw [he]
    change (mateEquiv (S.PX.derivedAdj n) (S.PY.derivedAdj n) (α ≫ₕ β)) = _
    rw [hh]
    apply NatTrans.ext
    funext K
    simp only [TwoSquare.vComp_app]
    change (S.properDerived.level n).direct.map
      ((mateEquiv (S.PX.derivedAdj n) (S.PZ.derivedAdj n) α).app K) ≫
      (mateEquiv (S.PZ.derivedAdj n) (S.PY.derivedAdj n) β).app
        (S.derivedOpen.obj K) = _
    rw [ho, proper_evaluation_mate B n]
    simp [StrictEtaleCompactSupport.evaluation]

end AlgebraicGeometry
