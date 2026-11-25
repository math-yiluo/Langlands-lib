/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparison
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomAdjunction
import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! # Tensor-Hom duality for perfect complexes

Source: Stacks Project, duality.tex, Tag 0A9T; cohomology.tex, Tags 08DQ,
0FPC and 0GM7 (blueprint: lem-pc-perfect-tensor-hom-duality).
-/

@[expose] public section

universe u₁ w₁

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- Perfect complexes have a dual, evaluation and coevaluation satisfying the two
triangle identities, and the resulting tensor adjunctions. The full subcategory
D_QCoh has exactly the ambient Hom sets. Both left tensor adjunctions express the
specified Hom equivalences, naturally in both arguments. Their canonical forms are
Mathlib's `tensorLeftHomEquiv` for the respective exact pairings. The monoidal structure
on `schemeDerivedCategory X`, and on that of every `T`, is the global instance
`schemeDerivedTensorMonoidal` (def-pc-scheme-derived-tensor-structure).
Source: Stacks, Tags 0A9T, 08DQ, 0FPC, 0GM7 and 09UA
(blueprint: lem-pc-perfect-tensor-hom-duality).
Proof:
1. Define the dual globally as RHom(K,O_X). The perfect-RHom comparison
   (lem-pc-perfect-rhom-tensor-comparison) puts it in D_QCoh and supplies global
   evaluation and coevaluation satisfying the zig-zag identities (08DQ, 0FPC).
2. Apply lem-pc-dualizable-tensor-hom-equivalences to this exact pairing and its
   symmetric opposite. The two tensor adjunctions give the displayed natural Hom
   equivalences for every pair of quasi-coherent complexes.
3. On an open cover, represent K by strictly perfect complexes. The termwise
   pullback computes derived pullback (lemma-coherent-base-change-invertible-sheaves--2), and
   preserves finite free modules and their direct summands. Thus Lg*K is perfect.
   Both pulled objects have quasi-coherent cohomology
   (lem-pc-derived-pullback-tensor-qcoh). The global perfect-RHom comparison on the
   source identifies Lg*(Kdual) with RHom(Lg*K,O), transporting its exact pairing.
   Only isomorphism classes, not morphisms, are checked locally.
4. Apply the same exact-pairing Hom equivalences on the source of g, for arbitrary
   quasi-coherent A and B there. -/
theorem perfect_tensor_hom_duality
    (X : Scheme.{u₁})
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w₁}
        (SheafOfModules.{u₁} ((moduleRings X.toRingedSpace).over U))]
    (K : schemeDerivedQCohCategory X) (hK : Scheme.IsPerfect X K.obj) :
    ∃ Kdual : schemeDerivedQCohCategory X,
      Nonempty (ExactPairing K.obj Kdual.obj) ∧
      Nonempty (ExactPairing Kdual.obj K.obj) ∧
      Nonempty (tensorLeft K.obj ⊣ tensorLeft Kdual.obj) ∧
      Nonempty (tensorLeft Kdual.obj ⊣ tensorLeft K.obj) ∧
      (∀ A : schemeDerivedQCohCategory X,
        schemeDerivedQCohProperty X (K.obj ⊗ A.obj) ∧
        schemeDerivedQCohProperty X (Kdual.obj ⊗ A.obj)) ∧
      ∀ (T : Scheme.{u₁}) (g : T ⟶ X)
        [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings T.toRingedSpace))]
        [∀ U : T.Opens,
          HasDerivedCategory.{w₁}
            (SheafOfModules.{u₁} ((moduleRings T.toRingedSpace).over U))],
        Scheme.IsPerfect T ((derivedPullback g).obj K.obj) ∧
        schemeDerivedQCohProperty T ((derivedPullback g).obj K.obj) ∧
        schemeDerivedQCohProperty T ((derivedPullback g).obj Kdual.obj) ∧
        Nonempty (ExactPairing
          ((derivedPullback g).obj K.obj) ((derivedPullback g).obj Kdual.obj)) ∧
        Nonempty (ExactPairing
          ((derivedPullback g).obj Kdual.obj) ((derivedPullback g).obj K.obj)) ∧
        Nonempty (tensorLeft ((derivedPullback g).obj K.obj) ⊣
          tensorLeft ((derivedPullback g).obj Kdual.obj)) ∧
        Nonempty (tensorLeft ((derivedPullback g).obj Kdual.obj) ⊣
          tensorLeft ((derivedPullback g).obj K.obj)) ∧
        ∀ A : schemeDerivedQCohCategory T,
          schemeDerivedQCohProperty T (((derivedPullback g).obj K.obj) ⊗ A.obj) ∧
          schemeDerivedQCohProperty T (((derivedPullback g).obj Kdual.obj) ⊗ A.obj) := by
  classical
  obtain ⟨adj, s, adj', hadj, hs, he, hadj'⟩ := scheme_derivedInternalHom_adjunction X
  obtain ⟨Kdual, hdual, ev, hev, hperfect, comparison, hcomparison, hCM, hCK,
    bidual, hbidual, hbidualIso, η, hη, hηuniq, ⟨p, hp⟩, hbc⟩ :=
    perfect_rhom_tensor_comparison X K K hK adj hadj adj' hadj'
  let : ExactPairing K.obj Kdual.obj := p
  obtain ⟨Ddual, hDdual, evD, hevD, hDperfect, comparisonD, hcomparisonD, hDM, hDD,
    bidualD, hbidualD, hbidualDIso, ηD, hηD, hηDuniq, ⟨pD, hpD⟩, hbcD⟩ :=
    perfect_rhom_tensor_comparison X Kdual Kdual hperfect adj hadj adj' hadj'
  let : IsIso bidual := hbidualIso
  let : ExactPairing Kdual.obj Ddual.obj := pD
  let : ExactPairing Kdual.obj K.obj :=
    exactPairingCongrRight (asIso bidual ≪≫ eqToIso hDdual.symm)
  refine ⟨Kdual, ⟨p⟩, ⟨inferInstance⟩, ⟨tensorLeftAdjunction Kdual.obj K.obj⟩,
    ⟨tensorLeftAdjunction K.obj Kdual.obj⟩, ?_, ?_⟩
  · intro A
    exact ⟨canonical_derivedTensor_preserve_QCoh X K.obj A.obj K.property A.property,
      canonical_derivedTensor_preserve_QCoh X Kdual.obj A.obj Kdual.property A.property⟩
  · intro T g _ _
    obtain ⟨m, hm⟩ := exists_derivedPullbackMonoidalModel g
    let := m.toMonoidal
    let := ExactPairing.map (derivedPullback g) K.obj Kdual.obj
    let := ExactPairing.map (derivedPullback g) Kdual.obj K.obj
    have hKq := (derivedPullback_tensor_preserve_QCoh g).1 K.obj K.property
    have hDq := (derivedPullback_tensor_preserve_QCoh g).1 Kdual.obj Kdual.property
    refine ⟨derivedPullback_preserve_perfect g K.obj hK, hKq, hDq,
      ⟨inferInstance⟩, ⟨inferInstance⟩,
      ⟨tensorLeftAdjunction ((derivedPullback g).obj Kdual.obj)
        ((derivedPullback g).obj K.obj)⟩,
      ⟨tensorLeftAdjunction ((derivedPullback g).obj K.obj)
        ((derivedPullback g).obj Kdual.obj)⟩, ?_⟩
    intro A
    exact ⟨canonical_derivedTensor_preserve_QCoh T _ A.obj hKq A.property,
      canonical_derivedTensor_preserve_QCoh T _ A.obj hDq A.property⟩

end AlgebraicGeometry
