/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernIdentification

/-! # Reduction of a local completed Chern class

Source: diagonal tower coefficient changes proof (1), reduction of the section class.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint RestrictionSquare.mate CompletedRealization.singleUnit
  CompletedRealization.shiftedLine FiniteRealization.derivedUnit
  HasDerivedCategory.standard Etale.projectiveLineTraceDatum
  Scheme.finiteEtaleTateLine

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]

namespace UniformizerChernNormalizationData

/-- Assemble the finite factorization and its positive Kummer identification.
Source: diagonal tower coefficient changes proof (1), reduction of the section class.
(blueprint: lem-diagonal-uniformizer-local-chern).

Proof: choose a finite comparison factor, identify its comparison image with the
canonical Chern image using the normalization, and compose the two equalities.
Both sides use the same protected endpoint expressions, so transitivity applies directly. -/
theorem localChern
    (s : UniformizerChernNormalizationData l Y)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)
    (hz : s.LocalNormalized l Y
      (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) s.tq.chernX
        (SpTowerClasses.hyperplanePic Y)) z) : s.LocalChernNormalized l Y z := by
  obtain ⟨k, hk⟩ := localChern_transport_exists l Y s z hz
  have hident := localChern_transport_identification (l := l) (Y := Y) s z hz hk
  unfold UniformizerChernNormalizationData.LocalChernNormalized
  unfold UniformizerChernNormalizationData.LocalComposite at hk
  unfold UniformizerChernNormalizationData.localFiniteChernImage at hident
  exact hk.trans hident

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
