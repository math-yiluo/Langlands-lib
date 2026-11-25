/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerFiniteChernUniqueness
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteComparisonSurjective

/-! # Finite comparison tools for a local completed Chern class

Source: diagonal tower coefficient changes proof (1), reduction of the section class.
(blueprint: lem-diagonal-uniformizer-local-chern-transport).
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

/-- The completed normalized arrow has a finite comparison factor.
Source: diagonal tower coefficient changes proof (1), reduction of the section class.
(blueprint: lem-diagonal-uniformizer-local-chern-transport).

The target of the finite arrow is a degree-zero sheaf shifted by two, hence
bounded below. The etale/pro-etale comparison is bijective on morphisms into
this target. Apply its surjectivity to LocalComposite and reverse the resulting
equality. The normalization hypothesis is needed only for identification of the
factor, not for existence. -/
theorem localChern_transport_exists
    (s : UniformizerChernNormalizationData l Y)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)
    (hz : s.LocalNormalized l Y
      (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) s.tq.chernX
        (SpTowerClasses.hyperplanePic Y)) z) :
    ∃ k : LocalFiniteArrow l Y s,
      LocalComposite l Y s z = FiniteComparison l Y s k := by
  let _ := hz
  unfold LocalFiniteArrow FiniteComparison LocalFiniteArrow.toHom
  exact finite_comparison_surjective
    (ULift.{u + 1} (completedResidue l s.E s.π s.n))
    (l ^ (s.n + 1)) s.hA (ProjectiveLine Y) (LocalComposite l Y s z)

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
