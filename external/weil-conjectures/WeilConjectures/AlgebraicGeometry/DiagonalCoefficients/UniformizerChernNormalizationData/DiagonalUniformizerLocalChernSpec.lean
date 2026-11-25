/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernFinite
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalLocalChernIntegralProjection
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalLocalChernNormalizedBoundary
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceIntegralKummerComparison
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleComparison

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

/-- The finite factor has the normalized finite Kummer specification.

Source: diagonal tower coefficient changes proof (1), finite Kummer normalization.
(blueprint: lem-diagonal-uniformizer-local-chern-finite-spec).

Proof: use hz to express the scalar restriction of z as the limit of the
strict-system Chern arrow. Compute that arrow and its reduction on a common
K-flat resolution of the integral line-bundle extension. Tensor first with the
integral coefficient ring and then with its uniformizer quotient. Since hA
kills the quotient by l^(n+1), this reduction factors through level n of the
strict system. Naturality of the connecting morphism identifies its value with
the Kummer boundary of the hyperplane bundle. The coefficient-unit endpoint
sends one to one, by completedP.unit_normalization, toIntegral.units,
scalar.units, and eP.unit_normalization. The root endpoint is the finite root
projection followed by the scalar root map, by completedP.line_normalization,
the scalar line endpoints, and lineP's normalization. Thus the same boundary,
with its positive sign, is the ordinary finite Kummer class after site
comparison and forgetting scalars. Substitute hk and use the integral
constant-generator adjunction to recover the coefficient-linear class of k.
This is precisely ordinaryFiniteP1ChernSpec, hence its canonical wrapper.
The argument uses neither a trace nor a degree equation. It also covers n=0,
the zero coefficient ring, and the empty scheme. -/
-- The normalization hypothesis hz retains the repair of the former missing hypothesis.
theorem localChern_transport_finite_spec
    {s : UniformizerChernNormalizationData l Y}
    {z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧}
    {k : LocalFiniteArrow l Y s}
    (hz : s.LocalNormalized l Y
      (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) s.tq.chernX
        (SpTowerClasses.hyperplanePic Y)) z)
    (hk : LocalComposite l Y s z = FiniteComparison l Y s k) :
    LocalFiniteChernSpecCanonical l Y s k := by
  unfold LocalFiniteChernSpecCanonical LocalFiniteChernSpec
  apply (Etale.ordinaryFiniteP1ChernSpec_iff _ _ _ _ _ _).mpr
  apply (comparison_mapExt_bijective AddCommGrpCat.{u + 1} (ProjectiveLine Y)
    _ _ 2).injective
  apply (DiagonalTrace.finiteExtEndpointEquiv
    (SpTowerClasses.integerComparison (ProjectiveLine Y))
    ((forgetComparisonIso (ULift.{u + 1} (completedResidue l s.E s.π s.n))
      (ProjectiveLine Y)).app (Scheme.finiteEtaleTateLine (ProjectiveLine Y)
        (l ^ (s.n + 1)) (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.hA))).injective
  exact (localChern_transport_integral_projection l Y hk).trans
    ((localChern_normalized_integral_boundary l Y hz).trans
      (DiagonalTrace.diagonalTrace_integralKummer_comparison l
        (ProjectiveLine Y) (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.n s.hA
        s.tq.chernX.kummer
        (affineTraceProjectiveInvertible (l ^ (s.n + 1)) Y s.hYpow)
        (SpTowerClasses.hyperplanePic Y)))

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
