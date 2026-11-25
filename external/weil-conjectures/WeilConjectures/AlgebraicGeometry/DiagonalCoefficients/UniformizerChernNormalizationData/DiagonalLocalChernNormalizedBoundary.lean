/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernDefinitions
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalIntegralProjection
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalChernNormalizedBoundaryProjection
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalChernNormalizedBoundaryKummer

/-! # Finite boundary of a normalized completed Chern arrow -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
namespace UniformizerChernNormalizationData

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Functor.mapDerivedCategory HasDerivedCategory.standard
  Scheme.finiteEtaleTateLine

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]

/-- The integral finite projection of a normalized completed Chern arrow is the
positive Kummer composite. No scalar-extension functor or supplied finite factor occurs.

Source: blueprint latest, diagonal tower trace proof (1), finite levels of the section
class; geometric tower classes proof (2), finite Kummer normalization.
(blueprint: lem-diagonal-local-chern-normalized-boundary).

Proof: postcompose hz with the n-th projection of tq.LX. Naturality of that projection
moves firstChern outside the derived limit. Normalize the coefficient cone by
exactConeComparison_projection. For the shifted root cone use tq.LX.unitShift and its
normalization on the shifted single complex: this identifies the shifted projection
with the single of coefficientsX.lineProjection at n, including both exact shift
comparisons. Thus the projected equation is the evaluated strict-system Chern arrow,
preceded by the actual coefficient cone component, and followed by the actual root
cone component.

Forget to abelian sheaves. Restriction.underlying identifies strict-system restriction
followed by evaluation and forgetting with intrinsic finite evaluation and forgetting.
The coefficientsX.coefficient_projection equation identifies the source component with
the actual completed ring projection. Its composite with localCompletedGenerator is the
integer-cast map into the finite coefficient sheaf, since ring projections preserve
integer casts. The coefficient_one equation then identifies it with finiteQuotient.
The coefficientsX.line_projection equation identifies the target component with the
n-th root-limit projection. The line_tensor equation and lineEvaluation normalization
identify its comparison with finiteRootMap, followed by cartierProRootMap.

Apply tq.finiteX to the hyperplane Picard class and level n, unpacking its heterogeneous
endpoint equalities. The resulting equation identifies the preceding composite with
evaluation of the Yoneda composite of lineBundleClass and tq.chernX.kummer, followed
by the finite scalar root map. Exact evaluation preserves Yoneda composition. By the
definition of evaluatedIntegralKummerClass and Ext.homEquiv this is the asserted Ext
equality. No etale-site cancellation and no scalar-reduction normalization is used.
The exponent is n+1, hence positive even for n=0; zero rings, trivial Picard classes and
empty schemes require no exception. -/
theorem localChern_normalized_integral_boundary
    {s : UniformizerChernNormalizationData l Y}
    {z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧}
    (hz : s.LocalNormalized l Y
      (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) s.tq.chernX
        (SpTowerClasses.hyperplanePic Y)) z) :
    completedIntegralProjection l (ProjectiveLine Y)
      (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.n s.hA
      (affineTraceProjectiveInvertible (l ^ (s.n + 1)) Y s.hYpow) z =
    DiagonalTrace.evaluatedIntegralKummerClass l (ProjectiveLine Y)
      (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.n s.hA s.tq.chernX.kummer
      (affineTraceProjectiveInvertible (l ^ (s.n + 1)) Y s.hYpow)
      (SpTowerClasses.hyperplanePic Y) := by
  exact (DiagonalTrace.localChern_normalized_boundary_projection l (ProjectiveLine Y)
    s.tq.chernX s.tq.restrictionX s.tq.coefficientsX _ s.n s.hA
    (affineTraceProjectiveInvertible (l ^ (s.n + 1)) Y s.hYpow) s.tq.LX _ z
    (by simpa only [LocalNormalized] using hz)).trans
      (DiagonalTrace.localChern_normalized_boundary_kummer l (ProjectiveLine Y)
        s.tq.chernX s.tq.restrictionX s.tq.coefficientsX _ s.n s.hA
        (affineTraceProjectiveInvertible (l ^ (s.n + 1)) Y s.hYpow)
        s.tq.finiteX (SpTowerClasses.hyperplanePic Y))

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
