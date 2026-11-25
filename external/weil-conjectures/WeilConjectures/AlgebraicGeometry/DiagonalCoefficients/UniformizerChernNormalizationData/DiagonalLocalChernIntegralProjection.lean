/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernDefinitions
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalIntegralProjection
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleComparison

/-! # Integral comparison for a local uniformizer reduction -/

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

/-- The integral image of a scalar-reduced arrow is its actual finite root projection.
This concerns every completed arrow, without any Chern or Kummer hypothesis.

Source: blueprint latest, diagonal tower coefficient changes proof (1), integral and
uniformizer reduction; diagonal tower trace proof (1), the normalized section endpoints.
(blueprint: lem-diagonal-local-chern-integral-projection).

Proof: compose the completed-realization equivalence, the integral scalar adjunction,
the quotient scalar adjunction and the finite-realization equivalence. Transpose the
realized target endpoint through these actual adjunctions. The Endpoint.normalization
fields identify each scalar transpose with its specified ordinary semilinear insertion;
the equivalence triangle identifies the last transpose with the ordinary finite root
insertion. Exact-single composition coherence and the adjunction-induced shifts give
the corresponding formula in degree two.

Forget these ordinary insertions to abelian sheaves. CompletedRealization.line_normalization
identifies the first map with the bottom integral root map. The integral-root transition
formula identifies its integral extension with lineP's integralRoots. The quotient-line
normalization therefore makes the whole target map the n-th root projection followed by
lineP's finiteRoots.toLine. Its kernel-inclusion equation identifies the finiteRoots
isomorphism with cartierRootsIso, so this last map is cartierProRootMap.

Precompose the transposed equation with the integral generator of the completed unit.
The scalar-unit semilinear maps preserve one; completedP.unit_normalization identifies
the coefficient projection at every positive level. The map to the quotient factors
through level n because s.hA says l^(n+1) is zero there. The finite realization's
unit_normalization identifies the resulting generator with the ordinary finite integer
generator after site comparison. Naturality of the composite adjunction unit now
identifies the forgotten integral arrow with completedIntegralProjection. Substitute hk.
Exact comparison commutes with forgetting coefficients via forgetComparisonIso; Ext
functoriality moves the two endpoint comparisons outside. This is exactly the displayed
integral image of ordinaryFiniteClass. Only integral Ext is compared: no faithfulness
of derived coefficient forgetting is asserted. All maps preserve zero and one, so the
same calculation applies to z=0, n=0, the zero coefficient ring and the empty scheme. -/
theorem localChern_transport_integral_projection
    {s : UniformizerChernNormalizationData l Y}
    {z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧}
    {k : LocalFiniteArrow l Y s}
    (hk : LocalComposite l Y s z = FiniteComparison l Y s k) :
    Ext.mk₀CompMk₀ (SpTowerClasses.integerComparison (ProjectiveLine Y)).inv
      ((Etale.ordinaryFiniteClass
        (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)
        (Scheme.finiteEtaleTateLine (ProjectiveLine Y) (l ^ (s.n + 1))
          (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.hA) 2
          (LocalFiniteArrow.toHom l Y s k)).mapExactFunctor
        (comparisonUpperStar AddCommGrpCat.{u + 1} (ProjectiveLine Y)))
      ((forgetComparisonIso (ULift.{u + 1} (completedResidue l s.E s.π s.n))
        (ProjectiveLine Y)).hom.app (Scheme.finiteEtaleTateLine (ProjectiveLine Y)
          (l ^ (s.n + 1)) (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.hA)) =
    completedIntegralProjection l (ProjectiveLine Y)
      (ULift.{u + 1} (completedResidue l s.E s.π s.n)) s.n s.hA
      (affineTraceProjectiveInvertible (l ^ (s.n + 1)) Y s.hYpow) z := by
  sorry

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
