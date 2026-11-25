/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientSourcePullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison

/-! # Supported-source normalization of the scalar/pullback mate

Source: diagonal coefficient changes, paragraph (3), supported source normalization.
(blueprint: lem-diagonal-supported-pullback-scalar-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] derivedUpper derivedScalars singlePullback
  scalarPullbackComparison

/-- Supported coefficient endpoints commute with geometric inverse image under the
scalar mate. The coefficient change is arbitrary; no positive line or diagonal class
occurs in the equation, and no diagram or trace compatibility is assumed.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3), closed diagonal base change;
lem-diagonal-quotient-class-pullback, proof step 1 (supported-source part).
(blueprint: lem-diagonal-supported-pullback-scalar-normalization).

Proof: Transpose the displayed composites through the scalar adjunction at the primed
surface. Replace the scalar endpoint maps by their normalized degree-zero semilinear
maps and use the exact inverse-image single comparison. SourcePullback's supported
normalization replaces each geometric supported map by sourcePullbackMap, the ordinary
exchange followed by the coefficient-unit map. The definition of supportMap replaces
each scalar supported map by direct image of its unit semilinear map followed by the
restriction/direct-image comparison. These ordinary maps commute: transpose once more
through the diagonal adjunction, expand the ordinary exchange mate, and use naturality
of the coefficient unit together with the unit/counit triangle identities. Both orders
are the same coefficient map on the primed projective line, followed by the same
diagonal counit. Unit Endpoint and PullEndpoint normalization fixes the unit maps, so
there is no rescaling. Faithfulness of the module forgetful functor identifies the
ordinary module arrows. Apply the degree-zero functor and injectivity of the scalar
adjunction to recover the displayed equality. No flatness of a, or noetherian hypothesis,
is required: the supplied endpoints already assert the relevant isomorphisms. -/
theorem diagonalSupported_pullbackScalarNormalization
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (L₀ : ∀ X : Scheme.{u}, Modules R X) (L : ∀ X : Scheme.{u}, Modules T X)
    (m₀P : (upperStar Ab.{u + 1} (baseP g)).obj (L₀ (ProjectiveLine Y)).X ⟶
      (L₀ (ProjectiveLine Y')).X)
    (m₀W : (upperStar Ab.{u + 1} (baseW g)).obj (L₀ (diagonalSurface Y)).X ⟶
      (L₀ (diagonalSurface Y')).X)
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X)
    (s₀ : SourcePullback R g L₀ m₀P m₀W) (s : SourcePullback T g L mP mW)
    (c : Endpoint a (Mod.regular (condensedRingObj R (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj T (ProjectiveLine Y)))
      (coefficientMap a (ProjectiveLine Y)))
    (c' : Endpoint a (Mod.regular (condensedRingObj R (ProjectiveLine Y')))
      (Mod.regular (condensedRingObj T (ProjectiveLine Y')))
      (coefficientMap a (ProjectiveLine Y')))
    (e : Endpoint a (source R Y) (source T Y) (supportMap a Y c.semilinear.hom).hom)
    (e' : Endpoint a (source R Y') (source T Y') (supportMap a Y' c'.semilinear.hom).hom) :
    (scalarPullbackComparison a (baseW g)).app
        ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).obj (source R Y)) ≫
      (derivedUpper T (baseW g)).map e.iso.hom ≫
      (singlePullback T (baseW g) (source T Y)).hom ≫
      (DerivedCategory.singleFunctor (Modules T (diagonalSurface Y')) 0).map s.supported.hom =
    (derivedScalars a (diagonalSurface Y')).map
      ((singlePullback R (baseW g) (source R Y)).hom ≫
        (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
          s₀.supported.hom) ≫ e'.iso.hom := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
