# Actual complex affine coordinates of the Harris group

This module is an internal specialization of the published affine restriction
and scalar-extension comparisons to the actual rational Harris similitude
group. Its maps come from pullback projections and the canonical affine test
isomorphisms. No comparison or geometric existence assertion is added as an
assumption.

Retain `D : CentralSimpleUnitaryData E K A n`, with the actual totally real
number field E, totally complex quadratic extension K/E, and central simple
K-algebra A with its second-kind involution. All the specified E-, K- and
rational algebra structures and scalar towers on A are retained. Write σ
for the rational involution and b for `D.rationalBasis`.

Let T be a commutative complex algebra, in universe zero, with compatible
real and rational structures. The standing hypotheses give the towers
ℝ → ℂ → T, ℚ → ℝ → T and ℚ → ℂ → T. The constructions involving only the
real projection do not require the rational structure on T; Lean omits
unused hypotheses. Write X = Spec_ℂ T, G = `D.rationalGroupScheme`, and
G_ℝ, G_ℝ,ℂ for the actual real and iterated complex pullbacks.

## Projection to the original affine models

For x : X → G_ℝ,ℂ, `complexAffineRealPoint T x` is the morphism
Spec_ℝ T → G_ℝ obtained by the complex pullback point adjunction and the
inverse of `restrictedAffineTestIso ℝ ℂ T`. The theorem
`complexAffineRealPoint_left` identifies its underlying scheme map with
x followed by the first complex pullback projection.

`complexAffineRationalPoint T x` applies `originalAffinePoint b σ` to that
real point. It is an actual morphism Spec_ℚ T → G.
`complexAffineRationalPoint_left` identifies its underlying scheme map
with x followed by both first pullback projections, in that order.

`complexDirectGroupSchemeIso_hom_fst` proves that the existing canonical
isomorphism from G_ℝ,ℂ to the direct complex pullback preserves this
projection to G. Its proof first establishes the projection identity for
an arbitrary group scheme and a composite of base maps identified with
another base map. Equality elimination and the existing
`baseChangeCompIso_inv_fst` prove that generic identity. Applying it to
the rational, real and complex bases gives the claimed Harris identity.

Consequently, `complexAffineRationalPoint_direct` proves that
`complexAffineRationalPoint T x` equals `originalAffinePoint b σ` of x
after `D.complexDirectGroupSchemeIso`. The proof compares the underlying
scheme maps and uses the projection identity and associativity. Thus the
two routes give the same actual rational affine point.

## Comparison with the real algebra model

Let H be the similitude scheme of ℝ ⊗_ℚ A with involution σ_ℝ, and let
e = `D.realGroupSchemeIso : G_ℝ ≅ H`.
`complexAffineRealPoint_comparison` proves that projecting x after the
complex pullback of e gives exactly

    complexAffineRealPoint(T,x) ≫ e.

Here the left route uses `originalAffinePoint` for the real algebra
model. The proof is the target naturality of the pullback point adjunction,
precomposed with the same affine test identification, followed by
associativity.

`complexAffineSimilitudes T x` takes x through the complex pullback of e
and the published normalized affine point equivalence for H. Its output
is a similitude of T ⊗_ℝ (ℝ ⊗_ℚ A), with its scalar multiplier retained.
`complexAffineSimilitudes_tower` proves

    complexAffineSimilitudes(T,x)
      = baseChangeTowerSimilitudes(ℝ,T,σ)
          (rationalAffinePointsEquiv(T)(complexAffineRationalPoint(T,x))).

The proof identifies normalized coordinates with the real affine point,
uses `complexAffineRealPoint_comparison`, and applies
`scalarExtensionIso_originalAffinePoints` for ℚ → ℝ → T.
The tensor expansion sends t ⊗ a to t ⊗ (1 ⊗ a); it preserves the
multiplier through the existing similitude equivalence.

These results hold for every such T and affine point x. They do not infer
equality of schemes or scheme morphisms from field-valued points.
The subsequent comparison with matrices in global sections, the explicit
Harris cocharacter weights in embedding-labelled affine coordinates,
conjugacy and reflex-field alignment, smoothness and reductivity, and
the PEL geometry, levels and coefficient descent remain separate work.
