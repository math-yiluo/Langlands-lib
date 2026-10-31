# The normalized determinant forces the full Harris–Taylor central trace

Author: Worker 57.

This internal construction proves that the normalized Harris–Taylor determinant condition implies the existing `CentralLieTraceCondition` for every scalar of the CM field. It removes the order-membership restriction from the earlier local coefficient consequence by using the constructed full order. The arithmetic normalization, actual Lie sheaf and all-chart quantifiers remain those of `HarrisTaylorCMLieDeterminant`.

The general lemma `Langlands.AbelianScheme.lieRationalSectionDeterminant_traceCoefficient` applies to an actual abelian scheme `B/S`, an actual map `p : S → Spec R` with rational algebra structure on the commutative ring `R`, and any unital ring action `α : O →+* End0 B`. The scheme and section rings have universe `u`, the action ring may have universe `v`, and the finite chart index has universe `u`. On any finite free Lie chart `e` over `U` and any smaller open `V : Over U`, it identifies

```text
traceCoefficient (lieRationalSectionDeterminant p B α e (1,a) V)
  = lieRationalSectionTrace p B α e a V.
```

Here `traceCoefficient` evaluates the actual binary polynomial at `(1,X)` and extracts coefficient one. The proof expresses the section determinant in `localSectionBasis e V`, uses unitality to identify its first endomorphism with the identity, and applies the existing arbitrary-commutative-ring identity for the coefficient of `det(1 + Xf)`. The existing basis formula for the actual section trace finishes the identification. No polynomial or trace is supplied as replacement data.

For number fields `L` and `F` with CM structures and `[Algebra L F]`, `lieTraceValueAddHom` bundles the already proved zero and addition laws for the arithmetic value. The resulting `lieTraceSection_zsmul` holds for every integer on every actual section ring of a scheme over `F`. Its proof composes this additive map with the actual section homomorphism.

The Harris specialization retains a totally real number field `E`, a totally complex quadratic extension `F/E` with `[IsCMField F]`, the central simple unitary datum `D` of degree `n`, compatible rational, `E` and `F` structures and scalar towers on `A`, an imaginary quadratic CM field `L`, `[Algebra L F]`, an embedding `τ₀`, and actual signature charts `C` for `harrisCMSection E (algebraMap L F) τ₀`. These arithmetic types and the scheme have universe zero. Let `p : S → Spec F`, let `B/S` be an actual abelian scheme, and let `i : A →ₐ[ℚ] End0 B`.

`harrisTaylorCMRationalLieDeterminantCondition_centralTrace` assumes the full normalized determinant condition and proves the central trace identity for every open, finite free Lie chart, smaller open and scalar `a : F`. The implemented argument is as follows.

1. Fullness of `harrisHodgePELIntegralOrder` supplies a nonzero integer `m` such that `m • algebraMap F A a` lies in this actual order. Denote the resulting order element by `c`; the ring map's integer-scaling law identifies its image with `algebraMap F A (m • a)`.
2. Apply the assumed determinant condition to the actual order family `(1,c)`. The existing normalized central coefficient theorem gives the prescribed arithmetic section for `m • a`. The general lemma above identifies its left side with the actual rational Lie trace of `c`.
3. The equality of the two elements in `A` identifies this trace with the actual central-action trace of `m • a`. Additivity of the actual trace and the prescribed section trace rewrites the equality as multiplication by `m` on both sides.
4. Since `m ≠ 0` and `F` has characteristic zero, `(m : F)` is a unit. Its image under the actual section homomorphism is a unit in `Γ(S,V.left)`, so cancellation proves the required equality for `a`.

This cancellation uses units, rather than an assumed domain or reducedness of the section ring. The result therefore retains arbitrary schemes over `F`, including nilpotents and empty opens.

`HarrisTaylorCMDeterminantDimensionCondition` is the conjunction of the normalized determinant condition and the existing actual geometric condition

```text
B.HasRelativeDimension ([E : ℚ] * n²).
```

The final `_iff` theorem identifies this predicate with the normalized determinant condition together with `HarrisTaylor.NumericalCondition`. That numerical condition consists of this same geometric dimension and the full central trace identity just proved. This equivalence does not derive geometric dimension from a trace equality or assert dimension invariance under rational isomorphism.

The provenance is internal: the new consequences use the constructed full order, the actual binary determinant and trace, and the previously proved normalized arithmetic coefficient comparison. The reused arithmetic value is the conjugate of `trace L F (n²*a)`, embedded into `F`, plus `n*a` minus `complexConj F (n*a)`. Its original source is Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties* (2001), III.1, Lemma III.1.2(3), printed p.90 / PDF p.98, registered source `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`. The normalization prerequisite derives this arithmetic value from the actual Kottwitz Hodge module using the explicit conjugated reflex map.

The module proves a consequence of the full normalized determinant and the stated equivalence of conjunctions. It supplies no converse from a central trace to the determinant, satisfying abelian scheme, full source Lie-plus equivalence, polarization, level structure, moduli representability or scheme level.
