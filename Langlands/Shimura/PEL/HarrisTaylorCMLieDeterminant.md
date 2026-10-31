# The normalized Harris–Taylor determinant through one CM structure map

Author: Worker 57.

This internal construction defines a same-CM-base rational Lie determinant condition using the explicitly conjugated scalar map from `HarrisHodgeTraceNormalization`. It preserves the earlier `HarrisCMLieDeterminant` condition and the unconjugated `harrisReflexToCM` with their original meanings. The new condition uses `harrisTaylorReflexToCM` throughout; no equivalence between these two arithmetic normalizations is asserted.

Fix the displayed totally real number field `E`, totally complex quadratic extension `F/E`, actual central simple unitary datum `D` of degree `n`, and the compatible rational, `E` and `F` algebra structures and scalar towers on `A`. Fix an imaginary quadratic CM field `L`, `[Algebra L F]`, its embedding `τ₀ : L →+* ℂ`, and actual Harris signature charts `C` for exactly `harrisCMSection E (algebraMap L F) τ₀`. As in the reflex determinant construction, all these types and schemes have universe zero. The field, signature and scalar-tower hypotheses are retained from the imported constructions; no arbitrary trace or determinant polynomial is supplied.

For any actual `S : Scheme.{0}` and `p : S → Spec F`, the reflex structure in this module is

```text
b = harrisTaylorReflexStructure C p
  = p ≫ Spec.map (harrisTaylorReflexToCM C),
harrisTaylorReflexToCM C
  = cmConjugation E F ∘ harrisReflexToCM C.
```

Under the distinguished complex embedding this new scalar map sends a reflex element with complex value `t` to the value `conj(t)`. This is the proved normalization that makes the actual central Hodge determinant agree with the Harris–Taylor arithmetic trace. It does not follow merely from uniqueness of rational scalar structures. The latter uniqueness will be used only for the rational scalars of one fixed Lie action.

For an actual abelian scheme `B/S` and rational algebra action `i : A →ₐ[ℚ] End0 B`, `HarrisTaylorCMRationalLieDeterminantConditionAt` equates two actual multivariate polynomials over the full structure-sheaf section ring on `V.left`: the polynomial of the rational Lie action with rational scalars supplied by `p`, and the existing reflex determinant first mapped through `harrisTaylorReflexToCM C` into `F` and then through `secHom p V.left`. Its arguments range over any finite family in the constructed Harris order, any finite free Lie chart on an open `U`, and any smaller open `V : Over U`. It imposes no reducedness, flatness or nonemptiness assumption on the section ring.

`harrisTaylorCMRationalLieDeterminantConditionAt_iff` proves equivalence with the existing rational determinant condition at the constructed normalized `b`. Its two steps have separate roles. `lieRationalSectionDeterminant_base_independent` identifies the rational scalar structures on the fixed actual action; `harrisReflexSectionDeterminant_harrisTaylor_CM` identifies the prescribed coefficients through the specific normalized map. Thus this theorem does not identify arbitrary arithmetic embeddings. The `_iff_coeff` theorem is equality of every coefficient in the actual section ring, by polynomial extensionality and the coefficient-map formula. The `_restrict` theorem transfers the existing restriction law through this local equivalence.

`HarrisTaylorCMRationalLieDeterminantCondition` requires this local equality for every finite family, actual finite chart and smaller open. Its `_iff` theorem follows pointwise. Its `_iso` theorem transfers the existing global invariance under an actual two-sided equivariant rational isomorphism. No geometric-dimension invariance is required or proved.

The final theorem, `harrisTaylorCMRationalLieDeterminantConditionAt_centralCoefficient`, additionally uses `[IsCMField F]`. Let `a : F` and let `c` be an element of the actual Harris order with `(c : A) = algebraMap F A a`. If the local condition holds for the order family `(1, c)`, then extracting the linear coefficient after evaluation at `(1, X)` from its actual rational Lie determinant gives exactly

```text
HarrisTaylor.lieTraceSection L p n a V.left.
```

The proof rewrites the family using the given equality in `A`, applies the local determinant equality, and uses `traceCoefficient_harrisTaylorCentralDeterminant_section`. That imported theorem derives the coefficient from the actual Kottwitz regular Hodge module and its left central action, then descends it through the actual reflex polynomial and the explicitly conjugated map. In the imaginary-quadratic case `L = F`, `n = 3`, the imported `traceCoefficient_harrisTaylorCentralDeterminant_rank_three` gives `-3*a` when `complexConj F a = -a`. This supplies the corrected sign rather than relying only on formal transport of a predicate.

The arithmetic formula reused here is the existing `HarrisTaylor.lieTraceValue`: the embedded conjugate of `trace L F (n²*a)`, plus `n*a`, minus `complexConj F (n*a)`. Its original source is Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties* (2001), III.1, Lemma III.1.2(3), printed p.90 / PDF p.98, registered source `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`. The present provenance is internal: this module derives the normalized predicate, its compatibility laws and its actual coefficient consequence from existing constructions and proved comparisons.

This module does not assert a satisfying abelian scheme, remove the full-order membership hypothesis in its last local theorem, prove equivalence with the source's full Lie-plus compatibility condition, replace the CM tower, or provide varying-base representability. It supplies the normalized determinant prerequisite for those later constructions.
