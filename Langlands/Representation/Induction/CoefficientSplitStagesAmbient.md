# Native split stages with the original inducing quotient

This internally derived transport removes the intermediate subgroup from the
coefficient quotient in the native compact split-stages comparison. The
original inducing representation and its original normal-coinvariant action
remain visible. Coefficient, ambient group, section group and the two
inducing carriers have independent universes.

Write `r : G →* L`, `s : L →* G`, with `r(s(l)) = l`, and let
`H ≤ P ≤ G` with `ker r ≤ P`. Require that `s(l)` belongs to `H` for every
`l : P.comap s`. Put

```text
K  = P.comap s
HP = H.subgroupOf P
rP = splitStagesRetraction r s hrs P hker
sP = s.subgroupComap P
φ  = (Subgroup.subgroupOfEquivOfLe hHP).toMonoidHom
N  = r.ker.comap H.subtype
a  = splitStagesInducingSection s P H hsH
```

For the original representation `σ : Representation R H V`, the coefficient
quotient used by the inner integral is the full coinvariant quotient for the
restriction of `σ.comp φ` to `HP.comap rP.ker.subtype`.
The published `splitStagesCoefficientEquiv` identifies it with the actual
`Jacquet.Coinvariants σ N`: the two relation submodules correspond through
the literal intersection equivalence and retain the class of every vector.

`splitStagesAmbientCoefficientEquiv` bundles this linear equivalence as an
equivalence of representations of `K`. Its source is the implemented
`splitKernelCoefficientAction rP sP HP hsH (σ.comp φ)`. Its target is

```text
(σ.toCoinvariants N).comp a.
```

On a representative, both actions send `[v]` to `[σ(a(l))v]`.
The implemented equivariance proof uses quotient surjectivity and the
published `splitStagesCoefficientEquiv_section_mk`. Forward and inverse
representative formulas and naturality in every original inducing
intertwiner are proved. This part requires only a commutative coefficient
ring and the topological group structures used by the existing
split-kernel action.

For the compact comparison retain all hypotheses of
`Coefficient.splitStagesCompactEquiv`: `R` is a commutative complex algebra,
the inducing modules have compatible complex scalar towers, `G` is
Hausdorff and locally compact, `L` is a topological group, the splitting is
continuous, `P`, `H` and `ker r` are closed, and `σ` is smooth.
The compact-open subgroup neighborhood bases, regular two-sided kernel and
intersection Haar measures, measurable and Borel structures, locally finite
quotient measure and its actual `IsCompatible` proof are supplied exactly
as in that comparison. Local compactness of `P` is derived from closedness
inside the imported comparison.

Let `χ` be its exact positive subgroup-to-kernel Haar character, embedded in
`R` through `algebraMap ℂ R`. The same character is used on both sides of
the coefficient equivalence. Applying `twistEquiv` and then pointwise
`compactInducedEquiv` after the existing stages comparison constructs
`splitStagesAmbientCompactEquiv`:

```text
((compactInduced H σ).toCoinvariants r.ker).comp s
  ≃ compactInduced K (twist χ ((σ.toCoinvariants N).comp a)).
```

The evaluation formula on `[f]` at `l : L` is the existing relative quotient
integral of the original slice `q ↦ f(q*s(l))`, followed by
`splitStagesCoefficientEquiv`. The integrand formula verifies that every
integrand class becomes exactly `[f(n*s(l))]` in the original inducing
quotient. No change of quotient measure is asserted.

The target coefficient map is the quotient map induced by the original
`H`-intertwiner, restricted along `a` and twisted by the same `χ`.
Naturality of the imported stages comparison, followed pointwise by
naturality of the identity-on-classes coefficient equivalence, proves
naturality of the assembled comparison in independent inducing carrier
universes.

These constructions follow from the proved native stages comparison and
the published original-intersection quotient equivalence. They are internal
transport results, with no claim that a source states this formulation
verbatim. Actual rational orbit geometry, measure existence, normalization
or open-kernel properties of scalar twists, admissibility and the main
universal-family compact-open fixed-module finiteness theorem remain
separate obligations.
