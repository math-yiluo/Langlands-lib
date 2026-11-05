# Integral parabolic models from descended cocharacters

This internal construction works in any universe `u`. It constructs an actual
smooth closed subgroup model from a supplied descended cocharacter. The final
assembly is conditional on the published proposition `ParabolicDynamicStatement`;
this file does not prove that proposition or the unconditional simultaneous
spreading existence statement.

Let `R` be a Noetherian domain, let `K` be its supplied fraction field, and let
`M : IntegralModel R K G` be an actual ambient model with smooth structural map.
Fix an actual closed subgroup homomorphism `p : P ⟶ G` and a cocharacter
`χ : Gm(Spec R) ⟶ M.group`. The explicit presentation hypothesis is

```text
range (p ≫ M.genericIso.inv)
  = Dynamic.parabolic (Dynamic.baseChangeCocharacter (Spec.algebraMap R K) χ).
```

This is equality of subgroup functors on every scheme over `Spec K`, not only
equality of rational points. In particular, the existence and descent of `χ` are
inputs here, not conclusions.

## Smoothness and base change

`Dynamic.Affine.smooth_parabolicScheme` extends the existing coordinate proof to
a Noetherian base ring. The affine-coordinate isomorphism of the ambient group
transfers smoothness to its coordinate algebra using
`DynamicSmooth.smooth_algSpec_iff`. The existing
`DynamicSmooth.smooth_parabolicScheme` then proves smoothness of the explicit
quotient group scheme. That theorem already applies over a Noetherian ring;
its use here introduces no field hypothesis.

`isRepresentedBy_parabolicHom_baseChange` combines the existing arbitrary
base-change theorem for represented subgroup functors with
`Dynamic.parabolic_baseChange`. Thus the changed inclusion represents precisely
the dynamic subgroup of the changed cocharacter on every test scheme.

## Actual model and inclusion

`IntegralModel.DynamicParabolic.genericIso` compares the generic fibre of
`Dynamic.Affine.parabolicScheme χ` with the supplied `P`. Closedness of
`p ≫ M.genericIso.inv` gives its monomorphism property, and the presentation
hypothesis identifies its range with the same functor represented by the
generic dynamic inclusion. The existing uniqueness isomorphism between
representatives therefore supplies an actual group-scheme isomorphism.
`genericIso_hom_comp` postcomposes its defining inclusion equality with
`M.genericIso.hom`. The inverse and forward ambient maps cancel, giving exactly
the generic square for the originally supplied `p`.

`model` uses this explicit dynamic group as its group scheme and that
isomorphism as its generic identification. Its structural morphism is affine
because the dynamic inclusion is closed and the ambient structural morphism
is affine. The smoothness proved above supplies flatness and local finite type.
`inclusion` uses the same dynamic inclusion, with the proved generic square;
`closedImmersion_inclusion` and `smooth_model` record these properties of the
actual constructed maps.

## Field fibres and conditional assembly

For every `k : Type u`, every field structure and every `Algebra R k`,
`fieldConnected` assumes connected reductivity of the actual ambient
`Spec.algebraMap R k` pullback. Its smooth, affine and connected properties,
combined with the base-changed representative, give connectedness of the
constructed subgroup fibre by the published
`DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic`.
This conclusion uses no parabolic-classification premise.

`fieldParabolic` separately takes the exact proposition
`ParabolicDynamicStatement.{u}` as an explicit hypothesis. The reverse
implication of that proposition applies to the actual changed dynamic
inclusion: its closedness is preserved by base change and its range is the
dynamic subgroup of the changed cocharacter. This is the geometric-Borel
`IsParabolicSubgroup` predicate required by the target.

`modelData` assembles the exact published `ReductiveParabolicSpreading.ModelData`
using this ambient model and this constructed subgroup model. Ambient
`IsReductive`, connected reductivity at every field algebra, the descended
cocharacter presentation and `ParabolicDynamicStatement` remain explicit
inputs. It constructs neither an initial ambient arithmetic model nor a finite
set of primes, and it discharges none of those remaining inputs.

The provenance is internal: every construction and implication above is
derived from the imported, published representability, smoothness,
connectedness, pullback and integral-model APIs. No additional literature
theorem is asserted here.
