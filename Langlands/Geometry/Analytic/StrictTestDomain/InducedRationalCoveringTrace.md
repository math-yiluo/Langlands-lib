# Finite-covering trace on actual induced rational spectra

This internal construction specializes the actual finite-fiber trace to
the original induced maps between balanced rational spectra. It retains
the full group action and every original smooth coefficient object and
intertwiner.

The geometric inputs are a complete ultrametric normed field
`K : Type u`, a presented strict affinoid algebra `P` over `K`, a
topological group `G : Type v`, and an actual
`RationalSpectralAction G P`. The ring `R : Type r` is any commutative
ring, and smooth coefficient carriers have universe `w`. The four
universes are independent. For `X : ρ.OpenSubgroupTransport`, the existing
space `X.InducedSpectrum` is the balanced quotient of `G` and the actual
Banach spectrum of the rational quotient algebra, in universe `max u v`.
Its original jointly continuous full-group action is reused.

For an original transport arrow `f : X ⟶ Y`, the hypotheses are exactly
`IsCoveringMap f.inducedMap` and a family of `Finite` instances for the
literal fibers of that same constructed map. These are genuine predicates
of the existing geometry; no covering or finiteness claim for every
transport arrow is made.

`Hom.compactSupportTrace` is a morphism from the existing full compact
function representation on `X` to the one on `Y`. Its evaluation at `y` is

```text
sum over x with f.inducedMap x = y of s(x).
```

The coefficient module has no topology, the empty sum is zero, and the
normalization involves no division by a degree. The full compact-support
carrier and the original diagonal action are unchanged. Compact support
and equivariance follow from the generic trace construction; no properness
or stable-neighborhood premise is added.

`compactSupportTrace_naturality` proves commutation with every original
smooth coefficient intertwiner. `compactSupportTraceNatTrans` packages
these maps between the entire original `CompactSections.coefficientFunctor`s:
their domain is `SmoothRep.{r, v, w} R G` and their codomain is
`SmoothRep.{r, v, max u v w} R G`. Its component is definitionally the trace
just constructed.

`finite_inducedMap_id_fiber` and `isCoveringMap_inducedMap_id` use the
existing pointwise identity formula for `inducedMap`, then the actual
one-point identity fiber and one-sheeted covering chart.
`compactSupportTrace_id` compares the trace with the original identity
morphism. `finite_inducedMap_comp_fiber` uses the original induced-map
composition formula and the actual composite-fiber equivalence to prove
finiteness of the composite fibers.

`compactSupportTrace_comp` proves that trace on `f ≫ g` is trace on `f`
followed by trace on `g`. It evaluates on each actual point, identifies the
original composite map with `g.inducedMap ∘ f.inducedMap`, and applies the
iterated-sum identity. Its signature retains finite-fiber instances for
the two maps and composite, and explicitly assumes that all three original
maps are covering maps. The finite-fiber proof is available separately;
closure of the covering predicate under transport composition is not
asserted.

The provenance is internal: specialize the proved finite-sum,
compact-support, and equivariance constructions to the already constructed
rational spectrum map and its proved identity, composition, and action
formulas. No source theorem from Harris or Berkovich is claimed. This is
ordinary-open degree-zero trace groundwork. Higher etale trace, sheaf
comparison, Godement trace maps, pull-push Hecke correspondence operators,
uniformization, arithmetic coefficient realization, and Harris
compatibility remain separate obligations.
