# Invariant rational spectra over the global continuous spectrum

Author: Worker 36.

This is an internal derived construction from the published actual local and
global spectrum actions of a `RationalSpectralAction G P`. Here `K` is a
complete ultrametric normed field, `P` is a presented strict affinoid algebra,
and `G` is a topological group in an independent universe. For each open
subgroup `U`, the construction retains the structural maps of the existing
invariant rational spectrum diagram and makes it a functor to the overcategory
of the restricted global continuous action.

The definition `restrictedGlobalSpectrum ρ U` restricts `globalSpectrum ρ`
along the continuous subgroup inclusion `U → G`. Its underlying space is the
original `BanachSpectrum P`, with the original inverse-pullback operators.
The theorem `restrictedGlobalSpectrum_apply` records their evaluation:

```text
(g • x)(a) = x((ρ(g : G)).inv(a)).
```

The underlying continuous homomorphism is the actual subgroup inclusion with
the subtype topology. The construction adds no continuity assumption on norm
orbits of algebra elements.

For an object `d` of the published full subcategory
`InvariantRationalDomain ρ U`, its actual rational locus is preserved by every
element of `U`. Its quotient algebra, topology and action are those of the
published `invariantSpectrum ρ U d`. The definition
`invariantSpectrumToBase ρ U d` uses the continuous spectrum pullback of
`d.obj.baseMap`, the actual bounded structural map from `P` to the rational
quotient algebra. It is a morphism of continuous `U`-actions: the published
`spectrumMap_smul` supplies its equivariance, applied to the same ambient
group element in the open locus stabilizer. The local and global actions
both use inverse pullback, so this is precisely the required equivariance
equation.

The theorem `invariantSpectrumToBase_apply` identifies the underlying function
with `d.obj.spectrumMap`. The theorem `invariantSpectrumToBase_apply_eval`
records the formula

```text
structuralMap(x)(a) = x(d.obj.baseMap(a)).
```

For an inclusion `h : d ⟶ e`, the existing rational spectrum diagram sends
`h` to pullback by the bounded restriction
`h.hom.restriction : e.obj.algebra → d.obj.algebra`. The theorem
`invariantSpectrumToBase_naturality` proves that its composite with the
structural map of `e` equals the structural map of `d`. After extensionality
of continuous-action, action and topological morphisms, this is exactly the
published equality `h.hom.spectrumMap_restriction`, whose algebraic content is
the structural-map equation for bounded restriction.

The definition `invariantSpectrumToBaseNatTrans` packages these maps as a
natural transformation from `invariantSpectrumFunctor ρ U` to the constant
diagram with value `restrictedGlobalSpectrum ρ U`. Mathlib's `Over.lift`
then constructs `invariantSpectrumOverFunctor ρ U`. Each object consists of
the actual quotient spectrum action together with its equivariant structural
map; each arrow is the existing equivariant rational spectrum map satisfying
the proved triangle equation. No structural maps or commuting triangles are
assumed as extra input.

The lemmas `invariantSpectrumOverFunctor_obj_hom` and
`invariantSpectrumOverFunctor_map_left` identify the resulting structural
maps and arrows exactly. The equality
`invariantSpectrumOverFunctor_forget` shows that forgetting the maps to the
base recovers the published continuous-action diagram. The equality
`invariantSpectrumOverFunctor_forget_topological` shows that subsequently
forgetting actions recovers the full invariant-subcategory inclusion
followed by `RationalData.toTopologicalSpace K P`. Both equalities are
reflexive: the construction preserves the original spectra and bounded
restriction maps definitionally.

The geometric motivation is Berkovich's unfinished *Etale equivariant
sheaves on p-adic analytic spaces* (1995–1996), section 1.1, printed/PDF
pp.1–2, which defines continuous analytic group actions and equivariant
morphisms. The present overcategory diagram is an internal consequence of
the Library's restricted fixed-field, unit-radius rational spectral action
and the proved joint continuity on actual local and global spectra. It is
not asserted to be a numbered theorem of that manuscript or to identify the
restricted rational spectral topology with the full analytic automorphism
topology defined there.

The rational affinoid context is Berkovich's *Non-archimedean analytic
spaces*, Trieste lectures (2009), Definition 2.2.1 and Exercise 2.2.2(ii),
printed/PDF p.9. They give the representing-property formulation of
affinoid domains and the rational quotient construction. The existing
Library implements the bounded structural and restriction maps used here;
the present natural transformation and categorical lift are derived from
their published compatibility equations.

The construction permits trivial scalar valuations, zero or nonreduced
quotients and empty spectra. It supplies no new arbitrary-radius domains,
analytic gluing, structure sheaves, atlases, etale or quasi-etale sites, or
Harris tower specialization.

The registered manuscript source is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The Trieste source is `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
