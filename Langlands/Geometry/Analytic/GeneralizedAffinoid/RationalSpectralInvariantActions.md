# Rational section diagrams for represented-domain spectral actions

Author: Worker 56.

Let `K : Type u` be a complete ultrametric normed field, let
`A : PresentedAffinoidAlgebra K` be an actual presented affinoid quotient,
and let `G : Type v` be a topological group. The field and group universes
are independent. Fix `rho : DomainSpectralAction G A` and an open subgroup
`H` of `G`. The continuity hypothesis is continuity of the given
automorphism homomorphism for the existing represented-domain spectral
topology. The conclusion constructs continuous actions on the original
rational quotient algebras and their section, spectrum and locus diagrams.

## Full invariant chart category

`spectralInvariantChartProperty rho H` requires
`H ≤ rho.locusOpenSubgroup d.toDomain` for a rational chart `d`. Thus every
element of `H` preserves the actual rational locus setwise.
`SpectralInvariantChart rho H` is the corresponding full subcategory of
`RationalChart K A`. Its arrows retain every original bounded rational
restriction with its equation over `A`; equivariance is subsequently proved,
without imposing a new condition on these arrows.

`spectralInvariantDomainFunctor` sends a chart to its actual represented
domain and a restriction to the same bounded domain restriction.
`fullyFaithfulSpectralInvariantDomain` supplies the fully faithful
structure, using the published fully faithful chart-to-domain functor.
Its preimage retains the supplied bounded map and structural equation.
The corresponding full and faithful instances are included.

## Continuous actions on the original section algebras

`spectralInvariantStabilizerInclusion` is the continuous homomorphism
from `H` to `rho.locusOpenSubgroup d.obj.toDomain`. It is the existing
invariant-domain inclusion, with both subgroup topologies induced from `G`.

`spectralInvariantSectionAction` first uses the proved
`d.obj.restrictSpectralAction rho` on the original rational quotient, then
precomposes with this continuous inclusion. The result is an object of the
existing `DomainSpectralActionCategory K H`. Continuity into the quotient
algebra's represented-domain spectral automorphism topology follows by
composition. The quotient algebra is unchanged, as exposed by
`spectralInvariantSectionAction_algebra`.

`spectralInvariantSectionAction_actionAut` identifies the full automorphism
homomorphism with `rho.invariantSectionAction H` on the corresponding
represented domain. The proof uses homomorphism extensionality, then
automorphism extensionality on the actual forward bounded algebra maps.
It therefore identifies the bounded inverses as well. It does not infer
equality of algebra maps from their spectrum operators.

`spectralInvariantSectionAction_baseMap` retains the original base-section
law for every `g : H` and `a : A`:

```text
localAction(g)(d.baseMap(a)) = d.baseMap(rho(g : G)(a)).
```

For every original restriction `f : d ⟶ e`,
`spectralInvariantSectionAction_restriction` gives the full bounded-map
equation

```text
f.restriction.comp localAction_e(g)
  = localAction_d(g).comp f.restriction.
```

Both laws are the published invariant-domain section laws after the
identification above. Section automorphisms and restrictions are constructed
by the imported represented-domain factorization properties, rather than
supplied as additional output-object inputs.

`spectralInvariantBoundedPresheaf` is the contravariant functor from this
full invariant rational category to `DomainSpectralActionCategory K H`.
It uses these section actions on objects and the original restrictions on
arrows. The restriction equation supplies each arrow's equivariance.
Identity and composition reduce to equality of their bounded maps.
`spectralInvariantBoundedPresheaf_forget` states definitional equality
with the original bounded section presheaf restricted to the full
invariant subcategory.

`spectralInvariantBaseAction` restricts the original ambient spectral
action along the continuous inclusion `H → G`.
`spectralInvariantBaseMapNat` bundles the original structural bounded
maps as a natural transformation from this constant base action to the
section presheaf. Equivariance follows from the base-section law and
naturality from each restriction's original equation over `A`.

## Continuous spectrum and locus diagrams

`spectralInvariantSpectrumFunctor` applies the existing
`DomainSpectralActionCategory.spectrumFunctor` in geometric direction to
the section presheaf. Its target is `ContAction TopCat H`: the imported
spectral continuity theorem supplies joint continuity on each actual
Banach spectrum. For `sigma_d = rho.invariantSectionAction H d`, the
object and arrow formulas are

```text
(g • x)(b) = x (sigma_d(g).inv(b)),
(spectrumMap(f)(x))(b) = x (f.restriction(b)).
```

These are `spectralInvariantSpectrumFunctor_obj_apply` and
`spectralInvariantSpectrumFunctor_map_apply`, with `d` interpreted through
the chart-to-domain functor in the first formula.
`spectralInvariantSpectrumFunctor_forget` identifies the underlying
topological diagram with the original rational chart spectrum functor.

The existing full-domain continuous spectrum diagram has the same points,
operators and bounded pullbacks on these objects.
`spectralInvariantSpectrumDomainIsoApp` constructs the component comparison
from the identity topological isomorphism. The equality of full section
actions proves its equivariance.
`spectralInvariantSpectrumDomainIso` assembles these components naturally.
Its forward and inverse point maps are identities, exposed by the two
application theorems; naturality evaluates the unchanged pullbacks.

`spectralInvariantLocusFunctor` is the existing continuous
invariant-domain locus diagram precomposed with
`spectralInvariantDomainFunctor`. The object formula
`spectralInvariantLocusFunctor_obj_coe` gives the original ambient action
on the underlying spectrum point. Forgetting actions recovers the
restricted original rational locus functor, by
`spectralInvariantLocusFunctor_forget`.

`spectralInvariantSpectrumLocusIso` uses each original rational
`locusHomeomorph` as its component. The section-action equality and
`rho.spectrumMap_smul` prove equivariance; the published naturality of the
rational homeomorphisms proves naturality for every original restriction.
Forgetting the actions recovers the original restricted
`spectrumLocusIso`, by `spectralInvariantSpectrumLocusIso_forget`.
`spectralInvariantSpectrumLocusIso_hom_eq` further identifies its forward
transformation with the identity spectrum comparison followed by the
published full-domain structural spectrum-to-locus transformation.
This equality is proved by evaluating the actual component maps.

`spectralInvariantSpectrumToBase` composes the identity spectrum
comparison with the existing continuous structural spectrum map to
`rho.restrictedGlobalSpectrum H`. Its value is exactly the original
`d.obj.spectrumMap`, by `spectralInvariantSpectrumToBase_apply`.
`spectralInvariantSpectrumLocusIso_over_base` states that the new
isomorphism followed by the original locus inclusion equals this
unchanged structural map. Its proof again evaluates the concrete maps.

## Provenance and sources

This is an internal construction by Worker 56 from
`RationalChartSpectralRestriction`, `DomainInvariantActions`,
`DomainSpectralActionCategory`, `DomainSpectralSpectrumFunctor`,
`DomainContinuousLocus` and `DomainContinuousOverBase`, together with the
actual rational chart category and spectrum/locus homeomorphisms.
It extends the common-subgroup section/spectrum/locus pattern of
`RationalNormInvariantActions` to an ambient represented-domain spectral
action. Continuous rational restriction supplies the missing local
algebra-action continuity; the original full-domain bounded action
equations supply equivariance. No implication between norm-orbit
continuity and represented-domain spectral continuity is asserted here.
The cited originals supply inherited geometric conventions and motivation,
rather than a numbered theorem stating this internal categorical construction.

Berkovich, *Non-archimedean analytic spaces* (Trieste lectures, 2009),
printed/PDF p.9 Definition 2.2.1 and Exercise 2.2.2(ii)-(iii), and p.10
Fact 2.2.3(i) and Definition 2.2.7, give represented affinoid domains,
positive-radius rational quotients, their spectrum/locus identification
and domain embeddings. The imported Lean rational charts use actual
quotient algebras and explicit unit-ideal generation, a sufficient
no-common-zero condition. This module does not prove its converse.
Registered source ID: `berkovich-2009-trieste-analytic-spaces`;
PDF SHA256:
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*,
unfinished 1996 manuscript, section 1.1, printed/PDF pp.1-2, motivates
continuous homomorphisms to automorphism groups whose neighborhoods test
setwise preservation of finitely many compact domains and non-strict
spectral displacement bounds on functions with positive tolerances.
The imported topology tests actual represented affinoid domains and
their quotient sections. The registered collection ID is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
collection content SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The member is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

## Scope

The underlying algebras use arbitrary positive polyradii, and trivial
valuations, nilpotents, zero quotients and empty spectra or loci remain
permitted. There is no quotient-norm continuity premise on section orbits,
spectral faithfulness assumption, or identification of quotient and spectral
norms. Every original bounded rational restriction is retained.

The outer local algebras here are rational chart algebras. This unit does
not prove continuous restriction to every represented domain or compare
the represented-domain topology with all compact analytic-domain tests
and the full analytic automorphism topology. General analytic atlases,
analytic algebra sheafness, etale/quasi-etale sites, compact/distinguished
lifting and the Harris tower remain separate construction obligations.
