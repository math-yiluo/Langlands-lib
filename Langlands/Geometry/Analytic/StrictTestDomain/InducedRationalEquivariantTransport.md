# Equivariant bounded transport on actual induced affinoid families

Author: Worker 36.

This module proves equivariance of the actual bounded quotient-algebra
pullbacks used by transport between the induced affinoid families. It
packages the bounded actions and transport maps into a functor, proves
commutativity for every admissible square of atlas charts, and constructs
natural comparisons with the existing balanced-quotient diagram of
jointly continuous spectrum actions.

## Sources and provenance

Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic
spaces*, retained Equish_1996 manuscript (1995–1996), Construction 1.1.2,
printed/PDF page 2, constructs induction from an open subgroup using
left-coset copies and the correction in `g*gi = gj*h`. The surrounding
text defines equivariant morphisms and continuous actions. This module
proves compatibility of the constructed bounded induction data with
transport; it is a derived construction, not a separately numbered
result in the manuscript. Registered folder source:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member *Berkovich--Etale equivariant sheaves on p-adic analytic spaces
(unfinished manuscript)--1996.pdf* has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The automorphism topology defined on printed/PDF pages 1–2 tests compact
analytic domains and functions and has broader scope than the joint
spectral continuity used here.

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
section 1.2, Definition 1.2.7 and the composition discussion, printed
page 18 / PDF page 15, requires compatible affinoid maps for every chart
pair with the required containment. This supplies the all-admissible-pair
convention used by the atlas-square result below. Registered source:
`berkovich-1993-etale-cohomology`, PDF SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The rendered original confirms printed page 18; text extraction misreads
the page header. General extended-atlas composition in that passage
requires further gluing beyond the disjoint atlases considered here.

Berkovich, *Non-archimedean analytic spaces* (Trieste lectures, 2009),
Definition 2.1.11, printed/PDF page 8, defines affinoid spaces as the
category dual to affinoid algebras with bounded homomorphisms. This fixes
the direction and order of the bounded pullbacks. Registered source:
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

These original passages were read and the cited pages visually checked
during development of this construction and its action dependency. No
source-specific errata note was present in the workspace, current Library
or shared project notes. The new proofs use the published rational
extension uniqueness, actual section action, strict/generalized bounded
comparison, induced atlas and bounded transport. They do not infer
algebra-map equality from equality on spectrum points.

## Hypotheses and actual objects

Work in
`Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction.OpenSubgroupTransport`.
Let `K : Type u` be a complete ultrametric normed field, `P` a presented
strict affinoid algebra, `G : Type v` a topological group, and
`ρ : RationalSpectralAction G P`. The universes `u` and `v` are
independent. For `X : ρ.OpenSubgroupTransport`, write `H_X` for its
actual open subgroup, `A_X = X.domain.obj.algebra`, and
`B_X = X.inducedChartAlgebra`.

The algebra `A_X` is the constructed strict rational closed-ideal Tate
quotient. The algebra `B_X` is its actual positive-polyradius quotient
presentation with all radii one. The published bounded equivalence is

`E_X = PresentedAffinoidAlgebra.strictEquiv K A_X : B_X ≃ A_X`.

The object `X.inducedAffinoidObject` has index type `G/H_X` and constant
algebra family `B_X`. Its spectrum is the topological sum of the actual
`BanachSpectrum B_X`. The published `X.inducedAffinoidHomeomorph`
identifies it with the actual balanced quotient `X.InducedSpectrum`.
Its atlas retains the nonempty component spectra. The imported
`X.inducedAffinoidAction` acts by bounded family maps with index
`c ↦ g • c` and actual pullback `X.affinoidActionPullback g c`.

An arrow `f : X ⟶ Y` retains a group label `l = f.label`, a conjugated
subgroup inclusion and the corresponding ambient rational-locus
containment. Its coset map `τ = f.cosetMap` sends `a H_X` to
`a*l⁻¹ H_Y`. Its constructed bounded pullback is

`φ_f(c) = f.cosetChartPullback c : A_Y → A_X`.

The published generalized-quotient pullback is

`F_f(c) = f.affinoidChartPullback c = E_X.symm ∘ φ_f(c) ∘ E_Y`.

These maps are constructed from the actual rational restriction and the
target representative correction; they are not extra input data.

## Equivariance on the strict rational algebras

Write `δ_X(g,c) = (g • c).out⁻¹ * (g * c.out) : H_X`, and
`α_X(g,c) = X.strictActionPullback g c : A_X → A_X`.
This is the inverse of the forward section action of `δ_X(g,c)`.
`strictActionPullback_comp_baseMap` proves the base triangle

`α_X(g,c) ∘ b_X = b_X ∘ (ρ(δ_X(g,c))).inv`,

where `b_X = X.domain.obj.baseMap` and `ρ(r) = ρ.toMonoidHom r`.
It specializes the published forward-section triangle to the inverse
subgroup element and simplifies the inverse automorphism.

`Hom.cosetMap_smul` proves `τ(g • c) = g • τ(c)` by quotient induction:
right multiplication by `l⁻¹` commutes with left multiplication by `g`.
The private `ambientInv_comp_equivariance` records the bounded-map order

`ρ(r).inv ∘ ρ(s).inv = ρ(s*r).inv`.

`Hom.cosetChartPullback_equivariant` proves the actual algebra equality

`α_X(g,c) ∘ φ_f(g • c) = φ_f(c) ∘ α_Y(g,τ(c))`.

The proof applies `Y.domain.obj.hom_ext`, the rational extension
uniqueness theorem. It precomposes both maps with `b_Y` and uses the
new action triangle and the published transport triangle

`φ_f(c) ∘ b_Y = b_X ∘ ρ(κ_f(c)).inv`,

where `κ_f(c) = (τ(c)).out⁻¹ * c.out`. Reassociation and the ambient
inverse composition law reduce the two sides to group products
`κ_f(g • c) * δ_X(g,c)` and `δ_Y(g,τ(c)) * κ_f(c)`.
Coset equivariance and cancellation identify both with

`(g • τ(c)).out⁻¹ * (g * c.out)`.

Thus rational extension uniqueness proves equality of bounded algebra
maps, including for algebras with empty spectrum.

## Generalized quotients and every admissible atlas square

`Hom.affinoidChartPullback_eq_ofStrictMap` identifies `F_f(c)`
definitionally with `PresentedAffinoidAlgebra.ofStrictMap K (φ_f(c))`.
`Hom.affinoidChartPullback_equivariant` applies the published
`ofStrictFunctor` composition laws to the strict equality. Writing
`β_X(g,c) = X.affinoidActionPullback g c`, its equation is

`β_X(g,c) ∘ F_f(g • c) = F_f(c) ∘ β_Y(g,τ(c))`.

`Hom.affinoidFamilyMap_equivariant` combines this equation and the
coset index equality with `AffinoidFamily.Hom.ext`, proving

`X.affinoidActionMap g ≫ f.affinoidFamilyMap =
  f.affinoidFamilyMap ≫ Y.affinoidActionMap g`.

`Hom.atlasTarget_action` gives the corresponding equality of actual
nonempty atlas indices:

`f.atlasTarget (X.actionAtlasTarget g c) =
  Y.actionAtlasTarget g (f.atlasTarget c)`.

For arbitrary charts `c,cg` of `X` and `d,dg` of `Y`, assume all four
containments: `g` maps chart `c` into `cg`, `f` maps `c` into `d`,
`f` maps `cg` into `dg`, and `g` maps `d` into `dg`.
`Hom.atlasPullback_equivariant` proves

```text
actionAtlasPullback_X(g,c,cg) ∘ atlasPullback_f(cg,dg)
  = atlasPullback_f(c,d) ∘ actionAtlasPullback_Y(g,d,dg).
```

These are the actual bounded maps between the named chart algebras;
the Lean statement includes the four containment proofs. The imported
uniqueness of a nonempty target component identifies `cg.val = g • c.val`
and `d.val = τ(c.val)`. The families are constant within each object,
so the bounded-map types need no transport. The equation reduces to the
already proved generalized-quotient equality. It therefore covers every
admissible square, beyond just the canonical selected targets.

## Equivariant functors and continuous spectrum comparison

`Hom.equivariantAffinoidMap` has underlying morphism
`f.affinoidFamilyMap` and commutativity proof
`f.affinoidFamilyMap_equivariant`. Its identity and composition laws
follow from the published bounded transport laws using `Action.Hom.ext`.
The selected definition `inducedEquivariantAffinoidFunctor` is

`ρ.OpenSubgroupTransport ⥤ Action (AffinoidFamily.{u,v} K) G`.

`inducedEquivariantAffinoidFunctor_forget` proves that composition
with `Action.forget` equals `inducedAffinoidTransportFunctor`.

Applying `AffinoidFamily.spectrumFunctor.mapAction G` gives a diagram
of actual topological spectrum actions. The natural isomorphism
`inducedEquivariantSpectrumComparison` compares it with
`inducedSpectrumFunctor` after forgetting the latter's continuity
property. Its components are the published
`X.inducedAffinoidSpectrumIso`. Naturality reduces, by extensionality
of action morphisms and continuous maps, to the symmetric form of the
published `f.affinoidFamilyMap_realization` equation

```text
f.inducedMap (X.inducedAffinoidHomeomorph p)
  = Y.inducedAffinoidHomeomorph (f.affinoidFamilyMap.spectrumMap p).
```

`inducedAffinoidContinuousSpectrumFunctor` uses the published
`X.inducedAffinoidContinuousSpectrum` as its object, retaining the
actual jointly continuous realized action. Its arrows are the spectrum
maps of `f.equivariantAffinoidMap`. The identity and composition proofs
reuse the laws of the composite spectrum-action functor.
`inducedContinuousSpectrumComparison` lifts the same component
isomorphisms and naturality proof to a natural isomorphism

`inducedAffinoidContinuousSpectrumFunctor ≅ inducedSpectrumFunctor`.

No new continuity hypothesis is assumed: joint continuity is the
published continuity of the actual realized bounded action, transported
through the constructed homeomorphism.

## Scope

Empty local spectra and infinite coset sets are allowed. The construction
proves bounded equivariance of the specific induced rational families,
all admissible squares of their disjoint atlases, and natural comparison
of their actual continuous spectrum diagrams. It retains the restricted
rational spectral topology of `RationalSpectralAction`; comparison with
the manuscript's full analytic automorphism topology remains open.
General overlapping atlas gluing and strong-morphism localization,
structure sheaves, etale and quasi-etale sites, equivariant analytic
sites, the full analytic induction universal property, compact and
distinguished domains in that generality, and Harris tower specialization
remain separate obligations of the larger branch.
