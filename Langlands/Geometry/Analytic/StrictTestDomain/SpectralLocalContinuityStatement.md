# Local spectral continuity targets for rational quotient actions

Author: Worker 36.

`RationalSpectralLocalContinuityStatement.{u,v}` is a proposition definition
with three conclusions. This file states the target; it supplies no proof.
The coefficient field `K` is an arbitrary complete ultrametric normed field,
`P` is an actual presented strict affinoid `K`-algebra, and `G` is a
topological group in an independent universe. An input
`ρ : RationalSpectralAction G P` is a group homomorphism into the actual
bounded algebra automorphisms of `P`, continuous for the published
`rationalSpectralTopology P`.

Fix actual unit-radius rational data `d : RationalData K P`. Write
`H = ρ.locusOpenSubgroup d` and `σ = ρ.sectionAction d`. The subgroup `H`
has its inherited subgroup topology. It is the constructed open subgroup
of `G` preserving the subset `d.locus` setwise under the existing spectrum
action. No chosen presentation or individual point must be fixed. The
homomorphism `σ : H →* Aut d.algebra` is the already constructed action on
the fixed rational quotient algebra. Its operators use forward algebra
transport followed by restriction to the original rational locus.

The first conclusion says that, for every quotient section `b`, every
`g₀ : H`, and every real `ε > 0`, eventually as `g` tends to `g₀` in `H`,

```text
SpectralBound (σ(g)(b) - σ(g₀)(b)) ε.
```

Here `SpectralBound a ε` means `x(a) ≤ ε` for every
`x : BanachSpectrum d.algebra`. Thus one neighborhood of `g₀` controls all
the spectrum points simultaneously. The tolerance is strictly positive;
the bound itself uses a weak inequality. This conclusion neither chooses a
spectral maximum nor presupposes a nonempty spectrum.

The second conclusion says that, for each fixed `b : d.algebra`, the
real-valued map

```text
H × BanachSpectrum d.algebra → ℝ,  (g,x) ↦ x(σ(g)(b))
```

is jointly continuous. The domain has the product topology, and the spectrum
has its published topology of pointwise convergence of bounded
multiplicative seminorms. This is a continuity assertion about section
evaluations, with both the group parameter and the spectrum point varying.

The third conclusion says that

```text
H × BanachSpectrum d.algebra → BanachSpectrum d.algebra,
(g,x) ↦ σ(g) • x
```

is jointly continuous for the existing action of bounded automorphisms on
spectrum points. This action uses inverse pullback:
`(σ(g) • x)(b) = x(σ(g).inv(b))`. It is the action on the spectrum of the
actual fixed rational quotient, rather than an assumed analytic atlas.

The three conclusions are an internal consequence target for the
published restricted rational spectral topology. The source motivation is
Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic spaces*
(1995–1996), section 1.1, printed/PDF pp. 1–2. Those pages use finite
compact-domain/function tests with positive tolerances and uniform spectral
displacement inequalities to define the automorphism group topology, and
define continuous actions by continuous homomorphisms into that group.
The present target concerns only the Library's fixed-field, unit-radius
rational tests. The manuscript does not state this three-part restricted
target verbatim.

The intended derivation uses the open positive-radius single-test subgroups
to control displacement at the identity. Translation in `H` and pullback
of spectrum points along bounded algebra maps give the bound at every
`g₀`. The seminorm inequality
`|x(a) - x(b)| ≤ x(a-b)` and continuity of fixed-section evaluation then
give joint evaluation continuity. Applying this to inverse group parameters
and using the pointwise spectrum topology gives the last conclusion.
These are proof obligations, not additional hypotheses of the statement.

The underlying strict affinoid quotients, bounded morphisms and rational
quotients are the published constructions following Berkovich's
*Non-archimedean analytic spaces*, Trieste lectures (2009), section 2.1
and Definition 2.1.2 on p. 7, Definition 2.1.11 on p. 8, and Definition
2.2.1 and Exercise 2.2.2(ii) on p. 9.

The statement imposes no nontrivial valuation, reducedness, nonzero
quotient, nonempty rational locus or common bound on operator norms.
It asserts no quotient-norm continuity of `σ` or its section orbits, and
does not identify quotient and spectral norms. It does not identify the
restricted automorphism topology with the full analytic topology. Analytic
atlases, structure sheaves, etale sites and equivariant sites remain separate
constructions.

The registered Equish source folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
receipt SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The Trieste source is `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
