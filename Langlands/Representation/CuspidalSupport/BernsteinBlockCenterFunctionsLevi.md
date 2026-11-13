# Renard VI.4.4 on the Levi of an actual Bernstein cuspidal datum

Worker 98. Unconditional helper module for the proof of Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`,
SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`),
VI.10.4, Theorem (printed pp.211–212 / PDF pp.217–218). That proof works on
the Levi `M` of a cuspidal datum `(M, ρ)`, with an irreducible constituent
`ρ₀` of `ρ|_{⁰M}`, the module `Π_D = ind_{⁰M}^{M} ρ₀` and its centre `ℨ_D`. It
uses the description of `ℨ_D` given by VI.4.4. This module supplies these
three facts for the actual standard cuspidal data of a standard family:

- (a) VI.4.4, last sentence, at `M = M_a`, as a closed proposition with its
  proof;
- (b) the existence of `ρ₀` (VI.3.2(ii));
- (c) a surjection `Π_D → ρ ⊗ ω` for every unramified character `ω`.

Nothing here is conditional, and no published statement is changed.

## Setting

`F, G, T, i, ν` and a `BernsteinStandardFamily i ν` are as in the published
statement `BernsteinBlockCenterFunctionsStatement` (module
`BernsteinCenterFunctionsStatements`). `a` is a `BernsteinCuspidalDatum` with
carriers in `Type (max uF uV)`. `M = bernsteinLeviScheme i ν a.roots` is its
rational Levi, and `ρ = a.representation` is its irreducible cuspidal smooth
representation of `M(F)`. `⁰M` is `rationalCommonNormKernel M`. `X = X(M)` is
`unramifiedCharacters (fun χ => (rationalNormCharacters M χ).toMul)`, and
`ρ ⊗ ω` is `rationalUnramifiedTwist M ω ρ`.

## (a) `BernsteinLeviCenterVarietyStatement`

The closed proposition is quantified exactly like
`BernsteinBlockCenterFunctionsStatement`. It has the same binders and the same
inline `haveI`/`letI` instances for `G` and for `M`: affineness from the closed
immersion `Standard.leviHom`, local finite type through its structure map, and
the topology `rationalPointTopology F M.X`. So it can be applied directly in
that statement's context.

For every irreducible smooth `ρ₀` of `⁰M`, at carriers in `Type (max uF uV)`,
and every injective `⁰M`-map `j : ρ₀ → ρ|_{⁰M}`, let

- `Π_D = rationalNormKernelSummandInduction M ρ₀`, the published compact
  induction `ind_{⁰M}^{M} ρ₀`;
- `Stab = {s ∈ X | ρ ⊗ s ≅ ρ}`.

Then there is an injective `ℂ`-algebra homomorphism
`Ψ : Subalgebra.center ℂ (End Π_D) →ₐ[ℂ] (X → ℂ)` with the following
properties:

- its range is the set of `Stab`-invariant elements of the published algebra
  `unramifiedRegularFunctions` of polynomial functions on `X`, which is
  `ℂ[Irr(M)[ρ]]` since `Irr(M)[ρ] ≅ X/Stab`;
- every central `z` acts on every map `φ : Π_D → ρ ⊗ ω`, by precomposition, as
  multiplication by `Ψ z ω`: `(z : End Π_D) ≫ φ = Ψ z ω • φ`.

This is Renard VI.4.4, Proposition, last sentence ("`Z` est isomorphe à
l'algèbre des fonctions de la variété `Irr(G)[π]`", printed p.159 / PDF p.165),
at the group `M_a`. It is the published
`RationalSummandCenterVarietyStatement`, specialised to `G := M_a` and
`π := ρ`, with two changes. The twists are of `ρ` itself, not of the universe
lift `rationalInertiaBaseLift M ρ`, because here the carriers of `ρ` already lie
in `Type (max uF uV)`. The instances of `M` are those of the VI.10.4 statement.
The provenance is therefore *derived*.

### Proof (`bernsteinLeviCenterVarietyStatement_holds`)

The proof applies the published theorem `rationalSummandCenterVariety` at
universe `max uF uV`. Its hypotheses are supplied as follows.

1. `M` is connected reductive. `bernsteinStandardRepresentativesGeometric`
   shows that the standard Levi is a rational Levi subgroup, and
   `isConnectedReductive` turns this into the required fact.
2. `j' = standardLeviTorusFactor` is `T` as a subgroup of `M`. It is a maximal
   split torus of `M`, by `isMaximalSplitTorus_standardLeviTorusFactor`. `ν`
   is generic for it, by the second component of `standardLeviStandardFamilies`.
3. The relative root system of `M` comes from `relativeRootSystem`. The
   semidirect decompositions of its standard parabolics come from
   `isSemidirectDecomposition_of_standardCocharacterStatement` with the
   published `standardCocharacter`. Closedness of their unipotent radicals
   comes from `isClosed_unipotent`.
4. Cuspidality of `ρ` for `M`'s own standard parabolics comes from
   `rationalLeviCuspidalityTransport` (direction `.mpr`) applied to
   `a.cuspidal`. That gives cuspidality of the pullback of the literal Levi
   representation `bernsteinLiteralLeviRep` along
   `leviRationalPointHomeomorph`. It is moved to `ρ` itself with
   `SmoothRep.pullbackSymmIso` and `IsCuspidal.of_iso`.

The theorem then gives `Ψ`, its injectivity and its range verbatim, because
`rationalNormKernelSummandInduction` is an abbreviation for the compact
induction used there. For the action clause, the published conclusion is
about maps into `ρ_lift ⊗ ω`, where `ρ_lift = rationalInertiaBaseLift M ρ`. Let
`e : ρ ⊗ ω ≅ ρ_lift ⊗ ω` be the twist functor (`SmoothRep.twistFunctor`)
applied to the iso `ρ ≅ ρ_lift` built by `SmoothRep.mkIso` from
`SmoothRep.universeLiftEquiv`. The published clause for `φ ≫ e.hom` reads
`(z ≫ φ) ≫ e.hom = (Ψ z ω • φ) ≫ e.hom` after reassociating and
`Linear.smul_comp`. Since `e.hom` is an isomorphism, it can be cancelled
(`cancel_mono`).

The proof never names `a.roots` through a `let`. With such a `let`,
unification between terms written with the alias and terms of the goal
unfolded the Levi group scheme and did not terminate in reasonable time.

## (b) `bernsteinCuspidalDatum_exists_normKernelConstituent`

There are an irreducible smooth `ρ₀` of `⁰M` (carriers in `Type (max uF uV)`)
and an injective `⁰M`-map `j : ρ₀ → ρ|_{⁰M}`. This is the existence of an
irreducible constituent of `ρ|_{⁰M}`, Renard VI.3.2(ii) (printed pp.143–144 /
PDF pp.149–150).

*Proof.* `M` is connected reductive (as in (a), step 1). The published
`rationalNormKernelConstituent_of_finiteRestriction`, fed with the published
proof `rationalNormKernelFiniteRestriction`, gives an irreducible
subrepresentation `W` of `ρ|_{⁰M}`. Take `ρ₀ = SmoothRep.subrepresentation _ W`
and `j` its inclusion `SmoothRep.subtype`, which is injective
(`SmoothRep.subtype_injective`).

## (c) `bernsteinCuspidalDatum_exists_surjective_twist`

For a nontrivial `ρ₀` of `⁰M`, an injective `⁰M`-map `j : ρ₀ → ρ|_{⁰M}` and every
`ω ∈ X`, there is a surjective `M`-map
`φ : rationalNormKernelSummandInduction M ρ₀ → ρ ⊗ ω`.

*Proof.* `ω` is trivial on `⁰M` (`ω.2`), and `⁰M` and `ker ω` are open. So
`NormalHecke.twistRestrictEquiv` identifies `⁰M`-maps `ρ₀ → ρ|_{⁰M}` with
`⁰M`-maps `ρ₀ → (ρ ⊗ ω)|_{⁰M}`. Frobenius reciprocity
`NormalHecke.inducedHomEquiv` then identifies those with `M`-maps
`ind_{⁰M}^{M} ρ₀ → ρ ⊗ ω`. Let `φ` be the image of `j`. If `φ` were zero, then its
Frobenius transform, which is `j` read through `twistRestrictEquiv`, would
vanish on a nonzero vector `v` of `ρ₀`, contradicting injectivity of `j`. Now `ρ ⊗ ω` is irreducible
(`isIrreducible_rationalUnramifiedTwist_iff`), so the nonzero map `φ` is
surjective (`Representation.IsIrreducible.surjective_or_eq_zero`).

## Technical notes

The section theorems (b) and (c) use local instances: `T2Space F`, and for
the Levis `M_I` affineness and local finite type (through `Standard.leviHom`),
the topology `rationalPointTopology`, local compactness and the
nonarchimedean group structure (through the closed embedding
`leviRationalPointHomeomorph` into `G(F)`), and the Hausdorff property
(`rationalPoint_t2Space`). They are `local`, so they are not exported. The module sets `maxHeartbeats 1200000` and
`backward.isDefEq.respectTransparency.types false`, like the published
statement module.
