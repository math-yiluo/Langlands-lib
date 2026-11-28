# Supercuspidal representations are projective and injective with fixed central character: proof

Module
`Langlands.Representation.Exponents.RepresentedSupercuspidalCentralProjectivityProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

`representedSupercuspidalCentralProjectivity` proves exactly
`RepresentedSupercuspidalCentralProjectivityStatement.{u, v}`
(module `Langlands.Representation.Exponents.RepresentedSupercuspidalCentralProjectivityStatement`),
for an arbitrary field universe `u` and an arbitrary, independent carrier universe
`v`. [Statement](RepresentedSupercuspidalCentralProjectivityStatement.md)

The statement is Renard, *Représentations des groupes réductifs p-adiques*
(French edition dated 9 July 2026, source
`renard-2026-representations-groupes-reductifs-padiques`), VI.3.6, the
Proposition after the Lemma, printed p.148 / PDF p.154: an irreducible
supercuspidal representation `τ` of `G(F)` with central character `χ` is
projective and injective in the full subcategory `M(G)_χ` of smooth
representations on which the centre of `G(F)` acts through `χ`.

## Scope

The theorem has no hypotheses. It covers every nonarchimedean local field
`k : Type u` (of either characteristic), every connected reductive group scheme
`G` over `Spec k` whose rational points, with their canonical topology, are
locally compact and a nonarchimedean group, every group homomorphism
`χ : Subgroup.center (rationalPoints G) →* ℂˣ`, and every smooth complex
representation `τ` with carrier in universe `v` that has central character `χ`,
is irreducible, and has vanishing Jacquet modules along every proper actual
rational parabolic triple. Both conjuncts, `Projective` and `Injective` in the
full subcategory of the property `fun A => A.HasCentralCharacter χ`, are proved.
No admissibility, finite-length, unitarity, smoothness-of-`χ` or other premise is
used. Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Proof

The Lean term is one application:

```
representedSupercuspidalCentralProjectivity_of_structure
  Langlands.GroupScheme.parabolicDynamic
  Langlands.GroupScheme.standardCocharacter
  Langlands.GroupScheme.relativeRootSystem
  Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence
  Langlands.Plancherel.RenardCartan.splitComponentLattice
```

- `representedSupercuspidalCentralProjectivity_of_structure`
  (module `Langlands.Representation.Exponents.RepresentedSupercuspidalCentralProjectivityReduction`)
  derives the target from five structural propositions:
  `ParabolicDynamicStatement`, `StandardCocharacterStatement`,
  `RelativeRootSystemStatement`, `JointSpecialCompactBasisExistenceStatement` and
  `Plancherel.RenardCartan.SplitComponentLatticeStatement`.
  [Reduction](RepresentedSupercuspidalCentralProjectivityReduction.md)
- The five premises are supplied by the Library theorems
  - `Langlands.GroupScheme.parabolicDynamic`
    (`Langlands.GroupScheme.Absolute.ParabolicDynamicProof`): a closed subgroup
    of a connected reductive group over a field is parabolic exactly when its
    range is the dynamic parabolic `P(λ)` of a cocharacter defined over the
    field (Milne, Theorem 25.1);
  - `Langlands.GroupScheme.standardCocharacter`
    (`Langlands.GroupScheme.Rational.StandardCocharacterProof`): standard
    cocharacters exist, and each standard subgroup functor agrees with the
    dynamic subgroup of every standard cocharacter;
  - `Langlands.GroupScheme.relativeRootSystem`
    (`Langlands.GroupScheme.Rational.RelativeRootSystemProof`): the relative
    roots of a maximal split torus form a root system, possibly nonreduced,
    on whose span the relative Weyl group acts faithfully as its Weyl group;
  - `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
    (`Langlands.BruhatTits.SpecialCompact.JointBasisProof`): Renard V.5.1–V.5.2
    at one special vertex, with a common geometric witness for the special
    compact subgroup, the Iwasawa and Cartan comparisons and the simultaneous
    standard basis;
  - `Langlands.Plancherel.RenardCartan.splitComponentLattice`
    (`Langlands.Representation.Plancherel.SplitComponentLatticeProof`): the
    valuation image of a split component of the centre has finite index in
    the valuation image of `G(k)`, and valuation is a bijection from the
    uniformizer subgroup `C0` onto the split-component valuation image; only
    the finite-index conjunct is used here.

## How the reduction proves the target

The reduction, whose proof this theorem instantiates, argues as Renard does
in VI.3.6, without passing through the block decomposition VI.3.5:

1. **Compact coefficients on `⁰G` (Renard VI.2.1, VI.3.2).**
   `compactRestriction_of_isSupercuspidal`
   (module `Langlands.Representation.Exponents.RepresentedCompactRestrictionSupercuspidal`)
   uses the first four premises to show that the restriction of `τ` to the common
   norm kernel `⁰G = Plancherel.rationalCommonNormKernel G` has compactly supported
   smooth-dual coefficients.
2. **Finite index of `⁰G Z(G)`.** `finiteIndex_rationalCommonNormKernel_sup_center`
   uses the split-component lattice statement and
   `Plancherel.finite_rationalCentralQuotient` to show that
   `⁰G ⊔ Subgroup.center (rationalPoints G)` has finite index in `G(k)`.
3. **Lifting and averaging.**
   `CentralCharacterProjectivity.projective_and_injective_of_compactRestriction`
   (module `Langlands.Representation.CompactCoefficient.CentralCharacterProjectivity`),
   applied to the open normal subgroup `⁰G`, gives both conjuncts. Epimorphisms
   and monomorphisms of `M(G)_χ` are surjective and injective intertwiners;
   `⁰G`-equivariant lifts and retractions exist because the restriction of `τ` to
   `⁰G` is compact; they commute with the centre because both sides have central
   character `χ`; averaging over the finite quotient `G(k) ⧸ (⁰G ⊔ Z(G(k)))` makes
   them `G(k)`-equivariant without changing the composites.

## Provenance

The statement and its source are described in its Markdown page. This proof is
an internal composition of the published Library theorems named above; the route
follows the proof of Renard VI.3.6 (restriction to `⁰G`, compactness there,
central character `χ`, averaging over the finite group `G / ⁰G Z(G)`).
