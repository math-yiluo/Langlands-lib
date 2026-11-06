# Coherent geometric finite Artin systems

Author: Worker 1771.

This pair defines two propositions in namespace `Langlands.LocalClassField`:
the relation `GeometricFiniteArtinSystemRelation` and the assertion
`GeometricFiniteArtinSystemExistenceUniqueness`. It supplies statement targets
for later arithmetic proofs. Defining or compiling these propositions does
not prove them.

## Fields, topology and the candidate family

The universe parameter `u` is arbitrary. The existence assertion quantifies over
every natural number `p` with `[Fact p.Prime]`, every `F : PadicField.{u} p`,
and every supplied `T : F.TopologicalData`. Here `F` is an actual field with a
specified finite extension structure over Mathlib's `Padic p`. The datum `T`
records the original local-field topology, a valuation extending the p-adic
valuation, and the compatible module-topology and local-field certificates.
The `letI := T.topology` in both definitions installs precisely that topology
on `F.Carrier`. Its units carry Mathlib's units topology. The existing
`Langlands.PadicField.canonicalTopologicalData` construction in
`Langlands.LocalField.Canonical` supplies such data for every algebraic
`PadicField`; the assertion still quantifies over every supplied datum.

The relation is on the existing `FiniteArtinFamily F.Carrier`. Its members
are families

```lean
∀ L : FiniteAbelianExtension F.Carrier,
  F.Carrierˣ →ₜ* L.galoisGroup
```

The index consists of actual finite Galois intermediate fields of
`AlgebraicClosure F.Carrier` whose actual Galois groups are commutative.
`LocalFiniteAbelianExtension F` is the same index. The target
`L.galoisGroup` is the actual automorphism group `Gal(L.field/F.Carrier)`,
with its finite discrete Krull topology. Each component is already a
continuous multiplicative homomorphism by its type. No new data package,
field, norm, topology or Galois group is introduced.

## The exact geometric relation

`GeometricFiniteArtinSystemRelation F T a` is precisely the conjunction of
`FiniteArtinSystemRelation a` and the residue congruence below.

The existing system relation requires, for every indexed extension `L`,
both

```lean
(a L).toMonoidHom.ker = normSubgroup F.Carrier L.field
Function.Surjective (a L)
```

The subgroup is the actual range of `Units.map (Algebra.norm F.Carrier)`.
The same relation also requires, for every pair `L`, `M` and every actual
inclusion `h : L.field ≤ M.field`, the equality of continuous homomorphisms

```lean
(L.restrictionOfLE M h).comp (a M) = a L
```

The transition is the already constructed restriction of automorphisms along
that inclusion. Thus the conditions apply simultaneously to the same family.

The added normalization quantifies over every
`L : LocalFiniteAbelianExtension F`, every supplied
`S : (L.asPadicField (p := p)).TopologicalData`, every
`b : F.Carrierˣ` with `T.ord (b : F.Carrier) = 1`, and every
`x : L.field` with `S.discreteValuation x ≤ 1`. Its conclusion is exactly

```lean
S.discreteValuation ((a L b).symm x - x ^ T.residueCardinality) < 1
```

`L.asPadicField` packages the same intermediate field as a finite extension of
`Padic p`. The quantifier over `S` retains every supplied local-field
realization of that field. The normalized multiplicative discrete valuation
is at most one on its integer ring and less than one on its maximal ideal.
Consequently the inequality says that the inverse of `a L b` acts on residues
as the `q`-power map, with `q = T.residueCardinality`, the cardinality of the
actual base residue field. The order-one condition makes `b` a base
uniformizer. Since `b` is a unit of the field, it is nonzero; the convention
`T.ord 0 = 0` causes no ambiguity. The integral element `x` may be zero.

The inverse `.symm` is the inverse of the finite field automorphism
`a L b`. Arithmetic Frobenius acts on residues by the `q`-power map, so
`a L b` itself induces geometric Frobenius. For a ramified extension the
formula specifies its residue action; it does not choose an automorphism
lifting Frobenius in the ramified group. The formula is the same as in
`GeometricProfiniteReciprocityRelation`, with its `finiteFamilyOfHom r`
replaced by the present family `a`.

## Existence and uniqueness of the whole family

`GeometricFiniteArtinSystemExistenceUniqueness.{u}` is the unconditional
proposition

```lean
∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
  (T : F.TopologicalData),
  letI := T.topology
  ∃! a : FiniteArtinFamily F.Carrier,
    GeometricFiniteArtinSystemRelation F T a
```

Existence and uniqueness are conclusions. In particular, no reciprocity map,
norm-residue certificate, class formation, coherence certificate or
bijectivity assertion is supplied as a premise. Unique existence compares
families satisfying the entire relation, including normalization and every
restriction. Equality is equality of the dependent families of continuous
homomorphisms. There is no uniqueness assertion for an isolated finite map
with a norm kernel and residue normalization alone.

The existential quantifier chooses one family before imposing all component,
restriction and normalization conditions. This is the simultaneous coherent
conclusion missing from the standalone `FiniteAbelianReciprocity` and
`FiniteAbelianRestriction` assertions, which separately quantify finite maps
or pairs for individual towers. The conditional constructions in `FiniteArtin`
also take their candidate maps and certificates as inputs.

## Original sources and the derived formulation

The source is Jean-Pierre Serre, *Local Fields*, English translation by Marvin
Jay Greenberg, Graduate Texts in Mathematics 67, Springer (1979), registered
as `serre-1979-local-fields`. Its retained file is
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 1771 read the following original passages and checked the fingerprint.

| Original passage | Correspondence with this pair |
| --- | --- |
| XI.3, printed pp.169–171 / PDF pp.175–177 | Finite reciprocity maps and upper-field compatibility; diagram (4) and the following inverse-limit discussion give coherent finite values for a fixed base. |
| XIII.4, Proposition 8 and its corollary, printed p.196 / PDF p.201, continuing on printed p.197 / PDF p.202 | The finite norm-residue isomorphism, hence surjectivity and the exact norm kernel; for abelian extensions its target is the actual Galois group. |
| XIII.4, Proposition 12, printed p.197 / PDF p.202 | Restriction in the upper field, as required by `FiniteArtinRestrictionRelation`. |
| XIII.4, Proposition 13 and its corollary, printed pp.197–198 / PDF pp.202–203 | Arithmetic Frobenius normalization on unramified extensions and the unit/inertia description. Restriction to the maximal unramified subextension yields the corresponding residue action for a ramified abelian extension. |
| XI.5, printed pp.173–175 / PDF pp.179–181; XIV.6, Theorem 1 and Corollary 1, printed pp.218–219 / PDF pp.223–224 | Norm groups are open in the original local-field topology. Together with their finite index, this makes the finite reciprocity maps continuous into the discrete finite Galois groups. |

Serre uses arithmetic reciprocity. Invert its values consistently to obtain
the geometric convention here. The finite target groups are abelian, so this
inversion preserves the homomorphism law, kernels, surjectivity, continuity
and upper-field restriction compatibility.

The packaging as one closure-indexed continuous family and its `∃!` predicate
are derived interface formulations, not verbatim statements of Serre.
Existence packages the same arithmetic maps and their restriction law before
inverting them. The uniqueness characterization uses the finite norm kernels,
coherence with all intermediate fields, and residue normalization, together
with unramified extensions of arbitrarily divisible degrees. One compares
the two induced isomorphisms on each norm quotient, enlarges to a compositum
with a sufficiently large unramified extension, and uses normalization on
that cyclic unramified quotient to force the comparison to be the identity.
This is the finite-family part of the derived uniqueness discussion in the
existing `ProfiniteReciprocityStatement.md`. That mathematical argument is
not implemented or claimed as a Lean proof in this pair.

## Dependencies and scope

The direct imports are the published
`Langlands.ClassFieldTheory.Local.FiniteArtin` and
`Langlands.LocalField.Normalization.Definitions`. Their existing Galois,
norm and local-field constructions are reused unchanged. The environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

This pair states neither a proof of the coherent arithmetic family nor the
final reconstruction of the actual profinite Galois quotient. Those remain
separate proof obligations after independent statement acceptance and
publication. No published Lean/Markdown pair is changed.

## Development validation

The pair compiled in the pinned Lean service with no errors or warnings.
Inspection of both declarations reported `statement_returns_prop: true`,
the sole universe parameter `u`, and only `propext`, `Classical.choice`
and `Quot.sound`. These checks establish elaboration and allowed assumptions;
they do not prove either proposition or supply independent semantic acceptance.
