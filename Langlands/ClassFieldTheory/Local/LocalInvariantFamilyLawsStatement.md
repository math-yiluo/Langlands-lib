# Laws of the local invariant family

Author: Worker 272.

Lean module: `Langlands.ClassFieldTheory.Local.LocalInvariantFamilyLawsStatement`.

This module states five propositions about one concrete invariant family,
`localInvariantFamily hEx p` from the Library module `LocalInvariantFamily`.
Together they assert that this family satisfies the continuous absolute
properties, the three invariant clauses of the finite relative class-formation
predicate, and arithmetic normalization. The module defines propositions only.
It proves none of them.

## The family

For a proof `hEx : UnramifiedH2Exhaustion.{u}` and a prime `p`,
`localInvariantFamily hEx p : InvariantFamily.{u,u} p` has these two fields:

- the absolute invariant of a p-adic field `F` is
  `localAbsoluteInvariant hEx F`. This is the Library's descended unramified
  invariant `AbsoluteInvariantAssembly.descendedHom`: a continuous absolute
  `H²` class comes from a finite unramified stage, and the value is the
  unramified (arithmetic Frobenius) invariant of that stage class;
- the relative invariant of a finite Galois extension `L/F` is
  `embeddedRelativeInvariant`. It transports a class of `H²(L/F)` to the image
  of the chosen embedding `closureEmbedding F L : L →ₐ[F] AlgebraicClosure F`,
  inflates it to continuous absolute `H²` by `closureInflation`, and applies
  the absolute invariant.

`UnramifiedH2Exhaustion.{u}` is the Library statement that every continuous
absolute `H²` class of a p-adic field comes from a finite unramified stage. Each
proposition below quantifies over its proofs `hEx`. Since the statement is a
proposition, all proofs give the same family.

## The five propositions

All five are in the namespace `Langlands.ClassFieldTheory.Local`. Each has the
form `∀ (hEx : UnramifiedH2Exhaustion.{u}) (p : ℕ) [Fact p.Prime],
(localInvariantFamily hEx p).C` for one Library clause `C`:

- `LocalInvariantFamilyContinuousStatement`: `C = ContinuousInvariantProperties`
  (`ClassFormation`). This is the conjunction of four facts:
  - `LocalAbsoluteH1Vanishing.{u} p`: continuous absolute `H¹` of the units of
    the algebraic closure vanishes for every p-adic field;
  - `AbsoluteIsomorphisms`: every absolute invariant is bijective;
  - `AbsoluteRestriction`: actual continuous restriction along a finite
    extension `E/F` of p-adic fields, with any supplied compatible
    closure embedding, multiplies the absolute invariant by `[E:F]`;
  - `OrdinaryClosureCompatibility` (`FiniteInvariantCompatibility`): for every
    finite Galois intermediate field `E` of `AlgebraicClosure F / F`, the
    absolute invariant of `closureInflation F E 2 x` equals the relative
    invariant of `x`.
- `LocalInvariantFamilyRelativeImagesStatement`: `C = RelativeImages`
  (`Invariants`). Every relative invariant of a finite Galois `L/F` is
  injective, and its range is `denominatorSubgroup [L:F]`, the subgroup of
  `ℚ/ℤ` killed by `[L:F]`.
- `LocalInvariantFamilyInflationStatement`: `C = InflationCompatibility`
  (`ClassFormation`). For every tower `F ⊆ L ⊆ M` with `L` and `M` finite
  Galois over `F`, actual inflation `relativeInflation F L M 2` preserves the
  relative invariant.
- `LocalInvariantFamilyRestrictionStatement`: `C = RelativeRestriction`
  (`ClassFormation`). For p-adic fields `F ⊆ E` (with `E` finite over `F`,
  compatibly over `Padic p`) and a finite extension `M` of `E` that is Galois
  over both, actual relative restriction `relativeRestriction F E M 2`
  multiplies the relative invariant by `[E:F]`.
- `LocalInvariantFamilyArithmeticStatement`: `C = ArithmeticNormalization`
  (`Invariants`). Let `L/F` be finite Galois. Let
  `χ : Gal(L/F) ≃* Multiplicative (ZMod n)` be an arithmetic unramified
  coordinate (`IsArithmeticUnramifiedCoordinate`): the residue action map is
  injective, and `χ⁻¹(1)` acts on the residue field of `L` as the `q`-th power
  map, where `q` is the residue cardinality of `F`. Then for every unit `a` of
  `F` of valuation `1` for its canonical local-field structure (a
  uniformizer), the relative invariant of the cyclic class
  `cyclicClass F L χ a` is `reciprocalClass n`, that is `1/n` in `ℚ/ℤ`.

Every map named above is the actual Library construction. These include
continuous restriction, closure inflation, finite inflation and restriction,
and the cyclic class.

## Intended use

The target `LocalAbsoluteCorestrictionCompatibleClassFormationStatement` (task
`f8ddc947-2d65-4e22-a2a4-e2f4844c8e78`) asks for one invariant family with all
local class-formation laws. The intended witness is
`localInvariantFamily hEx p`, where `hEx` is a proof of
`UnramifiedH2Exhaustion` (task `3263cf33`). These five propositions are the
family-specific laws. The remaining clauses follow generically. The relative
conjugacy and corestriction laws and the absolute corestriction law come from
`InvariantTransferConsequencesStatement`. The cup-product laws come from
`ClassFormationCupLawsStatement`. The fundamental-class laws come from the
published `relativeFundamentalClassConsequences`. `H¹` vanishing for finite
Galois extensions comes from the published `finiteRelativeH1Vanishing`.

## Provenance

Provenance: derived. Jean-Pierre Serre, *Local Fields* (1979), Chapter XIII,
§4, Theorem 1 (printed pages 195–196, PDF pages 200–201) states that the
Brauer groups `H²(/E)` of the finite subextensions `E` of a separable
closure, with the invariants `inv_E`, form a class formation. Axiom I is
Hilbert 90 (Chapter X, Prop. 2). Axiom IIa is Corollary 2 to Proposition 7 of
§3, and axiom IIb is Proposition 7 itself (printed pages 193–194, PDF
pages 198–199). Proposition 6 (printed page 193, PDF page 198) states that
`inv_K` is an isomorphism, and `inv_K` is defined just after it. That
definition passes to the maximal unramified extension, takes the valuation and
evaluates the resulting character at the Frobenius `F`.

The five propositions split that theorem into the clauses of the Library's
predicates, for the concrete family built from those definitions.

- Bijectivity and the restriction formula of the absolute invariant are
  Propositions 6 and 7.
- Closure compatibility, the image clause and inflation compatibility express
  Serre's identification of `H²(L/E)` with a subgroup of `H²(/E)` through
  inflation (Chapter XI, §2, printed page 167, PDF page 173). Here they are
  stated for abstract finite Galois extensions instead of subfields of one
  closure.
- Relative restriction is Proposition 7 on finite relative groups.
- Arithmetic normalization records the Frobenius convention in the definition
  of `inv_K` on the cyclic class of a uniformizer in an unramified extension.

The registered source is `serre-1979-local-fields`,
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
