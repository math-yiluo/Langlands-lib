# Constituent-support lattice of a multiplicity-free representation

`Langlands.MultiplicityFreeSubmoduleLatticeStatement.{uK, uG, uA}` is a single
proposition definition. This pair states the assertion; it proves nothing.
It imports only `Langlands.Representation.Filtration.ConstituentSupportDefinitions`
and reuses `HasMultiplicityFreeCompositionSeries`, `jordanHolderSupport`,
`ObjectRepFiltration` and `ObjectRepFiltration.HasSimpleFactors` from the
published Library without changing them.

## Statement

The proposition quantifies over every field `k : Type uK`, every monoid
`G : Type uG` and every representation `A : Rep.{uA} k G`. Its only premise
is `HasMultiplicityFreeCompositionSeries A`, which asserts an actual finite
filtration of `A` with irreducible graded representations, any two of which are
equivalent only when their indices are equal.

Inside the proposition a local map

```
support : Subrepresentation A.ρ → Set (Rep.{uA} k G)
support S := jordanHolderSupport (Rep.of S.toRepresentation)
```

is introduced by `let`. For an invariant subspace `S`, `Rep.of S.toRepresentation`
is the actual restricted representation on the carrier `S.toSubmodule`, which
lies in the ambient carrier universe `uA`. The target universe of
`jordanHolderSupport` is set explicitly to `uA`. Thus `support S` is the set of
actual representations `τ : Rep.{uA} k G` for which some actual finite simple
series of `S` has a positive number of graded representations equivalent to
`τ`. The name `support` is only this local abbreviation; no global definition
is introduced.

The conclusion is the conjunction of six clauses:

1. For every `S : Subrepresentation A.ρ` there exist `n : ℕ` and an actual
   `s : ObjectRepFiltration (Rep.of S.toRepresentation) n` with
   `s.HasSimpleFactors`.
2. For all `S R : Subrepresentation A.ρ`, `S ≤ R ↔ support S ⊆ support R`.
3. For all such `S R`, `support (S ⊔ R) = support S ∪ support R`.
4. For all such `S R`, `support (S ⊓ R) = support S ∩ support R`.
5. `support ⊥ = ∅`.
6. `support ⊤ = jordanHolderSupport A`, where the right-hand side is again
   ascribed the type `Set (Rep.{uA} k G)`.

Order, join, meet, bottom and top are Mathlib's lattice structure on
`Subrepresentation A.ρ`: inclusion of underlying submodules, their sum, their
intersection, the zero subspace and the whole space.

Clause 1 exposes an actual finite simple series of every invariant subspace as
an explicit output for later use. Logically it already follows from clauses 2
and 5 together with the imported definitions. If `support S` is empty, then
`support S ⊆ support ⊥`, so clause 2 gives `S ≤ ⊥`, and the zero subspace has
the length-zero series. If `support S` is nonempty, any member of it is, by the
definitions of `HasJordanHolderConstituent` and `HasJordanHolderMultiplicity`,
witnessed by an actual simple series of `S`. In particular, clauses 2 and 5
already rule out a nonzero invariant subspace with empty support.
Clause 2 states both monotonicity and order reflection. Order reflection makes
`support` injective, and clauses 3–6 then state that it preserves joins, meets,
bottom and top.

## Generality and scope

The field `k`, the monoid `G` and the three universes `uK`, `uG`, `uA` are
arbitrary and independent. No group inverses, topology, smoothness,
admissibility, finite dimension or nonzero ambient object is assumed. The zero
representation is included. Its multiplicity-free witness is the empty series,
and clause 1 is then witnessed by an empty series of each invariant subspace.

The proposition does not assert that every subset of `jordanHolderSupport A`
is the support of an invariant subspace. Such a realization is false in
general, for example for a nonsplit extension of two inequivalent simple
representations. It also does not assert that a support is a finite set of
actual representations. A support is a set of actual representations, not a
chosen set of isomorphism-class representatives. It is saturated under
representation equivalence within `Rep.{uA} k G`: if `τ` and `υ` are
equivalent, the published `Langlands.equivJordanHolderMultiplicityTransport`,
applied with the identity ambient equivalence, shows that `τ` and `υ` have the
same multiplicity predicates. Hence an equivalence class of representations
meets a support either entirely or not at all. A nonempty support therefore
typically contains many actual representations; finiteness in the
composition-factor sense concerns equivalence classes.

This unit supplies only the generic finite-length support-lattice assertion.
It does not supply segment support labels, the Basic Lemma 2.6 of the source,
a description of the submodule lattice of a particular induced representation,
or any classification statement.

## Source and provenance

Provenance: derived; an internal algebraic formulation of a literature
proposition.

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
§2.4, Proposition, printed p.177 / PDF page 14. Literature ID:
`zelevinsky-1980-induced-ii`. Retained original SHA-256:
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
Printed pp.176–178 / PDF pages 13–15 of the retained original were read
directly, including the rendered page 14. No source-specific project
erratum was found.

The source states: for a multiplicity-free module `π` and `𝒥 = 𝒥H(π)`, the map
`π' ↦ 𝒥(π') = 𝒥H(π') ⊂ 𝒥` is an embedding of the lattice of submodules of `π`
into the lattice of subsets of `𝒥`. It explains this as
`𝒥(π₁ ∩ π₂) = 𝒥(π₁) ∩ 𝒥(π₂)` and `𝒥(π₁ + π₂) = 𝒥(π₁) ∪ 𝒥(π₂)`.
Step (1) of its proof shows that `𝒥(π₁) ⊂ 𝒥(π₂)` implies `π₁ ⊂ π₂`, so the
map is injective. Step (2) proves the join identity, noting that multiplicity
freeness is not needed there. Step (3) proves the meet identity by finding a
factor of multiplicity at least two in `π₁ + π₂`. The multiplicity-free
condition is that of §2.1(c), printed p.176 / PDF page 13: every composition
factor occurs with multiplicity one.

The Lean clauses correspond to this as follows. Clause 2 is the order embedding
together with step (1), clause 3 is step (2), and clause 4 is step (3). Since
`𝒥H(π')` is defined only for representations of finite length, the source uses
implicitly that every submodule of the finite-length module `π` has finite
length; clause 1 states this explicitly with actual series. Clause 5 records
`𝒥H(0) = ∅`, and clause 6 records `𝒥(π) = 𝒥`, the ambient set of
the source map.

The source's `𝒥H(π')` consists of composition-factor classes. The Lean
`support S` consists instead of all actual representations in the ambient
carrier universe `uA` that are equivalent to a factor of some actual simple
series of `S`. By the published `Langlands.jordanHolderMultiplicityIndependence`,
any two actual simple series of `S` assign each target the same count. Hence
the choice of series in this definition does not matter, as for the source's
`𝒥H`. A class in `𝒥H(π')` corresponds to the set of its actual
representatives in `Rep.{uA} k G`. That set is nonempty, because every graded
representation of a series of `S` is an actual representation in `Rep.{uA} k G`.
Distinct classes give disjoint sets, and the saturation above shows that the
support is the union of the sets of the classes in `𝒥H(π')`. Hence equality,
inclusion, union and intersection of supports correspond exactly to those of
the source's class sets. Fixing the target universe to `uA` ensures that every
factor of every invariant subspace has representatives among the targets.

Zelevinsky's modules are smooth representations of the p-adic groups `G_n`;
there, submodules of smooth representations are smooth. The Lean statement
instead concerns all invariant subspaces of an arbitrary representation of a
monoid over a field. This is the internal generality of the purely
finite-length argument above: it uses only composition series of modules
over `k[G]`. The generality is a formal algebraic presentation. It does not
claim any representation-theoretic classification theorem for arbitrary
fields or monoids.

## Related Library material

The definitions come from
`Langlands.Representation.Filtration.ConstituentSupportDefinitions`, whose
Markdown describes the actual-series encoding of support and multiplicity
freeness. The published Jordan–Hölder independence, multiplicity additivity
and monotonicity, multiplicity transport and zero-factor deletion results in
`Langlands.Representation.Filtration` are possible inputs for a later proof.
This statement neither restates nor replaces them. The generic Boolean
closure statement `Combinatorics.OrientationClosureExtremaStatement` and the
strong constituent extrema statement in `Classification` are separate and
replace none of the clauses here.
