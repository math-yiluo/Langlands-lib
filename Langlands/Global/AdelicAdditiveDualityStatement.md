# Additive self-duality and the diagonal annihilator of the actual adeles

Author: Worker 1592.

`Langlands.Global.AdelicAdditiveDualityStatement.{u}` is a proposition
definition for every `K : Type u` with `[Field K] [NumberField K]`. For every
`ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)` trivial
on the actual diagonal image of `K`, it states both the topological additive
self-duality of the adeles under the multiplication pairing and the equality
of the diagonal field with its annihilator. This file states the result;
its proof is a separate obligation.

## Actual objects and character hypotheses

The imported `Langlands.Global.Adelic` supplies `Adeles K` as Mathlib's
`NumberField.AdeleRing (NumberField.RingOfIntegers K) K`. It uses the actual
archimedean completions and the cofinite restricted product of the actual
finite completions relative to their valuation subrings, with their existing
product and restricted-product topology.

`diagonal K` is the existing ring homomorphism
`algebraMap K (Adeles K)`. Its image in this statement is literally
`Set.range (diagonal K)`. The statement requires no topology on `K`.

The existing unitary additive-character bundle contains a `Circle`-valued
additive character, a proof of continuity in the adele topology, and a proof
that it is nontrivial. Its additive-character laws are
`ψ (x + y) = ψ x * ψ y` and `ψ 0 = 1`. The additional displayed hypothesis
is `∀ x : K, ψ (diagonal K x) = 1`. Thus nontriviality concerns the whole
adele group and is compatible with triviality on the diagonal field.

## Self-duality and group notation

The first conclusion asserts the existence of

```lean
e : Multiplicative (Adeles K) ≃ₜ*
  PontryaginDual (Multiplicative (Adeles K))
```

and specifies its value at every pair `a, x` by

```lean
e a x = ψ (Multiplicative.toAdd a * Multiplicative.toAdd x).
```

`Multiplicative` is Mathlib's type tag for viewing an additive group as a
multiplicative group. It retains the underlying adele topology: its group
multiplication means addition of adeles, its identity is the zero adele,
and its inverse means negation. The `*` on the right of the evaluation
formula is instead multiplication in the actual adele ring, after removing
the tags with `Multiplicative.toAdd`. Additivity of the resulting characters
corresponds to distributivity in that ring and the additive-character laws.

`PontryaginDual` is Mathlib's full group of continuous homomorphisms to
`Circle`, with its compact-open topology and pointwise multiplication. Its
identity is the constant-one character. The target includes that character;
it is not restricted to nontrivial characters. The evaluation formula sends
the zero adele to this identity. The notation `≃ₜ*` is
`ContinuousMulEquiv`, so it requires a group equivalence whose map and inverse
are continuous in these topologies.

The evaluation formula fixes the pairing directly, without supplying a
self-duality certificate as input. It uses `ψ(a*x)` with a plus sign and
no conjugation. The commutativity of the adele ring identifies this order
of the two factors with the evaluation order in the source.

## Diagonal annihilator

The second conclusion quantifies all `a : Adeles K` and states

```lean
(∀ x : K, ψ (a * diagonal K x) = 1) ↔
  a ∈ Set.range (diagonal K).
```

The left side says that the character paired with `a` is trivial on the
actual diagonal field. The right side says that `a` is itself the diagonal
image of an element of `K`. The conclusion includes zero. The reverse
implication follows mathematically from the diagonal ring homomorphism and
the hypothesis on `ψ`; the forward implication is the arithmetic annihilator
assertion in the source.

## Original source and correspondence

André Weil, *Basic Number Theory*, second edition, Springer, 1973,
Chapter IV, §2, Theorem 3 and its proof, printed pp.65–69
(PDF pp.82–86). The theorem is stated on printed p.66 (PDF p.83); printed
p.67 (PDF p.84) explicitly establishes bicontinuity, and the final paragraph
on printed p.69 (PDF p.86) extends the result to every nontrivial character
trivial on the field. The surrounding Corollaries 1 and 2 on printed
pp.69–70 (PDF pp.86–87) were also read for context.

Registered source: `weil-1973-basic-number-theory`.
Retained original:
`/home/taskhub/central-library/Weil--Basic number theory (book, 2nd edition)--1973.pdf`.
SHA256:
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
PDF page numbers here are one-based. Worker 1592 read these original pages
directly and visually checked the theorem on printed p.66. No source-specific
errata file was present in the checked Library or project notes.

Weil treats finite-dimensional vector spaces over an A-field. Here the field
is a number field and `E = K` is one-dimensional. Identifying its algebraic
dual with `K` by `a ↦ (x ↦ a*x)` identifies the adelic bilinear evaluation
with multiplication in `Adeles K`. The theorem's isomorphism from the adelic
algebraic dual onto the topological dual is precisely the first conclusion.
Its final assertion gives the forward implication of the second conclusion;
the diagonal-triviality hypothesis gives the converse, as explained above.
The arbitrary universe parameter is retained in the Lean definition.
