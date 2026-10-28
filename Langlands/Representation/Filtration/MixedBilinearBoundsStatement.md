# Mixed bilinear finite-filtration bound statements

This internal statement family extends the algebraic scope of
`Langlands.Representation.Filtration.InvariantBilinearBounds` to the actual
mixed covariance spaces in
`Langlands.Representation.Filtration.MixedBilinear`. It imports that published
construction and uses the existing `ObjectRepFiltration` and its actual
`gradedRepresentation`. No original-literature assertion is transcribed.

The module defines four propositions in namespace `Langlands.MixedBilinear`.
It supplies no proofs of them. The aggregate `FiltrationBoundsStatement` is the
exact target intended for a separate proof contribution. This unit establishes
no JPSS theorem or unequal-rank uniqueness result.

## Universes, quantifiers and covariance

Each declaration has six independent universe parameters in the order
`.{uK, uG, uH, uI, uV, uW}`. The first three propositions universally quantify
inside their definition over the field `k : Type uK`, monoids `G : Type uG`
and `H : Type uH`, and test type `I : Type uI`, together with all their
remaining data. They have no outer term parameters. The aggregate is the
conjunction of those three fully uniform propositions at the same six levels.
The representation carriers have the independent levels `uV` and `uW`.

For arbitrary functions `a : I → G`, `b : I → H` and `χ : I → k`, the published
space `forms a b χ ρ σ` consists of the actual bilinear forms satisfying

```text
∀ i v w, B (ρ (a i) v) (σ (b i) w) = χ i * B v w.
```

The test maps need no homomorphism property. The type `I` needs no algebraic
structure and may be empty. All form spaces use the published argument order
`a b χ ρ σ`, and `length a b χ ρ σ : ℕ∞` is their actual `Module.length k`.
There is no separate assumption of finite dimension or finite module length.
Every graded term retains exactly the same `a`, `b` and `χ` as the original
space.

## The three uniform targets

`FiltrationLengthBoundStatement` quantifies over `A : Rep.{uV} k G`,
`B : Rep.{uW} k H`, natural numbers `m,n`, supplied actual filtrations
`f : ObjectRepFiltration A m`, `g : ObjectRepFiltration B n`, and all the test
data. Its conclusion is

```text
length a b χ A.ρ B.ρ ≤
  ∑ i : Fin m, ∑ j : Fin n,
    length a b χ (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ.
```

The left filtration is a filtration over `G`, and the right one is a
filtration over `H`. They are the original supplied filtrations; the target
uses no restriction to a common ambient subgroup. The double sum ranges over
actual graded positions, preserving multiplicities even when several quotients
are isomorphic. No factor is assumed simple or nonzero. Repeated steps and
zero graded quotients are allowed. Either length may be zero: an empty sum
then has value zero, and a zero-to-full filtration with no graded positions
forces its underlying representation to be zero.

`SinglePairLengthBoundStatement` quantifies over the same data and then
positions `i₀ : Fin m`, `j₀ : Fin n`. Its only additional premise is

```text
∀ i j, i ≠ i₀ ∨ j ≠ j₀ →
  length a b χ (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ = 0.
```

It concludes

```text
length a b χ A.ρ B.ρ ≤
  length a b χ (f.gradedRepresentation i₀).ρ (g.gradedRepresentation j₀).ρ.
```

The selected pair is allowed to have length zero. The premise concerns all
other positions, including repeated isomorphic factors. If either filtration
length is zero, there is no choice of its selected position, so that instance
of this universally quantified target is vacuous.

`LengthOneProportionalityStatement` instead quantifies over arbitrary carriers
`V : Type uV`, `W : Type uW`, their `AddCommGroup` and `Module k` instances,
representations `ρ : Representation k G V`, `σ : Representation k H W`, and
the test data. It states

```text
length a b χ ρ σ ≤ 1 →
  ∀ B₀ B : forms a b χ ρ σ, B₀ ≠ 0 → ∃ c : k, B = c • B₀.
```

No filtration or existence of a nonzero form is assumed. The zero form space
is covered, with the conditional conclusion vacuous when no nonzero `B₀`
exists. For a supplied nonzero `B₀`, the conclusion concerns every form `B`,
including zero, and the scalar is an element of `k`.

## Aggregate and scope

`FiltrationBoundsStatement` is definitionally the conjunction

```text
FiltrationLengthBoundStatement ∧
  SinglePairLengthBoundStatement ∧
    LengthOneProportionalityStatement
```

with all three components explicitly instantiated at the same six independent
universe levels. All four declarations are Prop-valued `def` statements.

The targets concern internal linear algebra over a field and two independent
ambient monoids. They assume no topology, smoothness, irreducibility,
admissibility, or Whittaker-functional uniqueness. The existing mixed
construction already proves the elementary subrepresentation-plus-quotient
bounds; this module names the subsequent finite-filtration and proportionality
obligations. Their proofs, concrete unequal-rank adapters, exceptional-set
arguments and full uniqueness results remain separate work.
