# Exact trace images at a prime ramification break

Worker 27 supplied the precise statement design and its source/dependency
specification. Worker 384 implemented this Lean/English pair and checked the
cited original and author corrections. The module defines the closed proposition
`Langlands.LocalClassField.PrimeRamifiedTraceIdeals.{u,v}`. It supplies a theorem
target, without an arithmetic proof.

## Quantifiers and hypotheses

For every natural prime `p` with `[Fact p.Prime]`, the proposition quantifies
`F : PadicField.{u} p` and `L : PadicField.{v} p` at independent arbitrary
universe levels. It retains every supplied instance of
`Algebra F.Carrier L.Carrier`, its compatible
`IsScalarTower (Padic p) F.Carrier L.Carrier`, finite dimensionality, and
Galoisness. Write

```text
ell = Module.finrank F.Carrier L.Carrier,
TF = F.canonicalTopologicalData,
TL = L.canonicalTopologicalData.
```

The degree `ell` is assumed prime, and total ramification is expressed by
`TL.ramificationIndex = ell * TF.ramificationIndex`. For every natural `t`,
the only break hypothesis is

```text
∀ i : Nat, Ramification.Padic.lowerRamificationGroup TL F.Carrier i
  = if i ≤ t then top else bottom.
```

These are the actual lower ramification groups, defined using the action on
`TL.Integers`. No trace containment, different formula, or desired exponent
is a hypothesis. The tame case `t = 0` is included.

## Exact trace image

Put `d = (t + 1) * (ell - 1)`. For every natural `n`, put
`r = (d + n) / ell`, where subtraction and division are natural arithmetic.
Primality of `ell` ensures its positivity; thus `r` is the floor of
`(d + n) / ell` in the source's notation.

For every `y : F.Carrier`, the conclusion is the equivalence

```text
(∃ x : TL.Integers, x ∈ (maximalIdeal TL.Integers)^n
  ∧ Algebra.trace F.Carrier L.Carrier (x : L.Carrier) = y)
↔
(∃ a : TF.Integers, a ∈ (maximalIdeal TF.Integers)^r
  ∧ (a : F.Carrier) = y).
```

The maximal ideals here are `IsLocalRing.maximalIdeal` of the canonical
integer rings, and all displayed coercions are their actual inclusions into
the fields. The trace is Mathlib's field trace `Algebra.trace` for the supplied
extension algebra. The equivalence identifies the exact trace image as a set
of base-field elements. In particular, it includes a trace preimage in the
specified ideal power for each element on the right, as well as containment
of every trace on the left. No linear span replaces the image and no bundled
integral trace map is assumed. The exponent `n = 0` is retained, with the
zeroth ideal power equal to the whole integer ring.

## Original source and derived encoding

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
Graduate Texts in Mathematics 67, Springer, 1979, registered as
`serre-1979-local-fields`; retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Chapter V, §3, printed p.83 / PDF p.90, Lemma 3 gives the different exponent
`(t + 1)(ell - 1)` in the cyclic prime-order totally ramified setting.
Lemma 4 gives the exact trace ideal for every integer `n ≥ 0`, with exponent
the floor of `((t + 1)(ell - 1) + n) / ell`. Its proof invokes Chapter III,
Proposition 7. The original PDF pp.90–92 were read, and p.90 was also inspected
as an image to verify the formulas.

Serre's cyclic prime-order hypothesis is encoded here by prime degree and
Galoisness: the resulting finite Galois group has prime order and hence is
cyclic. Canonical p-adic data, the explicit lower-group break condition,
natural-number division, and the pointwise equivalence of actual field-element
images are the derived Lean formulation of Lemmas 3–4. The explicit expression
`d` is arithmetic notation; the module does not introduce a surrogate different.
Proving this proposition will require the arithmetic comparison with the actual
different and trace ideals. This module does not establish that comparison.

The registered author corrections, *Corrections to J-P. Serre's books* (2019),
`serre-book-corrections-2019`, retained at
`/home/taskhub/pilot/literature/Jean-Pierre Serre — Corrections to J-P. Serre's books (2019).pdf`,
SHA256 `b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`,
were read at PDF pp.2–3. The *Local Fields* list has no correction to printed
p.83; its nearby corrections to printed pp.74–75 distinguish the Herbrand
symbols.

## Scope

This target states only the trace-image formula. It makes no norm-expansion
or graded norm claim. The arithmetic proof and the proof of existence of the
actual break belong to separate work coordinated by Worker 27. Compilation
and exact declaration inspection check elaboration and the return type `Prop`;
they do not prove the asserted arithmetic.
