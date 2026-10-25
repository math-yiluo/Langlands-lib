# Prime-degree norm expansion modulo traces

Worker 27 specified the target and its source correspondence; Worker 107
prepared the Lean proposition and this explanation after reading the original
and the registered corrections. The module defines
`Langlands.LocalClassField.PrimeNormTraceExpansion.{u,v}`. It is a statement,
with no proof of the norm expansion.

For every prime `p`, let `F : PadicField.{u} p` and `L : PadicField.{v} p`
have independent arbitrary universes. The proposition quantifies the actual
`Algebra F.Carrier L.Carrier`, its compatible
`IsScalarTower (Padic p) F.Carrier L.Carrier`, finite dimension, and Galoisness.
Set

```text
ell = Module.finrank F.Carrier L.Carrier,
TF = F.canonicalTopologicalData,
TL = L.canonicalTopologicalData,
m_L = IsLocalRing.maximalIdeal TL.Integers.
```

Assume `Nat.Prime ell` and
`TL.ramificationIndex = ell * TF.ramificationIndex`. Here ramification indices
are the published absolute indices measured by the canonical order of `p`.
This equality expresses the totally ramified setting over `F`; it does not
require either field to have absolute ramification index one. The Galois
prime-degree hypotheses express Serre's cyclic group of prime order, without
supplying a generator or a ramification break.

For every natural number `n` and every `x : TL.Integers` in `m_L ^ n`, the
conclusion asserts that there exists `z : TL.Integers` in `m_L ^ (2 * n)` with
the following equality in `F.Carrier`:

```text
Algebra.norm F.Carrier (1 + (x : L.Carrier)) - 1
  - Algebra.trace F.Carrier L.Carrier (x : L.Carrier)
  - Algebra.norm F.Carrier (x : L.Carrier)
= Algebra.trace F.Carrier L.Carrier (z : L.Carrier).
```

Both maps are Mathlib's field maps on the given extension: `Algebra.norm`
is the determinant of multiplication, and `Algebra.trace` is the trace of
multiplication. The integer ring and maximal ideal are those of `TL`'s
canonical valuation. The existential witness states membership in the exact
trace image of the indicated ideal power; no arbitrary error ideal or assumed
trace-image formula is used.

The quantifier includes `n = 0`, where the zeroth ideal power is the whole
integer ring. It also includes `x = 0`, degree `ell = 2`, and `1 + x = 0`.
The formula is a field equality and uses no norm on units or nonvanishing
hypothesis. No trace-ideal exponent, graded norm coefficient, completeness
claim, or norm-surjectivity assertion is included. There is no arithmetic
norm-expansion premise.

## Source and encoding

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
GTM 67, Springer, 1979, Chapter V, §3, Lemma 5 and its proof, printed
pp.83–84 / PDF pp.90–91. The registered source is
`serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Serre states the congruence
`N(1+x) ≡ 1 + Tr(x) + N(x) mod Tr(m_L^(2*n))` in the cyclic prime-degree,
totally ramified setting. His expansion of the conjugate product separates
the empty, singleton, and full subsets. Every remaining subset has a free
orbit under the prime-order Galois group. Each orbit contributes a trace of
a product of at least two conjugates, belonging to `m_L^(2*n)`; trace
additivity combines the contributions. This describes the source argument,
not an implemented Lean proof.

The derived encoding specializes to the Library's canonical p-adic fields,
uses prime dimension and Galoisness to express the cyclic prime-order setting,
and replaces congruence modulo the trace image by its literal existential
membership meaning. The total-ramification hypothesis is retained from the
source even though the orbit argument suggests a more general statement.
No such generalization is asserted here.

The registered *Corrections to J-P. Serre's books* (2019),
`serre-book-corrections-2019`, PDF pp.2–3, SHA256
`b76739179d067850770081597a8e9ced68135ebf80678876605f471297a4fee5`,
was also read. Its Local Fields section has no correction to printed
pp.83–84. The nearby corrections on pp.74–75 concern Herbrand notation.
No additional source-specific errata note was found in the project notes
or current Library.

Compilation and exact declaration inspection check that the closed definition
returns `Prop` with independent universes `u` and `v`; they do not prove the
arithmetic assertion. A proof successor remains separate work coordinated
by Worker 27.
