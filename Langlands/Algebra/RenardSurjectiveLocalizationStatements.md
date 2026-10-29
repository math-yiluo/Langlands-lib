# Surjective canonical map and the actual power-kernel quotient

Authors: Worker 709 (statement design and shared draft) and Worker 751
(submission). This pair supplies the statement unit of focused task
`1b197ef2-b9a5-4bf3-bc02-675038be24ca` revision 1 under the whole-book
Renard parent `f5d1f399-a1f8-4ab5-a981-90b92abd4857`. It contains
statement declarations only: no proof, theorem or axiom.

The module is `Langlands.Algebra.RenardSurjectiveLocalizationStatements`.
Its three Prop-valued definitions belong to the namespace
`Langlands.Renard.EndomorphismLocalization`. They state the
surjective-canonical-map corollary using the actual published
localization and the actual published power-kernel quotient.

## Original source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated **9 July 2026**, Appendix A.III.1, unnumbered corollary after
example 5 and its lemma, printed p. 253 / PDF p. 259. The governing original
is registered as `renard-2026-representations-groupes-reductifs-padiques`
(SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
The corollary reads:

> Corollaire. Supposons que le morphisme canonique ι : L → L_a soit
> surjectif. Soit K = ⋃_{n∈ℕ} ker aⁿ, et L' = L/K. Alors (L_a, ã) est
> isomorphe à (L', a').

Its setting is that of the preceding lemma: L is a vector space over a
field k and a is an endomorphism of L. Part (ii) of the lemma defines
K, notes that K is stable under a, and lets a' be the endomorphism of
L' = L/K induced by a. Example 5 on printed p. 252 / PDF p. 258 defines
the localization (L_a, ã), with ã invertible, the canonical morphism
ι : (L, a) → (L_a, ã), and morphisms of pairs as linear maps intertwining
the endomorphisms. Workers 709 and 751 each re-read PDF pp. 258–259 and
inspected the rendered PDF p. 259 for this pair.

The registered supplementary author errata
`renard-2010-corrections-complements` (SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`)
were re-read on PDF pp. 18–19. Those pages list corrections for 2010
printed pages 280–322, and none concerns this corollary. They are an
older-edition check only; the 2026 original remains the reference. The
public Appendix A source-discrepancy note concerns the scalar-inverse
condition of example 4. It does not affect this encoding, because
`localizedEnd a` is the actual multiplication by X on the actual
localization, whose invertibility is proved in the localization module.

The following are internal formalization content rather than claims of
the book:

- **Commutative rings.** The source corollary is over a field. The ring
  declaration extends it to an arbitrary commutative ring and module. The
  field declaration restates the source case explicitly.
- **Universes.** The ring (or field) and the module live in independent
  universes u and v.
- **Canonical compatibility and uniqueness.** The source asserts only an
  isomorphism of pairs. The statements also require the equivalence to
  send `iota a v` to the class of v, and assert that exactly one
  equivalence has both properties. Since `iota a` is surjective by
  hypothesis, the compatibility equation determines the map. The book
  does not state this uniqueness.

## Actual data and universe scope

The general data are exactly

```text
R : Type u, [CommRing R]
V : Type v, [AddCommGroup V], [Module R V]
a : Module.End R V
```

with independent u and v. The published localization module
`Langlands.Algebra.RenardEndomorphismLocalization` supplies
`Localized a : Type (max u v)`, the actual Mathlib localization of the
polynomial-evaluation module `Module.AEval' a` at the powers of X; its
canonical map `iota a : V →ₗ[R] Localized a`, v ↦ v/1; and
`localizedEnd a : Module.End R (Localized a)`, multiplication by X.

The published quotient module
`Langlands.Algebra.RenardEndomorphismQuotient` supplies

```text
powerKernel a = ⨆ n : ℕ, LinearMap.ker (a ^ n)
PowerKernelQuotient a = V ⧸ powerKernel a : Type v
quotientProjection a = (powerKernel a).mkQ : V →ₗ[R] PowerKernelQuotient a
quotientEnd a = (powerKernel a).mapQ (powerKernel a) a _ :
  Module.End R (PowerKernelQuotient a).
```

Its lemma `mem_powerKernel_iff` identifies `powerKernel a` with the
literal increasing union of the kernels; exponents include zero, which
contributes only the zero kernel. So `PowerKernelQuotient a` is Renard's
L' = L/K, `quotientProjection a` is the canonical projection, and
`quotientEnd a` is the induced a'. The codomain of the equivalence below
is this quotient itself, not the localization of the quotient.

The sole additional hypothesis is `Function.Surjective (iota a)`. It
concerns the original localization map. Surjectivity of the quotient
projection is a different, always valid, property and is not the
hypothesis. No injectivity, surjectivity or bijectivity of a, kernel
equality for `iota a`, quotient-operator invertibility, chosen
equivalence, finite dimension, finite generation, Noetherianity or
stabilization is assumed. Zero rings and zero modules are allowed.

## Statement declarations

`SurjectiveIotaQuotientStatement` (universes u, v) universally quantifies
over the ring data above, assumes that `iota a` is surjective, and asserts
that there is exactly one

```text
e : Localized a ≃ₗ[R] PowerKernelQuotient a
```

satisfying both equations

```text
e.toLinearMap.comp (localizedEnd a) =
  (quotientEnd a).comp e.toLinearMap

e.toLinearMap.comp (iota a) = quotientProjection a.
```

The first equation says that e is an isomorphism of pairs from
(L_a, ã) to (L', a'), in the direction of the source. The second says
that e sends `iota a v` to the class of v. Both equations occur inside
the unique-existence predicate `∃!`. Invertibility of e is part of its
`LinearEquiv` type and is therefore a conclusion.

`FieldSurjectiveIotaQuotientStatement` (universes u, v) states the same
assertion directly for every field `k : Type u`, every k-vector space
`V : Type v` and every `a : Module.End k V`, of arbitrary characteristic
and dimension. It repeats the hypothesis, the actual equivalence and both
equations. This is the source-facing form of the corollary, with the
internal canonical-compatibility and uniqueness strengthening above.

`SurjectiveIotaQuotientStatements` is the conjunction
`SurjectiveIotaQuotientStatement.{u, v} ∧
FieldSurjectiveIotaQuotientStatement.{u, v}`. It is the intended target
of a later proof task.

## Dependencies and remaining work

The only direct import is the published quotient construction
`Langlands.Algebra.RenardEndomorphismQuotient`, which imports the
published localization `Langlands.Algebra.RenardEndomorphismLocalization`.
Worker 751 implemented the published localization; Workers 709 and 911
implemented the published quotient. This pair copies neither
implementation.

A possible later proof uses the kernel equality
`ker (iota a) = powerKernel a`, which must itself be proved; this
statement does not assume it. Descending `iota a` to the actual quotient
then gives an injective map, which is surjective by the hypothesis; its
inverse is e. The representative law `quotientEnd_projection` and the
published `iota_intertwines` give the operator equation, and surjectivity
of `iota a` gives uniqueness from the canonical-map equation.

The following remain separate obligations, not supplied here: the
kernel/exhaustion statements and their proofs, the comparison between
the localization of L and that of L/K, the inverse-power extension
converse, general possibly nonunital algebra actions, categorical
packaging, localization exactness, and the final C.II
finite-localization proposition.

## Development checks

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, against the public
Library at commit `c76b7751d5e9d82df7a4e5d57684adcee5d41cb7`, check
`b0a63078-7bce-4a43-87ad-bfc5f595dc27` compiled this module with no
errors or warnings. Inspection of the aggregate reports a definition
returning Prop, level parameters u and v, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. Private diagnostic
`e111fd1e-d50b-450b-88ae-7fd994e38118` printed the complete bodies of
all three declarations and the signatures of the seven imported
constructions. It also checked, by `Iff.rfl`, that the ring statement is
definitionally the same proposition with the codomain written as
`V ⧸ ⨆ n : ℕ, LinearMap.ker (a ^ n)` and the projection as its `mkQ`.
These are development checks only; they supply no independent semantic
acceptance and no proof.
