# Internal Noetherian core for endomorphism localization

This module specifies three internal propositions and their conjunction. It
contains no proofs of those propositions. Worker 709 derived this auxiliary
interface while preparing the finite-localization proposition in David
Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, Appendix C.II, printed page 279 / PDF page 285.
The propositions are implementation prerequisites, not a translation of
that final proposition.

The motivating registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 709 read and visually inspected the motivating PDF page. Worker 735
rechecked the fingerprint, the text of PDF285 and the localization passage
A.III.1, example 5 with its lemma and corollary, printed pages 252–253 /
PDF pages 258–259. The governing edition already incorporates the adjacent
quotient-index correction from the supplementary older author errata. That
correction does not affect these internal targets.

## Actual data and hypotheses

The scalar ring `R : Type uR` is an arbitrary ordinary unital `Ring`;
commutativity and `IsNoetherianRing R` are not assumed. The carriers
`M : Type uM` and `N : Type uN` are additive commutative groups with
ordinary unital `Module R` structures. All three universes are independent.
There is no finite-dimensionality, countability or nontriviality assumption.
Mathlib's `IsNoetherian R M` means that every actual `R`-submodule of `M`
is finitely generated. The corresponding hypothesis on `N` has the same
meaning.

The maps are actual Mathlib linear maps: `a : Module.End R M`,
`e : N ≃ₗ[R] N`, and `f : M →ₗ[R] N`. A linear equivalence supplies both
directions of the target automorphism. Powers use composition, with the
identity as exponent zero. Kernels, ranges and the invariant submodule
are actual `Submodule` values.

The import dependencies are Mathlib's linear-equivalence and Noetherian
definition modules. No replacement module category, formal localization
certificate, or assumed endomorphism-stability result is introduced.

## Declaration correspondence

All declarations are `def` declarations returning `Prop` in namespace
`Langlands.LinearAlgebra.NoetherianLocalizationCore`.

| Declaration | Full mathematical content |
| --- | --- |
| `InversePreservesSubmoduleStatement` | For a Noetherian ordinary `R`-module `M`, an actual automorphism `e : M ≃ₗ[R] M` and submodule `P`, if `e` carries every member of `P` into `P`, its inverse also carries every member of `P` into `P`. |
| `ExhaustionSurjectiveStatement` | Suppose only the target `N` is Noetherian. Assume `f (a x) = e (f x)` for every `x : M`, and for every `y : N` there are `n : ℕ` and `x : M` with `(e ^ n) y = f x`. Then `f` is surjective. |
| `StablePowerStatement` | Suppose both ordinary modules are Noetherian and the preceding intertwining and exhaustion conditions hold. Assume also that for every `x` killed by `f`, some nonnegative power of `a` kills `x`. Then `f` is surjective, and there is one positive `n` with `ker f = ker (a ^ n)`, `ker (a ^ n) = ker ((a ^ n) ^ 2)` and `range (a ^ n) = range ((a ^ n) ^ 2)`. |
| `NoetherianLocalizationCoreStatement` | The conjunction of these three closed targets, in that order. It adds no mathematical condition. Its universe parameter order is `uR uM uN`. |

Every target binds its ring, carriers, instances and maps internally.
The first target uses only `uR uM`; the other two and the aggregate use
`uR uM uN`. The local-nilpotence exponent and the exhaustion exponent may
be zero and depend on their vector. The concluding exponent is positive
and common to all three displayed kernel/range equalities. Stability here
is written out as the two equalities for the actual power and its square,
so it does not depend on a complex-only stability predicate.

## Derived provenance and proof interface

Renard's proposition on printed page 279 takes a commutative Noetherian
complex algebra `B`, a finitely generated `B`-module `L` and
`a ∈ End_B(L)`, and assumes that the localization `(L_a, ã)` of `L` at `a`
(A.III.1, example 5) is also a finitely generated `B`-module. It concludes
that `a` is eventually stable and that, for every positive `n` with `a^n`
stable, `K = ker a^n` and `I = Im a^n` satisfy `L = K ⊕ I`, with `(L_a, ã)`
isomorphic to `(I, a|_I)`. Its proof shows that the canonical map
`ι : L → L_a` is surjective, identifies `(L_a, ã)` with the quotient of `L`
by `⋃ₙ ker aⁿ` (lemma and corollary of A.III.1), and finds one nonzero `n`
for which this union equals `ker aⁿ`. The present internal interface
isolates a reusable algebraic argument for those intermediate steps, once
the localization construction has supplied intertwining, power exhaustion
and local nilpotence of the canonical map's kernel.

The auxiliary statements use arbitrary unital rings and directly assume
Noetherian ordinary modules. These hypotheses describe the internal
argument; they are not substituted for the source's coefficient and action
conventions. There is no assertion here that arbitrary maps satisfying
the premises have been constructed from a localization.

A prospective proof can use a different route from Renard's
inverse-polynomial argument. If an automorphism preserves `P`, it induces
a surjective endomorphism on the actual Noetherian quotient by `P`.
Mathlib's Hopfian theorem makes this quotient map injective, forcing
inverse preservation. Applying this fact to `range f` gives surjectivity
from exhaustion. Noetherian stabilization of the source power kernels
then bounds the locally nilpotent kernel. The resulting equality with
`ker f`, together with surjectivity and the inverse target iterate, gives
the two equalities for the positive source power. This paragraph describes
a proposed proof route, not a proof supplied by this statement module.

## Intended instantiation

The planned application, which this module does not carry out, takes
`M = L`, `N = L_a`, `f = ι` and `e` the linear automorphism of `L_a` with
forward map `ã` and inverse `ã⁻¹`. The premises would come from the actual
localization as follows.

- Intertwining `f (a x) = e (f x)` is the statement that `ι` is a morphism
  of pairs, `ι ∘ a = ã ∘ ι`.
- Exhaustion is the final assertion of the A.III.1 lemma,
  `L'_{a'} = ⋃ₙ (ã')⁻ⁿ(L')`, carried to `(L_a, ã)` by its isomorphism.
  Applying `ãⁿ` turns `y = ã⁻ⁿ(ι x)` into the displayed form
  `(e ^ n) y = f x`.
- Local nilpotence of the kernel is the inclusion `ker ι ⊆ ⋃ₙ ker aⁿ`.
  It follows from the same lemma: `ι` factors through `L' = L/K`, with
  `K = ⋃ₙ ker aⁿ`, followed by the injective canonical map `ι'` and the
  isomorphism of the two localizations. The lemma's proof gives the reverse
  inclusion.
- Noetherianity of `L` and `L_a` would come from their finite generation
  over the Noetherian algebra, after the comparison of the source's
  algebra and action conventions with an ordinary unital `Module` that is
  listed below.

`StablePowerStatement` would then give surjectivity of `ι` and one positive
`n` with `ker ι = ker aⁿ`, `ker aⁿ = ker (aⁿ)²` and `Im aⁿ = Im (aⁿ)²`. The
last two equalities are the stability condition of the C.II definition,
printed page 276 / PDF page 282, which the source also applies to
endomorphisms of `B`-modules. The statement supplies one such `n`. It does
not cover every stable power, and it states neither `L = K ⊕ I` nor the
identification of `(L_a, ã)` with `(I, a|_I)`.

## Separate obligations

The parent program still owes the actual vector-endomorphism localization
at powers of `X`, the canonical map and target automorphism, and proofs of
their intertwining, exhaustion, kernel-union and quotient-identification
properties. Its extension to compatible actions of a possibly nonunital
complex algebra also remains separate.

In particular, ordinary unital modules do not by themselves implement
the book's nonunital algebra and action conventions. Comparisons of
compatible stable vector subspaces, unitized submodules, finite generation
and Noetherianity must be made explicitly before applying this internal
core to the full final proposition. The source's converse localization
assertions and endomorphism-module finiteness assertion are also separate.
So are the conclusions for every positive stable power, the decomposition
`L = K ⊕ I` and the identification of `(L_a, ã)` with `(I, a|_I)`.
Neither compilation of this file nor a future proof of its targets
discharges those obligations or the whole-book program.
