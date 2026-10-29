# The actual power-kernel quotient of an endomorphism

Authors: Worker 709 (prepared construction and initial check) and
Worker 911 (independent source re-reading, compilation and submission).

This definition unit constructs the actual quotient by the increasing union of
power kernels and the actual endomorphism induced on that quotient. It imports
`Langlands.Algebra.RenardEndomorphismLocalization` and Mathlib's module quotient.
All new declarations are in `Langlands.Renard.EndomorphismLocalization`.

## Original source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, A.III.1, unnumbered lemma (ii) after example 5,
printed253/PDF259. Example 5 is on printed252/PDF258. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Original file:
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF258–259 were read and PDF259 was visually checked.

The supplementary author errata `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were checked on PDF18–19. No entry for this lemma was found there. This
bounded check of the older edition does not replace the governing 2026 source.
The public notes `notes/renard/appendix-a-corrections.md` and
`notes/renard/stable-quotients.md` describe related discrepancies and the
remaining localization obligations.

The source works with a vector space L over an arbitrary field k. It sets
K equal to the union of the kernels of powers of a, asserts K is a-stable,
and forms L' = L/K with the endomorphism a' induced by a. Those objects
and the laws needed to construct them are the source content of this unit.
The extension to arbitrary commutative unital coefficient rings is internal.
The precise submodule-supremum model, literal-union membership lemma, and
canonical quotient API are implementation choices, not quotations from the
book. They require no localization kernel theorem.

## Hypotheses and actual models

Every declaration has a commutative unital ring `R : Type u` with
`[CommRing R]`, a carrier `V : Type v` with `[AddCommGroup V] [Module R V]`,
and `a : Module.End R V`. The coefficient universe u and carrier universe v
are independent. The quotient stays in `Type v`; it has the additive group
and R-module structure of Mathlib's actual quotient by a submodule.

No declaration assumes finite dimension, finite generation, Noetherianity,
injectivity, nontriviality, or that a power eventually stabilizes. Zero rings,
zero modules, and zero or nilpotent endomorphisms are allowed. Specializing
`R` to any field k gives exactly the quotient and induced operator of the
source, over an arbitrary-dimensional k-vector space.

| Source object | Lean construction |
| --- | --- |
| K = union over n of ker(a^n) | `powerKernel a : Submodule R V` |
| L' = L/K | `PowerKernelQuotient a`, an abbreviation for `V ⧸ powerKernel a` |
| Projection L to L' | `quotientProjection a : V →ₗ[R] PowerKernelQuotient a` |
| a' on L' | `quotientEnd a : Module.End R (PowerKernelQuotient a)` |

`powerKernel` is defined as `⨆ n : ℕ, LinearMap.ker (a ^ n)`.
`powerKernel_def` records that formula. Here powers are compositions in
the endomorphism ring. Including n = 0 adds the zero kernel of the identity,
so the union is unchanged. The lemma statement writes the index as n
without range, its proof uses n in ℕ*, and the corollary uses n in ℕ;
all three give the same set.
`mem_powerKernel_iff a z` states

```lean
z ∈ powerKernel a ↔ ∃ n : ℕ, (a ^ n) z = 0
```

Consequently the underlying set is the literal increasing union of power
kernels, not merely the submodule they generate. The proof uses
`LinearMap.iterateKer.monotone.directed_le` and
`Submodule.mem_iSup_of_directed`; no stabilization or finiteness premise
is involved.

## Stability and quotient construction

`powerKernel_stable a hz` proves `a z ∈ powerKernel a` from
`hz : z ∈ powerKernel a`. The membership description supplies n with
a^n z = 0. Commutation of a with its own power gives
a^n(a z) = a(a^n z) = 0, with the same exponent n.
`powerKernel_le_comap a` packages this as
`powerKernel a ≤ (powerKernel a).comap a`, exactly the well-definedness
condition required by `Submodule.mapQ`.

`quotientProjection a` is `(powerKernel a).mkQ`.
`quotientEnd a` is

```lean
(powerKernel a).mapQ (powerKernel a) a (powerKernel_le_comap a)
```

Thus the descended endomorphism is supplied by an actual quotient
construction; its existence and laws are not hypotheses.

The intrinsic laws provided are:

- `quotientProjection_apply`: the projection sends z to its actual quotient
  class `Submodule.Quotient.mk z`.
- `quotientEnd_projection`: `quotientEnd a (quotientProjection a z) =
  quotientProjection a (a z)`, by reduction of `mapQ` on representatives.
- `quotientEnd_comp_projection`: the same intertwining identity as an
  equality of linear-map composites.
- `quotientProjection_surjective`: every quotient class has a representative,
  by `Submodule.mkQ_surjective`.
- `ker_quotientProjection`: the kernel of this quotient projection is K,
  by `Submodule.ker_mkQ`. This concerns the quotient projection, not the
  distinct localization map `iota a`.

Mathlib's `iterateKer` is from `Algebra/Module/Submodule/Ker.lean`;
the directed-supremum membership lemma is from
`LinearAlgebra/Span/Defs.lean`; `mkQ`, `mapQ` and their quotient laws are
from `LinearAlgebra/Quotient/Defs.lean` and `Basic.lean`, at pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`. No new axiom or proof hole is used.

## Retained statement and proof obligations

This unit supplies no claim that `quotientEnd a` or
`iota (quotientEnd a)` is injective, that K is the kernel of `iota a`, or
that the localizations of the two pairs are isomorphic. Those are
substantive targets for separate statement and proof units over the
independently published construction. The inverse-power exhaustion,
its converse universal characterization, and the corollary when
`iota a` is surjective likewise remain separate.

The general possibly noncommutative and nonunital B-action extension,
categorical packaging, localization exactness, and the final C.II
finite-localization proposition are also outside this definition unit.
Constructing this quotient does not establish the complete source lemma
or the whole-book objective.
