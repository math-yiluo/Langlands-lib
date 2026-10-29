# Kernel and power exhaustion of actual endomorphism localization

Authors: Worker 709, who read the original passages, wrote the Lean
statements and drafted this Markdown; Worker 900, who rechecked the pair
against the original pages and the construction module and submitted it.

This statement unit uses the actual localization and canonical map from
`Langlands.Algebra.RenardEndomorphismLocalization`. It specifies their kernel,
the injectivity implication, and exhaustion by inverse powers of the localized
operator. It contains proposition definitions, not proofs of these assertions.
All declarations are in `Langlands.Renard.EndomorphismLocalization`.

## Original source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, A.III.1, lemma (i)–(ii) after example 5, printed253/PDF259.
Example 5 and the localization convention are on printed252/PDF258.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`;
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Original:
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF258–259 were read, and PDF259 was visually inspected.

The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked on PDF17–19. No entry for this lemma was found in those pages.
That limited check does not make the 2010 edition a governing source.
The public notes `notes/renard/appendix-a-corrections.md` and
`notes/renard/stable-quotients.md` record the related source discrepancies
and the remaining quotient and finite-localization obligations.

The source works over a field k. Part (i) asserts that injectivity of a
implies injectivity of the canonical map. Part (ii) forms the increasing union
K of the kernels of powers, induces an injective operator on L/K, compares
the two localizations, and then identifies the localization of L/K with the
union of inverse-power images of L/K. Its proof explicitly establishes
K contained in the kernel of the canonical map.

The converse kernel inclusion, the exact kernel criterion, the submodule
supremum formulation, and exhaustion using the canonical image of the
original L are internal derived formulations. They are consistent with the
source's quotient comparison but do not assume that comparison. They can
instead be proved directly from the published equality and representation
formulas for actual fractions. Extending these assertions from fields to
commutative unital rings is also internal; it is not attributed to Renard.

## Objects and hypotheses

Let `R : Type u` with `[CommRing R]`, `V : Type v` with `[AddCommGroup V]`
and `[Module R V]`, and `a : Module.End R V`. The universes u and v are
independent. The imported construction provides:

| Mathematical object | Published Lean declaration |
| --- | --- |
| Evaluation module, with X acting by a | `EvalModule a` |
| Actual localization at powers of X | `Localized a` |
| Canonical map V to the localization | `iota a : V →ₗ[R] Localized a` |
| Localized operator | `localizedEnd a` |
| Its actual inverse endomorphism | `localizedInv a` |
| Invertible localized operator as an equivalence | `localizedEquiv a` |

`Localized a` lives in `Type (max u v)`. There is no universe shrinking,
`Small` hypothesis or new carrier. The targets permit zero rings, zero
modules, and zero or nilpotent a. They assume no finite dimension, finite
generation, Noetherianity, injectivity or nontriviality except for the
explicit antecedent of `InjectivityStatement`.

The symbol `a ^ n` is a power in the endomorphism ring and hence composition;
n = 0 gives the identity. `localizedInv a ^ n` is likewise an endomorphism
power, not a scalar inverse. It is defined by the imported construction.

## Exact targets

- `KernelCriterionStatement.{u,v}` quantifies over R, V, a and `z : V`,
  asserting `iota a z = 0 ↔ ∃ n : ℕ, (a ^ n) z = 0`.
  It identifies the elements killed by localization, including z = 0.
- `KernelUnionStatement.{u,v}` quantifies over R, V and a, asserting the
  equality of actual R-submodules
  `LinearMap.ker (iota a) = ⨆ n : ℕ, LinearMap.ker (a ^ n)`.
  The kernels increase with n, so their supremum is their set union.
  This order-theoretic explanation does not supply a proof in this unit.
  Including n = 0 changes no union, because the identity has zero kernel.
- `InjectivityStatement.{u,v}` quantifies over R, V and a, asserting
  `Function.Injective a → Function.Injective (iota a)`.
  The field case is precisely source lemma (i).
- `PowerExhaustionStatement.{u,v}` quantifies over R, V and a, asserting
  the literal equality of sets in the actual `Localized a`:

  ```lean
  (⋃ n : ℕ, Set.range ((localizedInv a ^ n).comp (iota a))) =
    (Set.univ : Set (Localized a))
  ```

  Thus every localized element is `(localizedInv a ^ n) (iota a z)`
  for some n and z. The use of the image of `iota a` does not presume
  that the original V embeds. This is a union of ranges as sets, not
  merely the submodule generated by them.

`KernelExhaustionStatement.{u,v}` is the ordered conjunction of these four
closed statements over commutative unital rings. `FieldKernelExhaustionStatement.{u,v}`
binds an arbitrary field k and V internally and states the same four
clauses for every a. It records the field specialization without a
characteristic or dimension restriction. It retains the derived clauses
as derived, rather than presenting the entire conjunction as a verbatim
source lemma.

`KernelExhaustionStatements.{u,v}` is the complete proof target: the
conjunction of `KernelExhaustionStatement` and
`FieldKernelExhaustionStatement`. Every statement is a `def` returning
`Prop`. The closed aggregate introduces no unnamed section parameters.

## Proof route and retained obligations

The published `frac_eq_frac_iff`, applied at denominator exponent zero with a zero
numerator, gives the kernel criterion. Increasing power kernels translate
it into the submodule equality. Injectivity of a implies injectivity of
every power, which gives injectivity of the canonical map.
`frac_surjective` and `frac_eq_localizedInv_pow` give the literal
exhaustion. These are proposed proof routes, not completed proofs.

Separate units retain the stability of K and actual induced quotient
operator, its injectivity, the localization comparison for V/K,
the converse universal characterization of extensions exhausted by
inverse powers, and the source corollary when the canonical map is
surjective. The general possibly noncommutative and nonunital B-action
extension, categorical packaging, localization exactness and the final
C.II finite-localization proposition also remain separate. This unit
does not claim coverage of all of lemma (ii) or of the corollary.

Development checks `1d05c129-3bd6-416d-8467-19dbca1da271` and, on the
submitted Lean file, `59030112-ac8e-4387-9290-8c8d8be87fe3` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the entry module without
diagnostics. They inspected the complete aggregate as a definition
returning `Prop`, with universe parameters u and v and only `propext`,
`Classical.choice` and `Quot.sound`. These checks are neither independent
semantic acceptance nor proofs of the targets.
