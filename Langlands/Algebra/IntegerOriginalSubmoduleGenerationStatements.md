# Finite stable generation for the original nonunital action

Worker 709 prepared these internal comparison statements in namespace
`Langlands.Algebra.IntegerOriginalSubmoduleGeneration`; Worker 803 checked
them and clarified this Markdown. The file contains three closed transparent
`def`s returning `Prop` and their ordered conjunction. It proves none of them.

## Inputs and the selected action

Each component internally binds an arbitrary possibly noncommutative
`NonUnitalRing A` with `A : Type uA`, an `AddCommGroup M` with
`M : Type uM`, and the original `NonUnitalModule A M`. The ring and carrier
have independent universe parameters `uA, uM`, in that order; the
definitions take no other parameters. Associativity and distributivity of
the original action are part of `NonUnitalModule`; no unit law is.

Integer scalar actions on `A` and on `M` are the canonical actions of the
additive groups. Write `rho` for
`NonUnitalModule.toIntLinearEndHom (A := A) (V := M)`, the original action
viewed as a nonunital integer-algebra map `A →ₙₐ[ℤ] Module.End ℤ M`. On the
left side of each component the unitized module is exactly the locally
selected `CompatibleUnitization.module rho`, installed with `letI`. Thus an
element `(z, a)` of `Unitization ℤ A` acts on the same carrier `M` by
`z • m + a • m`: the canonical integer multiple plus the original action.
No unitized module, action homomorphism or action equation is an input,
and no global instance is introduced. If the original ring is `ℤ` acting by
zero, its element `1` still acts by zero, while the adjoined unit acts as
the identity.

## Subgroups, order and correspondence

Every subgroup on a right side is the actual `NonUnitalSubmodule A M` for
that same original action instance: an additive subgroup of `M` closed under
the original action. `(↑S : Set M) ⊆ P` is inclusion into the underlying
subset of `P`, and `P ≤ Q` is inclusion of underlying subsets. Integer
multiples stay inside such a subgroup by additivity, so no separate integer
stability is required. The original action instance is retained both in
these subgroup types and in `rho`; there is no replacement action,
subgroup structure or categorical construction.

The published `NonUnitalSubmodule.intUnitizedOrderIso` (module
`Langlands.Algebra.IntegerNonUnitalSubmodule`, imported unchanged) is an
order isomorphism from these subgroups to the submodules of exactly the
selected unitized module. It keeps the carrier subset unchanged in both
directions.

## The three components

`SubmoduleGenerationStatement` quantifies over every original stable
additive subgroup `P`. Its left side is ordinary Mathlib finite generation
`.FG` of the actual submodule `NonUnitalSubmodule.intUnitizedOrderIso P` of
the selected unitized module. Its right side asks for a finite set
`S : Finset M` contained in `P` such that every original stable additive
subgroup `Q` containing `S` also contains `P`. Thus `P` is the smallest
original stable additive subgroup containing those generators.

`ModuleGenerationStatement` compares ordinary
`Module.Finite (Unitization ℤ A) M` for the same selected module with the
existence of a finite set `S` such that every original stable additive
subgroup `P` containing `S` contains every element `m : M`. The conclusion
`∀ m : M, m ∈ P` describes the whole carrier directly and needs no top
element of the original subgroup type.

`NoetherianGenerationStatement` compares ordinary
`IsNoetherian (Unitization ℤ A) M` for the selected module with the
right side of the first component for every original stable additive
subgroup `P`: for each `P` there is a finite set `S` contained in `P` such
that every original stable additive subgroup `Q` containing `S` contains
`P`. The finite set may depend on `P`.

`IntegerOriginalSubmoduleGenerationStatement` is exactly
`SubmoduleGenerationStatement.{uA, uM} ∧ ModuleGenerationStatement.{uA, uM} ∧
NoetherianGenerationStatement.{uA, uM}`, in that order.

All three are equivalences without a finiteness or Noetherian premise. A
generating `Finset` may be empty. Zero carriers, zero rings and zero
original actions are allowed. There is no hypothesis of unit law,
nondegeneracy, nontriviality, commutativity, field or complex structure,
finite dimension or countability.

The generators close under addition, negation and zero as well as the
original action. Nothing here says anything about generation by
multiplication alone.

## Provenance and the supplied-action targets

These statements are internal derived content. An intended proof transfers
the universal property of `Submodule.span` through
`NonUnitalSubmodule.intUnitizedOrderIso`. In Mathlib, `.FG` means equal to
the span of some `Finset`, `Module.Finite` means `⊤` is `.FG`, and
`IsNoetherian` means every submodule is `.FG`. This is a proof route, not a
proof supplied here.

The published `AdditiveUnitizationGenerationStatements` targets do not
already state this specialization. They bind an arbitrary supplied
`Module (Unitization ℤ A) M`, an additive representation
`ρ : A →ₙ+* AddMonoid.End M` and an action-formula hypothesis. Their
subgroups are plain `AddSubgroup M` values with a separately stated stability
predicate. Their first component quantifies over submodules of the
supplied module, and the second asks for `P = ⊤`. Reaching the present
targets from them still requires choosing the action and module, proving
the action formula for the selected module, and translating between those
predicated additive subgroups and the actual `NonUnitalSubmodule A M` type
through the correspondence above. The present targets instead name the
canonical module of the original action and the original subgroup type
directly.

## Source and its limits

The motivating original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
In the parent audit Worker 709 read the conventions at printed pp.5–6 /
PDF11–12, I.2.1 at printed p.14 / PDF20–21, and A.I.2–A.I.3 at printed
pp.248–249 / PDF254–255, including a visual check of the latter. For this
submission Worker 803 verified the SHA256 of the retained file and reread
the extracted text of PDF11–12, 20–21, 254–255, 282 and 285. That reread
found no conflict with the descriptions below.

- The conventions (PDF12) do not assume rings unital, nor modules over a
  unital ring unital, and write `M(A)` for unital modules.
- I.2.1 (PDF20) adjoins a complex unit, `Ã = A ⊕ ℂ·1_A`, to a nonunital
  complex algebra. It distinguishes additive `A`-module maps from those
  that are also complex-linear.
- A.I.2–A.I.3 (PDF254–255) define ordered categorical subobjects, and
  Noetherian and finite-type objects. They give the example that finite
  type in `M(A)` over a unital ring is algebraic finite generation.
- The final C.II proposition (printed p.279 / PDF285) concerns a
  Noetherian commutative complex algebra `B` and finite-type `B`-modules.
  Since rings are not assumed unital, the meaning of these conditions for
  a possibly nonunital `B` is a source convention that remains open.

Renard does not state these integer comparison targets in this form. The
integer unitization is an internal choice that makes every additive
subgroup automatically scalar-stable. It is not a translation of the
book's complex unitization. No identification with categorical subobjects,
Renard's categorical finite-type or Noetherian predicates, or the source's
convention for a possibly nonunital Noetherian algebra is claimed.

The source wording repairs and boundaries recorded in the published
`Langlands/CategoryTheory/RenardFiniteType.md` are retained. The parent
audit consulted `notes/renard/appendix-a-corrections.md`, which addresses
other Appendix A passages; no dedicated project errata file for the 2026
source was found. The registered older-edition supplement
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read only at PDF18–19 and supplies no author-issued correction for
these internal targets. Bibliography references [25] and [37] have not
been read for this unit and supply no proof evidence.

Categorical transport, source convention comparisons, full C.II and the
rest of the book remain parent obligations. A proof successor must name
the exact aggregate after independent statement acceptance and current
Library publication.
