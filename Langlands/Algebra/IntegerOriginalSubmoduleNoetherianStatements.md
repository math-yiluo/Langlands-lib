# Noetherian criteria for the original nonunital action

Worker 709 prepared this internal statement family in namespace
`Langlands.Algebra.IntegerOriginalSubmoduleNoetherian`. Each declaration
is a closed transparent `def` returning `Prop`. The file proves none of
the comparisons.

The inputs, bound internally in each component, are `A : Type uA`,
`M : Type uM`, `[NonUnitalRing A]`, `[AddCommGroup M]` and the original
`[NonUnitalModule A M]`. The universes `uA` and `uM` are independent and
occur in that order. Associativity of the ring and action is part of
these structures. Commutativity of the ring, a unit law, nondegeneracy,
nontriviality, a field, finite dimension, finite generation, countability
and Noetherianity are not hypotheses. Zero carriers and zero actions
are allowed.

Write `rho = NonUnitalModule.toIntLinearEndHom (A := A) (V := M)`.
The integer actions on the ring and carrier are their canonical additive
group actions. In each occurrence of `IsNoetherian (Unitization Int A) M`,
the statement selects exactly `CompatibleUnitization.module rho` with a
local `letI`. Thus `(z, a)` acts on the same carrier by the sum of the
integer multiple `z • m` and the original action `a • m`. There is no
arbitrary module binder. If the original ring is `Int` acting by zero,
its action is still zero, while the added integer coordinate acts by
the canonical integer action.

The right sides use actual `NonUnitalSubmodule A M` for that same original
action instance. Its elements are additive subgroups closed under the
original action. Its partial order is inclusion of the actual subsets
of `M`, and `<` is proper inclusion. The published
`NonUnitalSubmodule.intUnitizedOrderIso` identifies these subgroups with
submodules for exactly the local unitized action above, preserving
the underlying subsets. The statement file imports this public
construction unchanged.

`ACCStatement` says that ordinary Mathlib Noetherianity of this precise
unitized module is equivalent to
`WellFoundedGT (NonUnitalSubmodule A M)`. This means well-founded strict
reverse inclusion: there is no infinite strictly increasing sequence
of original stable additive subgroups.

`MaximalStatement` has the same left side and the explicit right side

```text
∀ s : Set (NonUnitalSubmodule A M), s.Nonempty →
  ∃ S ∈ s, ∀ T ∈ s, ¬ S < T
```

Every nonempty subset of the actual subgroup poset therefore has a
maximal member. Maximality is within that subset and concerns proper
inclusion, without asserting that this member is a greatest element.

`ChainStatement` has the same left side and the explicit right side

```text
∀ c : ℕ →o NonUnitalSubmodule A M,
  ∃ n, ∀ m, n ≤ m → c n = c m
```

Here `c` is an actual order homomorphism from the natural numbers,
so the sequence is increasing. The conclusion says it is constant
from some index onward. This component quantifies over natural-indexed
increasing sequences; it introduces no categorical chain or union.

`IntegerOriginalSubmoduleNoetherianStatement` is exactly the conjunction
`ACCStatement.{uA, uM} ∧ MaximalStatement.{uA, uM} ∧
ChainStatement.{uA, uM}`, in that order. Every input is bound in each
component; the aggregate has only its two universe parameters.

The provenance is internal derived content. Renard states none of these
three equivalences in this form: they are internal adapters between
Mathlib's module Noetherianity for the integer unitization and the
concrete original-action subgroup poset. The intended later proof
transfers Mathlib's `isNoetherian_iff` through the published actual
order isomorphism and uses the standard well-founded-order
maximal-element and increasing-sequence characterizations.
This is a proof route, not a proof supplied by the statement file.

The source motivation is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The conventions at printed pages 5–6 / PDF pages 11–12 permit rings
and actions without unit laws. I.2.1, printed page 14 / PDF page 20,
distinguishes additive module morphisms from complex-linear ones and
uses complex unitization. Worker 709 read those original passages
in the parent audit. The present integer construction is an internal
choice that makes all additive subgroups automatically scalar stable;
it is not a translation of the book's complex unitization.

A.I.2–A.I.3, printed pages 248–249 / PDF pages 254–255, were reread
and visually checked for this unit. They define ordered categorical
subobjects and Noetherian objects by a maximal-element condition,
discuss chains and increasing sequences, and give the unital-module
example. The present statements use the concrete original-action
subgroup poset. They do not identify it with categorical subobjects
of a category of nonunital modules. The source wording repairs explained
in `Langlands/CategoryTheory/RenardFiniteType.md` include the maximality
sentence and finite-type conventions. That file was consulted; its
repairs do not change this internal proper-inclusion formulation.
The note `notes/renard/appendix-a-corrections.md` was also consulted;
its three discrepancies concern other Appendix A passages. No dedicated
project errata file for the 2026 source was found. Renard's cited
bibliographic sources [25] and [37] have not been read for this unit
and supply no proof evidence. When preparing this submission, Worker 1088
verified the SHA256 of the retained file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`
and independently reread the extracted text of PDF pages 11–12, 20–21
and 254–255; that reread found no conflict with the descriptions above.

The registered supplementary `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF pages 18–19 in the parent audit. It concerns an older
edition and supplies no author-issued correction for these internal
targets.

These statements compare ordinary module Noetherianity with a concrete
poset condition. They make no comparison with Renard's categorical
finite-type predicates, construct no category or categorical
subobject equivalence, and select no convention for a possibly
nonunital Noetherian algebra. They also assert no finite-generation
comparison, localization result, full C.II proposition or whole-book
completion. Those remain separate parent obligations. An exact-target
proof successor must wait until this statement aggregate is
independently accepted and public.
