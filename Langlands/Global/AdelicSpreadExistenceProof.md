# Existence of actual arithmetic spreads in both characteristics

Authors: Worker 208 (complete proof draft); Worker 1601 (verification against
the published prerequisites, explanatory Markdown and submission preparation).

`Langlands.Global.adelicSpreadExistence` proves the unchanged proposition
`Langlands.Global.AdelicSpreadExistenceStatement`, the conjunction of the
function-field and number-field existence assertions.

The proof applies general filtered-ring scheme-model existence to the
actual integer-algebra diagram. To forget its fixed initial integer base,
it composes the equivalence between commutative algebras and commutative
rings under that base with the under-category forgetful functor. The
equivalence preserves colimits, and the latter functor preserves connected
colimits. The filtered indexing category is connected, so the actual
field-valued integer-algebra colimit remains a ring colimit.

A finite-type scheme over this Noetherian colimit ring is locally
Noetherian. Its structure map is locally of finite presentation and
quasi-separated, so together with the given quasi-compactness it satisfies
the general model-existence hypotheses. That theorem produces a scheme
over an actual stage, with locally finitely presented, quasi-compact
structure map, and an actual pullback square.

Forgetting local finite presentation to local finite type gives the
required model finiteness. The inverse of the canonical isomorphism
from the supplied pullback square to the categorical pullback gives an
isomorphism from the actual generic fiber to the original field scheme.
Its compatibility with the second projection makes it an isomorphism
over the original field.

The two arithmetic clauses instantiate this argument with the literal
integer-ring diagrams and their proved field-valued colimits. This
retains arbitrary nonaffine finite-type field schemes, arbitrary perfect
function-field constants with the specified compatible rational-function
action, possibly inseparable rational-function extensions, and every
finite initial place set, including the empty set. The proof introduces
no separatedness or additional quasi-separatedness premise.

The source specialization is Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), printed pp.5–6, Theorem 3.4(1) and its
arithmetic application, as documented in the paired target statement. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The published general model-existence proof and the actual integer-ring
colimit proof are reused through imports. This result asserts existence of spreads; separated models
require the additional eventual-separatedness argument.
