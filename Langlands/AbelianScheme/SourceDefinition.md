# Equivalence with the source definition of an abelian scheme

Author: Worker 129.

`Langlands.AbelianScheme.SourceDefinitionEquivalence` is a proposition, not a
proved theorem. For every scheme `S` and every group object `G` in `Over S`,
it states that `G` is smooth and proper over `S` with geometrically connected
fibres if and only if there is an `AbelianScheme S` whose underlying group
object is exactly `G`. There is no noetherian, connectedness, characteristic,
or fixed relative-dimension assumption on the base.

The left side is `GroupScheme.IsAbelian G`, the three geometric predicates
from `Basic`. The right side uses the bundle from that module, which also
requires `IsCommMonObj G.X`. The equality `A.toGrp = G` keeps the given group
object, including its group law, rather than merely asserting that an unrelated
abelian scheme exists. Thus the nontrivial direction requires commutativity of
every group scheme satisfying the source's geometric definition. The reverse
direction follows by forgetting explicit commutativity, as already expressed
by `AbelianScheme.isAbelian`.

The source definition over an arbitrary base is Lan, *Arithmetic
compactifications of PEL-type Shimura varieties* (2008 thesis),
Definition 1.3.1.1, printed p.103 (PDF p.143). Corollary 1.3.1.7, printed
p.108 (PDF p.148), proves commutativity using the preceding rigidity
corollary. Corollary 1.3.1.6 explicitly reduces to the locally noetherian
case using Theorem 1.3.1.3. This supplies the arbitrary-base scope needed here.

The original GIT counterpart is Mumford--Fogarty--Kirwan, *Geometric
Invariant Theory*, third edition, Chapter 6: Definition 6.1, printed p.115
(PDF p.128), and Corollary 6.5, printed p.117 (PDF p.130). The chapter
restricts to locally noetherian schemes, and Definition 6.1 states a
noetherian base. Consequently GIT alone is not used to justify the
arbitrary-base quantifier.

The existential formulation is an internal packaging of the cited
commutativity result and source definition, chosen to express precisely the
relationship with the explicit-commutativity bundle. The cited literature
does not use Lean bundles or this equality formulation. This module adds no
axiom, construction of a commutativity witness, or proof of the proposition.
A separate proof task is required after publication of this statement.

Sources read directly for this statement:

- `lan-2008-arithmetic-compactifications-pel-thesis`, SHA256
  `c3086d5140bab887e31a508cf4bf8804f092326a35882fc003a3422c4ab65bdd`,
  PDF pp.143 and 148, with the intervening noetherian-reduction discussion
  previously read for `Basic`.
- `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
  SHA256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`,
  PDF pp.128 and 130.
