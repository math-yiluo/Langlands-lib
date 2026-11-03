# The simultaneous basis and the existing Jacquet contraction input

`Langlands.BruhatTits.SpecialCompact.SimultaneousBasisJacquetAdapterStatement`
is a Prop-valued adapter target. It specializes the published
`Langlands.Jacquet.HasIwahoriContractionBasis` to the same actual standard
subgroups used by `SimultaneousStandardBasisAt`. It supplies no proof of
either the simultaneous structural theorem or this implication.

The hypotheses fix an arbitrary nonarchimedean local field, an actual
connected reductive group scheme, a maximal split torus inclusion `i`, and
a generic cocharacter `ν`. Both characteristics and all ranks are retained.
For any subgroup `K0`, the simultaneous property is an explicit premise.
This implication does not assert that arbitrary `K0` has that property; the
structural target must supply it for the shared geometric compact stabilizer.
The canonical topology is explicitly `rationalPointTopology F G.X`. The
topologies on all subgroup types are its induced topologies.

For every `J ⊆ simpleRelativeRoots i ν`, the conclusion is the existing
Jacquet predicate for `N_J(F)`, `M_J(F)` and the actual opposite standard
radical. In particular, every open subgroup `L` of `M_J(F)` must admit a
compact open subgroup `K` of `G(F)` with the literal intersection
`K.comap M_J.subtype ≤ L`, and an actual element `g` of `G(F)` satisfying
`IsIwahoriContraction K N_J M_J Nbar_J g`. Its `mem_levi` field places `g`
in `M_J(F)`. Its remaining fields require the actual ordered factorization,
the two radical contraction inclusions, the inverse Levi inclusion,
pointwise entry into `K` under positive powers, and uniform opposite
contraction into every ambient open subgroup. No independently chosen
factorization map or alternative topology is used.

The adapter is derived packaging of Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.5.2(ii)–(iv), printed123/PDF129, registered as
`renard-2026-representations-groupes-reductifs-padiques`. It introduces no
second generic contraction predicate and does not duplicate the separate
compact-subset-containment statement or its S22-to-Jacquet consumer.

## Retained proof obligations

The intended proof first uses the inherited identity-neighborhood basis
to choose a member whose Levi intersection lies in `L`. The common
character chambers and compatible algebraic split component must then
supply an actual strictly contracting element. Nonemptiness of that strict
chamber is a root and character statement; it is not a consequence of
merely defining the chamber, and it is not proved in this module. The
maximal splitness and genericity hypotheses are retained for this step.

For that element, the simultaneous property's actual multiplication
bijection gives the factor field. Its normalization and weak-contraction
clauses give the three conjugation fields. Exhaustion gives the pointwise
entry field. The opposite power neighborhood basis gives uniform
containment in the intersection of any ambient open subgroup with the
opposite radical, which is the `contract` field.

The existing
`Langlands.Jacquet.IsIwahoriContraction.eventually_mem` upgrades pointwise
entry to entry for every sufficiently large exponent once the actual
standard-Levi normalization
`M_J(F) ≤ Subgroup.normalizer N_J(F)` is supplied. That algebraic
normalization and its actual-group specialization remain part of the
standard-parabolic proof obligations; the adapter's conclusion is exactly
the published Jacquet predicate. No eventual-entry proof, Jacquet
exactness, admissibility, or canonical-section theorem is claimed here.
