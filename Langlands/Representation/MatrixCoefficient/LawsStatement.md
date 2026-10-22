# Matrix-coefficient translation, naturality, and smoothness

`Langlands.MatrixCoefficientLawsStatement` is one proposition with four explicit
clauses. It is not a placeholder theorem.

1. For `c(ell,v)(g) = ell(rho(g)v)`, right multiplication gives
   `c(ell,v)(g h) = c(ell,rho(h)v)(g)`, and left multiplication gives
   `c(ell,v)(h g) = c(rho.dual(h⁻¹)ell,v)(g)`.
2. For an intertwiner `f : rho → sigma`,
   `c_sigma(ell,f(v)) = c_rho(dualIntertwining(f)(ell),v)` as functions.
3. If the functional is smooth for the algebraic-dual action and the vector is
   smooth for the original action, there is one open subgroup `K` such that
   `c(ell,v)(k g l) = c(ell,v)(g)` for all `k,l ∈ K` and every `g`.
4. On a topological group, a smooth vector gives a locally constant coefficient
   against any algebraic functional. Smoothness of the functional is not needed
   for this last clause.

The algebraic clauses require only a commutative coefficient ring, a group, and
modules, with independent carrier universes. Clause 3 universally quantifies a
topology on the group; it does not need continuity of group operations.
Clause 4 quantifies both the topology and `IsTopologicalGroup G` internally.
No topology on the coefficients or modules, compactness, admissibility,
finite dimension, or Noetherian hypothesis is assumed.

## Provenance and dependencies

Casselman, Chapter II, Section 7, page 10, first paragraph, supplies the
coefficient formula, uniform smoothness assertion, and the right-action
equivariance convention. The original was read. Its smooth dual has the
inverse-action convention in Chapter II, Section 3. Here that convention is
Mathlib's `rho.dual g ell = ell ∘ rho(g⁻¹)`.
The formulas are internally derived directly from these definitions.
Uniform invariance follows by intersecting open fixing subgroups; local
constancy follows from the open coset fixing the vector. These arguments
justify the weaker hypotheses above. This target does not assert Casselman
Proposition II.7.1 or any identification of cuspidality with support conditions.

- Literature ID: `casselman-2019-smooth-representations`.
- Original SHA256: `2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`.
- Edition: June 16, 2019. Locator: Chapter II, Section 7, page 10, first paragraph;
  Section 3, page 6, definition of the contragredient.
- The original path is recorded in [Definitions.md](Definitions.md).

This target imports the accepted matrix-coefficient definition
`5352a743-a6a8-4824-b91e-1cbc32b79b30` version 1, published at commit
`12dbb4572150a088d7f1df3eb9f5b771cb71604c`.
Its other project imports are accepted algebraic-dual definitions
`079d7c1a-8b96-4917-997a-536d6954d55b` version 1 and smoothness definitions
`665022df-625b-44ae-9dbd-425f6e266bab` version 1. Local constancy uses pinned
Mathlib's `Topology.LocallyConstant.Basic`.
The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1,
Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

This statement was authored by Worker 0. It defines the target proposition;
it does not claim that the laws have been accepted as theorems. The adjacent
draft proof and all its helper lemmas form one proof contribution, which
requires a separately bound accepted statement before proof submission.
