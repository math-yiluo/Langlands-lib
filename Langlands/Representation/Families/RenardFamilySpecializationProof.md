# Renard VI.8.1: admissibility of specialization

Worker 1761 proves the unchanged `SpecializationAdmissibilityStatement`
at independent universes `uB`, `uG`, `uV`. The source is Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026,
VI.8.1 specialization Lemma, printed p.189 / PDF p.195.
Literature ID: `renard-2026-representations-groupes-reductifs-padiques`;
SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The proof uses the actual scalar extension of the original coefficient action.
As an action on the underlying additive group, this is the tensor action with
a trivial first factor. The tensor smoothness lemma therefore proves that
scalar extension preserves smoothness.

For a compact open subgroup `K`, scalar extension of the inclusion of `V^K`
is a linear map from `A ⊗[B] V^K` into the fixed vectors of the scalar-extended
action. Its surjectivity follows from the fixed-tensor comparison over `B`:
the underlying action and inclusion maps are the same. If `V^K` is finite
over `B`, its scalar extension is finite over `A`, and the surjective map
makes the target finite as well. These internal helpers hold for any
commutative scalar-extension algebra `A` over the complex coefficient algebra.

Apply this to `A = ℂ` with the algebra structure defined by the given point
`χ`. This gives finite-dimensional fixed vectors for every compact open `K`.
For any open subgroup `H`, Van Dantzig provides a compact open subgroup
`K` contained in `H`. The `H`-fixed subspace lies inside the finite-dimensional
`K`-fixed subspace, so it is finite-dimensional. Together with smoothness,
this is the published all-open-subgroups definition of admissibility.

The closing theorem retains the published flatness hypothesis, although the
averaging comparison makes it unnecessary for this consequence. The proof
changes no imported statement or definition and adds no hypothesis.
