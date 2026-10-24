# Applying constituent induction to a finite family of types

Author: Worker 196. This is an ancillary application lemma for the final
cuspidal constituent proof. It combines the finite-type compact-open selection
with the fixed-vector induction, following the choice in Bernstein–Zelevinsky
(1976), Proposition 3.30, proof steps (2)–(3), printed/PDF page 37, registered
source `bernstein-zelevinsky-1976-representations-gln`.

The ambient group is a locally compact nonarchimedean topological group. The
open normal subgroup `H` joined with the center has finite index. The smooth
complex representation `A` is admissible and semisimple on restriction to
`H`; `D` is admissible, irreducible, and an actual subquotient of `A`. A finite
family of nonzero subrepresentations of `D` restricted to `H` supplies actual
equivalences to every simple subrepresentation of `A` restricted to `H`.
The group, carrier and finite-indexing-type universes are independent.
The conclusion is both an actual embedding of `D` in `A` and an actual
surjection from `A` to `D`.

Irreducibility first gives a nonzero vector of `D`. Smoothness gives an open
subgroup fixing it. The finite-type selection lemma chooses one compact open
subgroup `K` contained in that stabilizer and in `H`, fixing a nonzero vector
in each listed type. Thus `D` has a nonzero `K`-fixed vector. Actual
equivalences transfer the selected type vectors into every simple
subrepresentation of `A` restricted to `H`. Semisimplicity then implies that
the ambient `K`-fixed vectors generate the entire `H`-representation, via
`eq_top_of_fixedVectors_le_of_semisimple`.

Admissibility supplies finite dimension of `A`'s `K`-fixed space. All the
concrete hypotheses of `fixedVectorConstituentInduction` are now available,
so it supplies the two maps. No finite dimension of `A` or additional
splitting hypothesis is assumed. The finite-type selection and induction
theorems are imported from the published Library. This ancillary pair is
used by `ConstituentProof` to prove the full actual-Levi theorem.
