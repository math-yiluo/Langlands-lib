# Constituent extraction by induction on fixed-vector dimension

Worker 196 authored the statement draft and induction design. Worker 189
checked the source correspondence and prepared this focused statement pair.

`Langlands.CuspidalSupport.FixedVectorConstituentInduction` is a proposition
statement for the algebraic induction in Bernstein–Zelevinsky,
*Representations of the group GL(n,F) where F is a non-archimedean local field
(survey)* (1976), Proposition 3.30, proof steps (2)–(3), printed/PDF
page 37, and Lemma 2.9(a), printed/PDF page 17. The registered source is
`bernstein-zelevinsky-1976-representations-gln`. This is a derived general
form of the source's Levi-group argument, with the subgroup and generation
properties that its application to actual Levi groups must supply separately.
The retained English translation is in *Russian Mathematical Surveys* 31:3
(1976), pp. 1–68, with SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.

Let `G` be a topological group, `H` a normal subgroup such that the join of
`H` with the center has finite index, and `K` a compact open subgroup contained
in `H`. Let `A` and `D` be actual smooth complex representations, with independent
group and carrier universes. Assume:

- the restriction of `A` to `H` is semisimple;
- the ambient `K`-fixed vectors generate that restriction, meaning that every
  `H`-invariant subspace containing them is the whole space;
- the space of `K`-fixed vectors of `A` is finite dimensional;
- `D` is admissible and irreducible, has a nonzero `K`-fixed vector, and is an
  actual subquotient of `A`.

The proposition asserts that there exist both an actual injective intertwiner
from `D` to `A` and an actual surjective intertwiner from `A` to `D`, expressed
by the existing `SmoothRep.IsSubrepresentation` and `SmoothRep.IsQuotient`
predicates. It does not assume finite dimensionality or full admissibility of
`A`, nor semisimplicity of `A` under `G`. The two existential maps need not be
mutual splittings; the proposition does not assert that their composite is
the identity.

The source's scalar-center case uses semisimplicity over `H`, unchanged upon
adjoining scalar operators, followed by finite-index averaging (BZ76 §2.9(a),
printed/PDF page 17). Its general case uses Schur's lemma for `D` and the
endomorphism `A(z) - chi_D(z) id`. A nonzero shift is detected by the fixed
vectors under the explicit generation assumption. Compact averaging and an
actual subquotient presentation make its fixed-vector action noninjective.
Kernel/image and image/cokernel alternatives then decrease the finite
fixed-vector dimension. Semisimplicity and generation over `H` pass to these
actual subquotients, retaining the same `K`.

These paragraphs explain the intended derivation; this file publishes only
the proposition, with proof separate. In the Levi application, block isolation
and finite-type detection are additional prerequisites supplying `H`, `K`,
and the generation assumption. In particular, step (1) of Proposition 3.30
is outside this statement: the source assumes an admissible ambient Levi
representation with a cuspidal constituent, whereas this derived target
assumes explicitly the subgroup semisimplicity and fixed-vector hypotheses
needed for steps (2)–(3). Finite-type compact-open selection is also a
separate prerequisite. No arbitrary theorem-valued input or
unproved splitting witness occurs in the statement.
