# Central dual eigenfunctionals give irreducible admissible scalar quotients

Worker 189 prepared this proof and explanation, reusing the proof route and
privately checked wrapper supplied by Worker 261.

The module proves
`Langlands.centralDualEigenQuotient.{uG,uC,uV} :
Langlands.CentralDualEigenQuotientStatement.{uG,uC,uV}`.
The theorem is closed and preserves the three independent universes of the
published statement: the ambient group, central parameter group and
representation carrier respectively.

For a topological group `G` in which every open subgroup contains a compact
open subgroup, consider a central homomorphism `z : C →* G`, a character
`χ : C →* ℂˣ` and a complex representation `ρ` on `V`. Assume that `ρ.asModule`
is finitely generated over `MonoidAlgebra ℂ G`, that `ρ` is admissible, and
that the full algebraic dual contains a nonzero `φ` satisfying
`φ (ρ (z c) v) = (χ c : ℂ) * φ v` for every `c` and `v`.
The conclusion supplies an actual bundled representation `S : Rep.{uV} ℂ G`
that is irreducible and admissible, has scalar character `χ` along `z`,
and receives a surjective intertwining map from `ρ`.

The implemented proof introduces all the statement's quantified objects,
instances and hypotheses, then unpacks the existential antecedent as
`⟨φ, hφ, heig⟩`. It applies the published theorem
`Langlands.MaximalConeQuotient.exists_irreducible_quotient` from
`Langlands.Representation.Classification.MaximalConeQuotient` to those same
objects and hypotheses. That theorem already returns exactly the required
representation, irreducibility, admissibility, scalar character and surjective
intertwiner. This wrapper performs no additional quotient construction and
changes neither the eigen-equation nor the character.

The hypotheses are exactly those in the published statement. In particular,
the parameter group `C` has no topology requirement, the functional belongs to
the full algebraic dual, and no finite length or semisimplicity assumption is
introduced. The quotient carrier remains in universe `uV`.

This is a derived generic algebraic and admissibility prerequisite. It packages
an existing Library theorem for downstream dual-exponent arguments; it is not
a literature theorem or a transcription of a numbered result. Its mathematical
input is the imported generic extraction theorem, whose own implementation
and provenance are documented in its paired module. This proof does not
establish a GL specialization or an analytic support theorem.
