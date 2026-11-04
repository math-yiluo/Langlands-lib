# Conditional assembly of the rational Howe implication

`Langlands.SmoothRep.rationalHoweAssembly` proves exactly
`Langlands.SmoothRep.RationalHoweAssemblyStatement.{u, v}`. This is an internal
composition of published interfaces. Its conclusion is the existing
`RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement.{u, v}`,
under the seven prerequisites retained in the assembly statement:
standard cocharacters, standard Levi intersections, relative root systems,
standard Levi split components, joint special compact basis existence,
cuspidal compact coefficients on the common norm kernel, and finite semisimple
norm-kernel restriction for every irreducible smooth complex representation.
The last two prerequisites are at carrier universe `max (u + 1) v`.
Their proofs remain separate obligations.

The proof accepts an arbitrary field, connected reductive group scheme and
smooth complex representation from the final target. It installs the canonical
rational-point topology and its local compactness, separation and
nonarchimedean group instances. It lifts the representation to carrier universe
`max (u + 1) v`, preserving actual group-algebra finite generation and
admissibility. This matches the universe of the published cuspidal Jacquet
subquotient theorem.

After choosing a maximal split torus and a generic cocharacter, the joint
geometric premise supplies one special compact subgroup `K0`, its Iwasawa
products and its simultaneous basis. `commonBasisFixedGenerators` chooses one
member `K` of that basis which fixes a finite generating family. Thus the
`K`-fixed vectors generate the lifted representation. The basis properties make
`K` compact and open and normal in `K0`; admissibility makes its fixed space
finite-dimensional.

To apply `compactOpenDetectionConsequences`, the proof considers each
irreducible actual subquotient `D`. Irreducibility makes `D` nonzero, so
`exists_irreducible_cuspidal_jacquet_subquotient` supplies an actual standard
Levi and an irreducible cuspidal subquotient `E` of the normalized Jacquet
module. The standard Levi split-component premise supplies connected
reductivity of this Levi representative; the remaining clauses of that premise
are not needed here.

The two internal coefficient lemmas provide the coefficient input for `E`.
`compactCoefficients_of_jointBasis` specializes the joint geometric premise to
the group being considered, obtains the positive Cartan cover at its same
special compact subgroup, and applies the explicit cuspidal compact-restriction
premise. `leviCompactCoefficients_of_jointBasis` applies this argument to the
actual Levi and its torus factor. The published standard-family comparison
gives inherited genericity, the relative-root-system premise supplies the
intrinsic root labels, and cuspidality transport identifies all the proper
normalized Jacquet tests. The resulting coefficients are compact on the
Levi's intrinsic common norm kernel. This local coefficient argument may use
the Levi's own geometric special compact subgroup.

For ambient detection, the proof retains the previously chosen `K` and `K0`.
The simultaneous basis gives contraction and cofinality for this very `K`.
A strict element from the compatible split component therefore gives its
Iwahori contraction. The original `K0` Iwasawa product and the standard
parabolic decomposition yield the required `m * n * k` factorization. The
standard-cocharacter comparison identifies the literal standard unipotent
subgroup with the dynamic unipotent; the published compact-open containment
theorem then places every finite subset in a compact open subgroup.
`rationalLeviJacquetFixedVectorDetection` combines these data, the fixed-vector
generation, the actual Jacquet subquotient and the intrinsic compact
coefficients. Its finite-restriction premise applies to all irreducibles as
stated, and is used here for the selected cuspidal constituent. It produces a
nonzero `K`-fixed vector in `D`.

The compact-open detection consequence gives finite length of the lifted
representation, and the universe-lift equivalence gives actual group-algebra
finite length of the original representation. The field and representation
universes remain independent. The ambient representation is never assumed
nonzero, so the zero representation is included.

This proof does not discharge any of the seven premises or prove the
unconditional Howe target. The converse, the separate VI.6.3 intermediate
assertions and the stronger compact-open length bound retain their own proof
obligations. No new translation of a literature assertion is claimed.
