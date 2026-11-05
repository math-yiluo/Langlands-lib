# Moderate growth of coefficients on actual rational points

This pair states both assertions of J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques d'après Harish-Chandra* (2003), Corollary I.4.4,
printed p.245 / PDF p.11. The matrix norm is the one defined in I.1, printed
p.242 / PDF p.8, computed with the residue-normalized absolute value.

## Actual group and norm

`GroupScheme.MatrixRepresentation.rationalMatrixNorm F ρ g` uses the published
`ρ.rationalMatrix`, whose argument is a literal point of the supplied group
scheme over `Spec F`. It takes the maximum of the absolute values of all entries
of that matrix and its inverse. Its scalar absolute value is the published
`LocalField.residueNormalizedAbsoluteValue F`; the auxiliary `NormedField`
structure occurs only inside this real-valued definition. The representation
and its smooth dual use the original canonical rational-point topology
`rationalPointTopology F G.X`.

The index is a nonempty finite type in the universe accepted by the existing
matrix group-scheme construction. The targets quantify over every supplied
closed algebraic embedding `ρ`. The closed-embedding premise is essential: a
nonfaithful matrix representation need not detect growth in its kernel.
Existence of such an embedding is not part of this pair.

The four elementary norm laws are internal consequences of the published
`rationalMatrix` monoid homomorphism and `HarishChandraSchwartz.glNorm` laws.
The lower bound by one and submultiplicativity use the published ultrametric
inequality for the residue-normalized absolute value. These laws introduce no
coefficient-growth assumption.

## Coefficientwise assertion

`RationalCoefficientModerateGrowthStatement.{u,uV}` quantifies over an arbitrary
nonarchimedean local field `F : Type u`, a connected reductive group scheme `G`,
a supplied closed algebraic embedding, and an admissible smooth complex
representation `π` whose carrier lies in the independent universe `uV`.
For every vector `v` and smooth algebraic-dual functional `φ`, there are a natural
number `d` and a positive real number `c` such that, for every actual point `g`,

`‖φ (π(g) v)‖ ≤ c * rationalMatrixNorm F ρ g ^ d`.

Here `d` and `c` may both depend on `v` and `φ`. Admissibility is the existing
all-open-subgroups predicate, which in particular implies finite dimension of
compact-open fixed spaces. The coefficient uses the usual complex absolute
value and an element of `SmoothDual π.representation`, not an arbitrary
nonsmooth algebraic-dual functional.

## Finite-length assertion

`RationalFiniteLengthModerateGrowthStatement.{u,uV}` adds `π.HasFiniteLength`,
the published finite-composition-length predicate over the complex group
algebra. Its quantifier order is

`∃ d : ℕ, ∀ v φ, ∃ c : ℝ, 0 < c ∧ ∀ g, coefficient_bound`.

Thus the exponent can depend on the representation and chosen embedding, but
is independent of both the vector and functional. The constant may depend on
both. Finite length does not mean that the representation is finite dimensional.

`RationalModerateGrowthStatement` is the conjunction of these two Prop-valued
targets. Neither assertion imposes splitness, quasisplitness, characteristic
zero, irreducibility, unitarity, a central character, a strict Jacquet-exponent
bound, or an additional analytic estimate.

## Source and proof boundary

The first and second assertions reproduce respectively the first paragraph and
finite-length sentence of Corollary I.4.4. Waldspurger proves them using the
Cartan decomposition I.1 (4), Proposition I.4.3, and induction on semisimple
rank, reducing to finite functions on a split torus. This pair supplies targets
for that missing growth prerequisite; it does not prove them.

The source fixes a special compact subgroup and chooses its algebraic embedding
so that the compact subgroup maps into integral matrices. The targets express
the resulting growth property for every closed algebraic embedding. This does
not assert compact invariance for an arbitrary embedding: on an affine algebraic
group, entries of one closed embedding and its inverse are regular functions,
hence polynomial expressions in entries and inverse entries of another closed
embedding. Consequently their matrix norms bound each other by a positive
constant times a natural power, and the growth property transfers after
changing the constant and exponent. Proving that comparison in Lean, if needed
by the chosen route, remains a proof obligation.

This pair does not prove convergence or rationality of standard intertwining
integrals. Those conclusions remain in
`ConditionalParabolicIntertwiningStatement` with its unchanged structural
telescope. The elementary norm laws and the statement of I.4.4 do not discharge
that theorem.
