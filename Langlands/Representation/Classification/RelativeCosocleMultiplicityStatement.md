# Relative cosocle multiplicities

This pair states the GL_n specialization of Silberger 1978, Proposition 5.9.
It is a proposition definition, not a proof. It compares multiplicities in
the actual canonical radical quotients of two normalized induced
representations, using the existing `Classification.head` construction.

## Data and scope

The fine and middle data are those fixed on the source's p.99 and used in
`RelativeRecoveryStatement`. A positive-rank p-adic general linear group has
coarse block shape `B`, middle shape `D = B.flatten Q`, and fine shape
`C = D.flatten R`. The direct refinement `S` and actual shape equality
`C = B.flatten S` identify the same fine blocks inside the coarse Levi.
The equality transports the fine representation and parameter. Other
coordinate transports use the constructed flattened-Levi equivalence.

The fine representation `ω` is irreducible, cuspidal and unitarizable.
Cuspidality includes admissibility and vanishing of actual proper-refinement
coinvariants. The parameter `v₀` is a strictly positive combination of the
adjacent scalar roots inside each middle block, whose determinant-exponent
coordinates are `e_j/d_j - e_(j+1)/d_(j+1)`. The middle representation `σ`
is irreducible and square-integrable modulo the full middle-Levi center,
and receives an actual surjective intertwiner from the fine-to-middle
normalized induction of `ω |det|^(-v₀)`.

The coarse representation `π` is **any** irreducible tempered representation
of `B.Levi F`. There is no premise that it occurs in either the middle or
fine induction, and no support map to it. The middle datum constrains the
fixed fine data only. Square-integrability and temperedness use the existing
analytic predicates on every Borel Haar measure of the actual central
quotient; existence of those measures is proved in the Library.

For any strictly decreasing coarse vector `t`, the representation `J` is
an arbitrary irreducible target of an actual surjective intertwiner from
the normalized outer induction of `π |det|^t`. The regular-positive
unique-quotient theorem identifies such a target with the source's
`J(π,t)`. The present conditional statement does not assume a chosen
canonical representative, and does not claim quotient existence.
There is no premise that `J` is a quotient of the fine ambient induction.

## The actual quotients and the equality

Write

* `I_in = innerInduced T B S (fineTwist T B S ω v₀ 0)`;
* `I_out = fineAmbientInduced T B S ω v₀ t`.

These are actual normalized inductions from the fine Levi to the coarse
Levi and to the ambient group, respectively. The inner twist has determinant
exponents `-v₀(k)`; the ambient twist has exponents
`-v₀(k) + t(parent(k))`. Upper induction uses right translation and positive
half-modulus covariance, with residue-normalized absolute value
`q^(-valuation)`. Strict decrease is the regular positive chamber, and
allows arbitrary central shifts of `t`.

For a representation `ρ` on `V`, `Classification.headKernel ρ` is the
common kernel of all irreducible surjections with targets in the universe
of `V`. Every maximal invariant subspace has its actual irreducible
quotient in that universe. Thus this kernel is mathematically the invariant
radical. `Classification.head ρ` is the actual representation on
`V ⧸ headKernel ρ`, with its already constructed surjective projection.
The Lean statement uses this quotient directly; it introduces no second
cosocle carrier or arbitrary maximal semisimple quotient witness.

For finite-length representations the radical quotient is the maximal
semisimple quotient, called the maximum completely reducible quotient in
the source. The existing quotient construction and its projection laws
are proved. [The cosocle module](Cosocle.md) proves its general finite-length
semisimplicity, radical comparison, semisimple universal property and
functoriality. Applying finite-length semisimplicity to the potentially
reducible `I_in` and `I_out` still requires the finite-length hypotheses
for those inductions; the multiplicity comparison remains a separate
proof obligation.

`GLRelativeCosocleMultiplicityStatement` supplies a natural number `m`
such that

* `J` has Jordan–Hölder multiplicity `m` in `head I_out`;
* `π` has Jordan–Hölder multiplicity `m` in `head I_in`.

Each predicate supplies an actual finite composition series with exactly
that many factors equivalent to the specified constituent. This is an
existence assertion for both series, not an equivalence between possibly
false series predicates. The number may be zero: imposing positivity
would incorrectly exclude the arbitrary tempered inputs with no inner
support. Neither multiplicity is that in the full induced module.

The field, fine, middle, coarse and quotient carriers have independent
universes `uF`, `uV`, `uM`, `uW`, and `uZ`. Both fine induced carriers and
their head quotients live in `max uF uV`. Actual intertwining maps and
the equivalences in the multiplicity predicates permit different target
universes. The canonical head tests irreducible quotients in its own
carrier universe; its actual radical interpretation explains why this
does not omit maximal invariant subspaces.

## Original source and proof obligations

A. J. Silberger, *The Langlands Quotient Theorem for p-adic Groups*,
Mathematische Annalen **236** (1978), 95–104: the fixed nested support
setup on p.99, Lemma 5.6 on p.101, and Propositions 5.8–5.9 with their
proofs on p.102. The retained original is
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`,
registered as
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Worker 19 read the complete article and reread the p.102 text and formula
image for this pair. No retained erratum was located.

The explicit GL block coordinates, actual radical quotients and quotient
maps make this a derived specialization. The supporting middle datum is
retained from the setup, while the coarse input keeps Proposition 5.9's
arbitrary-tempered scope. Replacing the source's named Langlands quotient
by any irreducible outer quotient uses regular-positive uniqueness.

The printed proof identifies each cosocle multiplicity with a fine
cuspidal multiplicity in an opposite Jacquet module by reciprocity.
For the ambient side that Jacquet module belongs to `J` itself, not to
the entire outer induction of `π`. Establishing the equality therefore
needs the quotient-extraction and comparison steps, as well as finite
length, semisimplicity of the heads, the relevant Schur/Hom multiplicity
identifications, and Jordan–Hölder independence. None is proved by this
statement.

The printed generic step cites Lemma 5.3, whose unrestricted wording has
the [documented scope obstruction](../../../notes/jacquet/silberger-lemma53-scope.md).
One cannot apply the repaired constituent-only generic comparison to the
arbitrary `π` without first establishing the required support. The
arbitrary-tempered reflection of Proposition 5.8 handles the case where
an ambient quotient occurrence must force inner support. The multiplicity
comparison still requires the direct continuation and tempered-exponent
argument referred to in the last line of Proposition 5.9, with the fixed
positive-root datum and regular coarse chamber. A proof must justify
these steps for the arbitrary coarse input; the supported all-regular
comparison alone does not supply any missing middle-support map.

This pair states neither the general cosocle algebra nor its analytic
comparison proof. It does not prove semistandard conjugacy or exhaustive
Langlands classification.
