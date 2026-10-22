# Comparing the cuspidality predicates

This pair states two comparisons needed to use the product-Levi cuspidal
support statements with the existing GL classification objects. It adds
Prop-valued theorem targets; it does not prove either comparison or change
any definition of cuspidality.

## Objects and scope

The aggregate `Langlands.CuspidalSupport.PadicCuspidalityComparisonTheorems`
quantifies over every prime, every actual finite extension `F` of the p-adic
field, every compatible `F.TopologicalData`, and every positive rank `n`.
The coefficient field is complex. The field and representation-carrier
universes are independent, and the carrier is not restricted to finite
dimension. No irreducibility or unitarity hypothesis is imposed.

`GeneralLinear.IsSupercuspidal` already means admissibility together with
vanishing of actual unipotent coinvariant quotients for all proper ordered
block parabolics and all their conjugates. It does not itself include
irreducibility. `CuspidalSupport.IsLeviCuspidal` already means admissibility
and vanishing for all proper standard block refinements of the product
Levi. Both predicates include smoothness through admissibility.

## Statements

`StandardJacquetSupercuspidalityClause` says that the existing GL
supercuspidality predicate is equivalent to admissibility and vanishing
of the actual Jacquet quotient for every proper standard block parabolic.
The right side does not quantify over conjugating matrices. Properness is
the actual subgroup condition `B.parabolic F.Carrier ≠ ⊤`.
`B.JacquetModule ρ` is the quotient by the span of `ρ(u)v - v` for the
embedded standard unipotent radical. `Subsingleton` of its carrier means
that this quotient is zero. The normalized Jacquet module has the same
carrier; its inverse positive half-modulus changes only the Levi action,
so this test is also the normalized Jacquet-vanishing test of BZ77.

`SingleBlockCuspidalityClause` says that, for every ordered positive block
shape `B` with `B.length = 1`, the actual representation
`ρ.comp (B.leviEmbedding F.Carrier)` of `B.Levi F.Carrier` is Levi cuspidal
if and only if `ρ` is supercuspidal. The block embedding and the pullback
representation are the existing concrete constructions, not arbitrary
isomorphism or transport parameters. The shape still has total rank `n`;
the sole block therefore has that rank. Standard refinements of this
one-block shape are exactly the ordered block parabolics used by the
first clause, after the actual coordinate identifications. The statement
requires that comparison as a conclusion rather than assuming those
identifications or a classification theorem as data.

## Original source and derived formulation

Original source: Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups. I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The relevant original is printed page 446, sections 2.1–2.4 (PDF page 7),
with transport conventions in section 1.7 on printed page 443 (PDF page 4).

Section 2.1 fixes standard parabolic triples and standard subgroups inside
a standard Levi. Section 2.2 realizes GL standard Levis by ordered positive
partitions and their standard subgroups by refinements. Section 2.3 fixes
the normalized Jacquet functors. Section 2.4 defines quasicuspidality by
vanishing for all proper standard subgroups, then defines cuspidality by
adding admissibility. Thus the standard Jacquet test here is the GL
specialization of that definition. The one-block partition realizes the
ambient GL itself, giving the second comparison.

These equivalences are derived interface statements, not separately
numbered theorems in BZ77. The first comparison also uses the elementary
fact that inner conjugation transports unipotent coinvariants by the
actual invertible operator `ρ(g)`, so vanishing for a radical is equivalent
to vanishing for its conjugate. The second uses the actual one-block
matrix embedding, its topological inverse, and the corresponding
refinement and quotient identifications. These arguments explain why
BZ77's standard-subgroup definition agrees with both existing Library
predicates; no such equivalence is inserted as a hypothesis.

## Dependencies and retained proof obligations

The imported published modules are `CuspidalSupport.LeviDefinitions`,
`Classification.Supercuspidal` through that import, and `Jacquet.Parabolic`.
They supply the two predicates, actual block and refinement subgroups,
block embeddings, compatible topologies and actual Jacquet quotients.
No duplicate predicate or representation category is introduced.

Both comparison proofs remain separate obligations: construct the
conjugation-induced coinvariant equivalence, identify the single-block
embedding as a topological group equivalence, transport admissibility,
and identify all proper refinement quotient carriers. Compilation checks
the propositions but establishes none of these mathematical conclusions.
