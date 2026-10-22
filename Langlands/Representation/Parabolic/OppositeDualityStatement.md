# Canonical pairing and opposite-parabolic Jacquet duality

Author: Worker 8. This pair imports the published
`Langlands.Group.GL.OppositeBlocks` construction, including its actual
upper and opposite radicals and common-Levi normalizer inclusions.

`Langlands.Parabolic.OppositeDualityStatement` states uniqueness and
existence of the canonical Jacquet pairing, together with the actual
representation equivalence it induces. These are proposition definitions,
not proofs. The asymptotic characterization is an explicit predicate on an
actual bilinear form, not a pairing supplied as a field of representation
data.

## Actual groups, quotients and normalizations

Fix a prime `p`, a finite extension `F : PadicField p`, a compatible
topological realization `T`, an ordered positive block shape `B` of rank
`n`, and a complex representation `rho` of `G = GL_n(F)`. Its carrier
and the field have independent universes; the carrier has no topology.
The theorem hypotheses require admissibility of `rho`.

The actual embedded common Levi is `M = B.leviSubgroup F.Carrier`.
The upper and lower radical subgroups of `G` are
`B.unipotentSubgroup F.Carrier` and
`B.oppositeUnipotentSubgroup F.Carrier`. Their common-Levi normalizer
inclusions are proved in `OppositeBlocks`. The group topology is exactly
the one induced by `T.topology`.

For an ambient representation, `Jacquet.Coinvariants` is the actual
quotient by the span of the radical relations, with its actual quotient
map `Jacquet.mk`. The notation `V_N` below denotes this carrier. The
smooth dual `SmoothDual rho` is the published smooth-vector submodule
of the full algebraic dual. Thus the second quotient carrier really is
`(SmoothDual rho)_(opposite N)`.

The full positive modulus on the embedded Levi is
`(T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom`.
It is the explicit block product

`delta(m) = product_(i<j) |det m_i|_F^(n_j) / |det m_j|_F^(n_i)`,

with residue-normalized absolute values. The published
`Jacquet.normalizedActionOfModulus` constructs the inverse-positive-half
action on the upper quotient. The opposite quotient of the smooth dual
uses the inverse full character `delta^(-1)`, hence its normalization is
the positive upper half. The opposite rectangular blocks reverse every
factor in the determinant product. Formal identification with the
conjugation determinant or Haar scaling remains a separate proof
obligation, and is not a hypothesis of this target.

The upper and opposite Jacquet actions in the equivalence are both
representations of the same actual embedded Levi. No arbitrary
identification of Levi groups is assumed.

## Concrete meaning of sufficiently contracting

An element of the split center of the product Levi is specified by
`a : Fin B.length -> F units`. Its `i`th block is `a_i I_(n_i)`;
the actual embedding gives its element of `G` and `M`.
Conjugation on the upper rectangular block `(i,j)` multiplies it by
`a_i/a_j`.

`CanonicalPairingAsymptotics` takes an actual complex bilinear form

`b : (SmoothDual rho)_(opposite N) -> V_N -> Complex`.

For each original vector `v` and smooth functional `ell`, it requires
some real `epsilon` with `0 < epsilon <= 1` such that, for every tuple
`a` satisfying

`|a_i/a_j|_F < epsilon` for every `i < j`,

the following exact equality holds:

`ell(rho(a) v) = delta(a)^(1/2) b([ell], normalizedJ(rho)(a) [v])`.

The bound can depend on both `v` and `ell`; it is uniform over all
block-scalar tuples satisfying the inequalities. The group element is
constructed from the tuple, and the quotient classes and normalized
action are the actual imported constructions.

These inequalities express contraction of all upper radical root
spaces. They give the same sufficiently deep negative-chamber
condition as the inequalities on adjacent block ratios: adjacent
ratios are among them, and every other ratio is a finite product of
adjacent ratios. Restricting `epsilon` to at most one makes this
comparison immediate. Thus this is an explicit `GL_n` translation of
being sufficiently near zero in Casselman's contracting chamber; it
does not bound ambient central scalars. With one block or no blocks
the root conditions are empty, as they should be.

## Existence, uniqueness and actual duality

`CanonicalPairingClause` asserts that for every admissible `rho` there
exists exactly one such actual bilinear form with
`CanonicalPairingAsymptotics`.

`OppositeJacquetDualityClause` applies to every form satisfying those
asymptotics and asserts an actual equivariant complex linear equivalence

`normalizedJ_(opposite N)(smoothContragredient rho)
    = smoothContragredient(normalizedJ_N(rho))`.

It prescribes the equivalence on quotient representatives: the smooth
functional corresponding to `[ell]` evaluates on `[v]` as
`b([ell],[v])`. Thus the equivalence is explicitly induced by the same
canonical pairing. The target uses the smooth contragredient, not the
full algebraic dual or an unspecified dual module. Equivariance,
bijectivity, and smoothness of the resulting functionals are conclusions
of existence of this equivalence, not input assumptions.

## Original source and specialization

Bill Casselman, *Introduction to admissible representations of p-adic
groups*, Chapter III, revision April 29, 2019:

- Section 4, p.5, describes opposing parabolics and the direction of the
  contracting elements through their action on the two radicals.
- Section 5, pp.5-7, uses that contraction to construct canonical lifts;
  the coefficient ring is explicitly restricted to a field on p.7.
- Theorem III.6.2, p.7, asserts the unique pairing with the displayed
  positive-half asymptotic formula.
- Corollary III.6.3, p.8, says that this pairing gives the opposite
  Jacquet quotient of the smooth contragredient as the smooth
  contragredient of the upper Jacquet quotient.

The original eight-page chapter was read. The overbars on the opposite
radical and the positive half in III.6.2 were visually checked in the
retained reading record. Text extraction loses some overbars; it must
not be read as same-parabolic Jacquet duality.

This target specializes the source's connected reductive setting to
actual standard block parabolics of `GL_n` over finite extensions of
`Q_p`, with complex coefficients. The actual split-center coordinates
and root-ratio criterion above document the specialization. There is
no equal-characteristic or general-reductive assertion.

Registered original: `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`,
Section 4 p.5, Section 5 pp.5-7, and III.6.2-III.6.3 pp.7-8.

All theorem proofs, including the existence and uniqueness assertion,
remain separate obligations. The canonical-lift and Iwahori
factorization arguments in the original are not encoded as assumed
fields here. The imported opposite geometry is independently published;
this statement still requires its own independent review and publication.
