# General-coefficient comparison at a split supercuspidal place

`Langlands.GaloisRepresentation.HarrisSupercuspidalLocalComparisonStatement`
is an unproved derived local comparison input for Harris's Proposition 4.8.
Its forward implication is used contrapositively to distinguish local conjugates
in the induction.

Let `K` be a CM number field containing an imaginary quadratic field, and
let `S,T` be actual cuspidal realizations of the same rank `r+1 > 1`. Assume
both classes are regular algebraic and conjugate self-dual. Let `v` be a
finite place split over the maximal totally real subfield, expressed by
`Harris.conjPlace K v ≠ v`. Choose actual spectral presentations `P,Q`
whose local components at `v` are supercuspidal. Let `R,U` be genuine
lambda-adic collections over the same coefficient number field `L`, with
the same complex embedding, rank `r+1`, and pure weight `m`. Suppose `R`
and `U` are weakly associated to `S` and `T`, respectively.

For every coefficient place `lam` of residue characteristic different from
that of `v`, equality of the two local smooth classes implies that the
actual restrictions of `R_lam` and `U_lam` to the absolute Galois group of
`K_v` are linearly isomorphic over `L_lam`. The restrictions use the actual
completion embedding and the published `atFinitePlace`; the isomorphism is
an invertible linear intertwiner, not equality of characteristic polynomials
or a chosen matrix model. Both compared local factors are explicitly
supercuspidal, hence irreducible and admissible.

## Source and derived scope

M. Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39 (1999), 299–318, Theorem 5.9(ii), printed
pp.314–315 (PDF indices 15–16, zero-based), identifies the local restriction of the
cohomological family with the purely local Harris parameter at a split
supercuspidal place. It treats arbitrary cohomological coefficients.
Equations (5.4)–(5.5), printed p.313 (PDF index 14), define that parameter
with semisimplification, a character correction, and a contragredient.
Lemma 5.8, printed p.314, supplies compatibility with unramified twists.

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), 177–210, Theorem 1.7 and its surrounding
discussion, printed pp.189–190, state the local comparison and the
irreducibility of the local construction on supercuspidal classes.
The proof of Proposition 4.8 and its Remark,
printed pp.202–203, require arbitrary cohomological coefficients and use
this comparison to deduce distinctness of local conjugates from their
Galois parameters. The 1999 theorem supplies the general-coefficient
comparison, rather than an identification of differently titled historical
manuscripts.

This statement is a pairwise consequence of those results, not a new
unspecified local correspondence or a verbatim restatement of Theorem 5.9.
Its eventual proof retains the following obligations:

1. Interpret the corrected local construction (5.4)–(5.5), including its
   dual and character correction, and apply Theorem 5.9(ii) at `v` with
   general cohomological coefficients. Prove that regular algebraic type
   in this API supplies the required cohomological type.
2. Relate the supplied pure weakly associated collections to the
   cohomological families. The Library's unitary normalization agrees
   with (5.6). For a fixed pure weight, an unnormalized Euler polynomial
   is recovered by multiplying its normalized eigenvalues by the radius
   `q^(m/2)`. The proof must reconcile the weights of the cohomological
   families with this prescribed common weight, and justify the scalar
   correction and its cancellation in the pairwise comparison.
   Coefficient extension, Chebotarev density and Brauer–Nesbitt are
   required to compare semisimplifications. The supercuspidal canonical
   local parameter is irreducible, so the corresponding canonical global
   representation is irreducible. After establishing the scalar
   comparison, irreducibility removes the semisimplification ambiguity
   for a supplied family of the same rank.
3. Equal local smooth classes give the same canonical local parameter.
   Show that the common prescribed weight makes the scalar corrections
   agree, then descend the resulting isomorphism from an algebraic
   closure of `L_lam` to `L_lam`. No injectivity of the local
   correspondence is needed for this forward implication.
4. Identify the irreducible local factors of the actual spectral
   presentations with the components to which the local theorem applies.

The common pure weight is necessary for this formulation: the Library's
weak association removes the positive absolute-value scale of each
Frobenius eigenvalue. A Tate twist can preserve weak association while
changing an actual lambda-adic restriction. The statement never treats a
half-weight normalization as a lambda-adic character. Its future proof
must account for that scalar correction over a suitable coefficient
extension before cancelling it in the pairwise comparison.

The comparison assumes supercuspidality on both sides. It does not infer
supercuspidality from an arbitrary ramified Galois parameter, and does not
supply the supercuspidality of a descended representation in Proposition
4.8; that remains a conclusion of the separate descent and induction
inputs. The rank-one base case uses class field theory separately. No
`n < p` hypothesis, banality condition, or ramified nonsupercuspidal
compatibility is added. No restriction to trivial coefficient systems is
made. The published Theorem 5.9(i) existence statement remains unchanged.

The field universes `uK,uL`, Galois carrier universe `uV`, and spectral
local-factor universe `uW` are independent.
