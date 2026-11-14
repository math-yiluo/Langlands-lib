# Nonnegative root relations for minimal-parabolic coordinate lines

This internal derived module proves the algebraic half of the highest-weight
bound used in Springer's proof of the finiteness statement (F) (Springer 1994,
§3.6, pp. 215-216). Let G be connected reductive over a field k, let
i : T -> G be a maximal split torus, and let nu be a generic cocharacter of T.
Suppose a finite-coordinate representation rho of G has a coordinate line j
that the minimal standard parabolic `standardParabolic i nu ∅` preserves. Then
some positive multiple of the torus line character psi, minus the restriction
of an ambient rational character of G, is a nonnegative integral combination of
the simple relative roots. The statement holds in every relative rank and uses
no Cartan matrix, fundamental coweights or longest Weyl element. Springer's
text uses the conclusion only for the line stabilized by a parabolic. The
route below is a Lean-specific derivation from published Library results.

## Weight comparison under conjugation

`affineMatrix_comp_of_diagonal`: if chi composed with rho is the diagonal
cocharacter with exponent vector e, then rho of chi(x) is the diagonal unit
matrix with entries x^(e b) at every affine point x of the multiplicative
group.

`rationalMatrix_entry_eq_zero_of_conj_powerAction`: suppose conjugation by a
rational point g carries the cocharacter chi' to chi, that is,
chi' followed by inner(g) equals chi. Suppose also that chi composed with rho
is diagonal with exponents e, and chi' acts on the selected basis vector e_j by
the m-th power. Then the (b, j) entry of the rational matrix rho(g) is zero
for every coordinate b with e b different from m. The proof evaluates both
sides at the universal unit t of the Laurent polynomial ring k[t, t^-1]. It
compares the (b, j) entries of rho(g) rho(chi'(t)) and diag(t^e) rho(g).

`le_of_conj_powerAction_of_orbitWeightUpperBound`: assume moreover the
published orbit bound `HasOrbitWeightUpperBound e j`. It says that on every
orbit point g e_j, each coordinate of chi-weight strictly larger than e j
vanishes. Then m <= e j. If m > e j, every entry of column j of rho(g)
vanishes: entries of weight m by the orbit bound, the others by the previous
lemma. This contradicts invertibility of rho(g).

`basisConjugate_coordinateLineCharacter`: for an adapted change of basis B
sending the coordinate line j to the coordinate line a, the conjugated
representation has the same coordinate-line character at a as rho has at j.

`coordinateLineCocharacterWeight_le_of_conj_parabolic_eigenline`: let G be
smooth, affine and connected. Let iP represent the dynamic parabolic P(chi)
and iU the dynamic unipotent of the opposite cocharacter. Suppose the line j
is preserved by P(chi), by chi and by chi', and conjugation by a rational point
carries chi' to chi. Then the chi'-weight of the line is at most its
chi-weight. The published diagonalization retaining the coordinate line puts
chi in diagonal form. In the adapted basis, the published theorem
`hasOrbitWeightUpperBound_of_parabolic_eigenline` gives the orbit bound. The
previous lemmas then compare the weights.

`preservesCoordinateLine_restrict_comp`: restricting along a further
homomorphism keeps a preserved coordinate line.

## Weyl orbit and norm-kernel inequalities

`latticePairing_relativeWeyl_le_of_parabolic_eigenline`: let zeta be a
cocharacter of T with represented dynamic parabolic and opposite unipotent.
Suppose the line j is preserved by P(zeta) and by T, with torus line character
psi. Then for every element w of the actual relative Weyl group,
<psi, w zeta> <= <psi, zeta>. A rational normalizer point s represents w.
Conjugation by s^-1 carries the cocharacter w zeta to zeta. The previous
comparison then applies, and the published
`coordinateLineCocharacterWeight_eq_latticePairing` turns weights into lattice
pairings.

`latticePairing_normKernelCocharacter_nonneg_of_parabolic_eigenline`: under the
same hypotheses, and a finite relative Weyl group, the published integral
norm-kernel cocharacter |W| zeta - sum over w of w zeta pairs nonnegatively
with psi. This is the sum of the previous inequalities over W.

## Rational relations and the simple-root cone

`RationalSpan.exists_pos_nsmul_eq_toRat_of_mem_ratSpan`: every element x of
the rational span of a set R in Q tensor M has a positive natural multiple
d x equal to the image of an element of the integral span of R.

`exists_pos_nsmul_eq_restrict_add_mem_span_simpleRelativeRoots`: for G
connected reductive, i a maximal split torus and nu generic, every character
chi of T has a positive natural d, an ambient rational character theta of G,
and an integral combination r of simple relative roots with
d chi = (restriction of theta) + r. The proof uses the published equality
"root span plus restriction range is everything" rationally. It also uses the
rational span of the simple roots, clearing of denominators, and injectivity
of the rationalization on the character lattice of the split torus.

`Dynamic.parabolic_eq_standardParabolic_empty_of_isStandardCocharacter`: the
dynamic parabolic of every standard cocharacter for the empty index set (a
cocharacter pairing positively with every simple relative root) equals the minimal
standard parabolic `standardParabolic i nu ∅`. The proof combines the
published empty-index standard/dynamic comparison with the published
relative-root sign inclusions.

`mem_closure_simpleRelativeRoots_of_standard_pairing_nonneg`: given a relative
root system on a split torus and a generic nu, let r be an integral
combination of the simple relative roots. If r pairs nonnegatively with every
empty-index standard cocharacter, then r is in the additive submonoid
generated by the simple relative roots. Write r = sum of l_beta beta and
suppose l_beta < 0. The published standard cocharacter omega for the index
set Delta minus {beta} pairs to zero with the other simple roots and
positively with beta, so <r, omega> < 0. Then nu + M omega, with
M = |<r, nu>| + 1, is an empty-index standard cocharacter with negative
pairing against r, a contradiction.

`preservesCoordinateLine_torus_of_minimalStandardParabolic`: a coordinate line
preserved by the minimal standard parabolic is preserved by the torus. This
follows from the published theorem `preservesCoordinateLine_torus_of_parabolic`
and the empty-index standard/dynamic comparison.

`exists_pos_nsmul_sub_restrict_mem_closure_simpleRelativeRoots` (main result):
under the hypotheses of the first paragraph, with torus line character psi,
there are a positive natural d and an ambient rational character theta of G
such that d psi - (restriction of theta) lies in the additive submonoid
generated by the simple relative roots. Write d psi = theta|_T + r as above.
For every empty-index standard cocharacter zeta, the minimal standard
parabolic is P(zeta), so <psi, normKernel zeta> >= 0. The restricted ambient
character pairs to zero with every norm-kernel cocharacter (published). On
the span of the roots, pairing with normKernel zeta is |W| times pairing with
zeta (published for each root). Hence |W| <r, zeta> = d <psi, normKernel zeta>
>= 0, so <r, zeta> >= 0, and the previous lemma applies.

## Scope

The ambient rational character theta is retained; it is not shown to vanish.
The errata note `notes/errata/springer-1994-reduction-global-fields.md`
records that line weights need not be multiples of a single simple root. No
adelic statement is made here; the companion module
`Langlands/Global/AdelicMinimalParabolicLineBound.lean` evaluates the relation
under adelic norms.
