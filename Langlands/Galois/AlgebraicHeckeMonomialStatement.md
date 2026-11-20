# Algebraic Hecke characters and their monomial families

Harris (1998), printed p. 191, explains the common number field of values of
an algebraic Hecke character on the finite ideles, its compatible adic
avatars, and the possible half-integral norm twist. Printed p. 195 uses
`χ · |·|^((n−1)/2)` to give an integral infinity type. The proof of
Proposition 4.8, printed pp. 202–203, takes the restriction of the actual
families induced from these characters. The definitions here isolate the
rank-one construction and the induction of the resulting actual families.

`IsLocalLambdaAdicRealization` compares the finite Hecke character with the
restriction of the adic avatar to the actual local Weil group. The projection
to the absolute Galois group of the completion and geometric Weil reciprocity
are the published maps. For each Weil element the same element of the
coefficient field gives the complex Hecke value and the completed coefficient
value. This rank-one equality is used at finite places of residue
characteristic different from that of the coefficient place.

`AlgebraicHeckeAvatarExistenceStatement` is the finite-family form of the
algebraic Hecke character construction. For each algebraic character take a
number field of values, then take the compositum inside the chosen complex
embeddings. At each coefficient place transfer the algebraic infinity type
to the places over its residue characteristic and absorb it into the finite
idele character. The resulting continuous character descends through global
reciprocity to an adic character. At another finite place the absorbing
factor is one and the finite Hecke value is unchanged. At an unramified place
geometric reciprocity sends a Frobenius lift to a uniformizer. The local
clause is this same rank-one reciprocity calculation for all local Weil
elements. This statement isolates the uses of the global Artin map for the
avatars. The planned proofs for the exact-stabilizer branches use a different
route and retain their existing class field theory dependencies.

`IsInducedFromLambdaAdicCharacter` expresses actual finite-index induction.
The absolute Galois group embeds as the subgroup fixing the embedded copy of
the finite extension in a common algebraic closure. On that subgroup the
specified adic character acts on a lifted scalar line. The predicate gives
a linear intertwining equivalence from its induced representation to the
specified continuous representation. This permits all carrier universes used
by the consumer.

`HeckeMonomialCollectionStatement` supplies that induction at every
coefficient place of a common field. It takes a unitary character `χ` of a CM
field and avatars of its norm twist `χ · |·|^(b/2)`. It gives the rank, a
common finite set of bad base places, and a single collection of polynomials
over the coefficient field. Away from the conductor and the extension's
ramification, geometric Frobenius permutes the inducing cosets in cycles
indexed by all places above `v`. On the cycle at `w` the return map has
eigenvalue given by the adic avatar on geometric Frobenius at `w`, which
produces the factor `1 − C(a_w) X^f(w|v)`. The local avatar clause makes the
exceptional set independent of the coefficient place. Continuity of the
induction is checked in the finite coset coordinates on each open coset of
the kernel of the coset action.

The eigenvalues of the algebraic normalization at `w` have absolute value
`q_w^(-b/2)` under all complex embeddings. One can check this using a ray
class power of the prime to evaluate the powered character via its algebraic
infinity type. The sums of the two exponents at every complex place equal
`b`. Permuting the CM embeddings preserves that sum. Since
`q_w = q_v^f(w|v)`, all reciprocal roots at `v` have weight `−b` in the
Library's geometric-Frobenius convention. Dividing each eigenvalue by its
absolute value removes the norm twist and gives exactly
`WeakInduction.inducedEulerPolynomial` of the original `χ`, including a factor
for every `w` above `v`.

## Sources

- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), 177–210, printed pp. 191, 195, 202–203.
  `harris-1998-local-langlands`, companion TeX lines 866–875, 1186–1219,
  1574–1586 and 1630–1644.
- J.-P. Serre, *Abelian l-adic representations and elliptic curves*, II,
  §§2.3 and 2.6–2.7, pp. II-10–II-12 and II-21–II-24,
  `serre-abelian-l-adic-1989`.
  The realization on ideles gives the finite-place clause with geometric
  reciprocity in the Library's convention.
- J. Tate, *Number theoretic background*, Proc. Symp. Pure Math. 33 (1979),
  Part 2, (2.3.5), p. 12, `tate-1979-number-theoretic-background`, as used by the Library's
  `WeakInduction` module.
