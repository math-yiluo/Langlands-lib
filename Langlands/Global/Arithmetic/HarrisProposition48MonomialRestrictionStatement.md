# Restriction and invariance of the actual monomial family

This pair isolates the Galois representation step in the proof of Harris's
Proposition 4.8. The three implications concern actual continuous
representations and their cofinite spectra. They apply to both the
prime-orbit and singleton Mackey cases.

`Proposition48Problem.IsMackeyEnumeration` chooses one automorphism of the
actual normal closure for each double coset. The bijection uses the
Library order `Gal(L/D) \ Gal(L/E) / Gal(L/E')`, which is related by
inversion to Harris's order. The same enumeration is used on the arithmetic
and automorphic sides of the argument.

`Proposition48MonomialMackeyRestrictionStatement` takes the actual
induction of the parent avatar and an actual induced collection of each
Mackey character. The same coefficient field and complex embedding identify
the character values throughout. After extending the field embeddings into
compatible algebraic closures, the image of the absolute Galois group of `D`
is the subgroup fixing `D`. The preimage bijection of double cosets in the
absolute Galois group and the finite Galois group gives the same Mackey
index, since the normal subgroup fixing the normal closure lies in the two
fixing subgroups. In the Mackey direct sum, the intersection for `a` is the
subgroup fixing `D · a(E')`. Its scalar character is the restriction of the
parent's conjugated avatar. The finite-place norms and the map for geometric
Frobenius give exactly the avatar of `a(ξ) ∘ N` at unramified places.
The idelic norm normalization commutes with the norm pullback, hence has
the same exponent in both realizations. Chebotarev and continuity identify
the two characters on the whole absolute Galois group. The finite-index
coinduction model decomposes into the subspaces supported on the double
cosets. Its intertwiners, composed with the given induction equivalences,
give the actual direct-sum equivalence at every coefficient place. With a
different chosen closure embedding use `GaloisRepresentation.closureChange`
and `pullbackAlongClosureEquiv`, which identify the restrictions by the
action of the corresponding Galois element.

`FiniteDirectSumWeakAssociationStatement` takes the actual isomorphisms and
the weak associations of the summands. Intersect the cofinite good sets.
The direct sum multiplies the Euler polynomials, including repetitions of
roots. Unitarization divides each reciprocal root by its own complex
absolute value, so it respects this product. The polynomial of each
monomial summand uses the product over every place of its inducing field
above the given base place, with the exponent equal to the corresponding
residue degree. This uses the corrected sum convention in Harris's
Definition 1.3(b), as in `WeakInduction.inducedEulerPolynomial`.

`GaloisRestrictionEulerInvarianceStatement` extracts the arithmetic equality
needed for isobaric invariance. A lift of `σ` to the algebraic closure of
`K` gives an intertwiner by its action in the original representation.
Transport of local restriction and of geometric Frobenius to the conjugate
place yields equal Euler polynomials after the coefficient completion
embedding. For each good place choose a coefficient place of a different
residue characteristic to invoke compatibility and descend the equality to
the common coefficient field. The comparison uses the same complex
embedding and unitarization on both sides. The excluded base places can be
taken to contain the exceptional sets and their pullbacks. This comparison
concerns the numerical systems. Equality of the actual isobaric multiset
with its conjugate is obtained by applying the branch's explicit invariance
premise to the spectral attachments and this Euler equality.

## Sources

- M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), 177–210, `harris-1998-local-langlands`,
  Definition 1.3(b), p. 186, and proof of Proposition 4.8, pp. 202–203.
  The retained TeX gives the Mackey indexing and the norm-pulled characters
  in lines 1574–1602 and the isobaric sum and restriction invariance in
  lines 1630–1644.
- J. Tate, *Number theoretic background*, Corvallis Part II (1979),
  `tate-1979-number-theoretic-background`, p. 12, (2.3.5), for restriction
  of an induced representation to the groups of the completions. It
  accounts for the sum over all places in the local induction convention.
- J.-P. Serre, *Abelian l-adic representations and elliptic curves*,
  `serre-abelian-l-adic-1989`, Chapter I, §2.2, pp. I-8–I-10, for density
  and its use in distinguishing continuous characters by Frobenius values.
