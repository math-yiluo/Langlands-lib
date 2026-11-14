# Isobaric invariance in the Proposition 4.8 induction

`Langlands.Global.Harris.Proposition48IsobaricInvarianceStatement` is an
unproved implication from the published
`Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement`.
The latter is an explicit theorem hypothesis, not part of the isobaric data.

For small fields `F,K`, an `F`-automorphism `σ` of the number field `K`,
and actual isobaric constituent data `D` over `K`, supply spectral systems
attached to both `D` and `D.galoisConj σ`. If their Euler polynomials agree
outside a finite set, the conclusion is equality of the two multisets,
including ranks, classes and multiplicities. This is precisely
`D.IsGaloisStable σ`. The local-factor universe `uV` is arbitrary.
Attachment uses genuine cuspidal spectral presentations. Existence of
those presentations or equality of their Euler polynomials is not asserted.
No realized isobaric representation is substituted for the multiset.

Source and provenance: M. Harris, *The local Langlands conjecture for
GL(n) over a p-adic field, n < p*, Invent. Math. 134 (1998), 177–210,
`harris-1998-local-langlands`, proof of Proposition 4.8, printed p.202 (one-based PDF p.26), final
paragraph; companion `math_9611226v1.tex`, lines 1630–1644, especially
1641–1644. Harris restricts the
induced Galois family to the final prime cyclic field. That restriction
is Galois invariant, and strong multiplicity one then makes the
associated isobaric representation invariant.

The present interface is a derived separation of the last inference.
Its proof must enumerate the two multisets, apply the published
Euler constituent-recovery clause of cuspidal spectral rigidity, and
turn the resulting bijection into multiset equality. Recovering the
Euler equality from the actual restricted monomial family, constructing
the presentations, and transporting the raw parity-corrected
constituents remain obligations of the branch inputs. The single-class
cuspidal strong-multiplicity-one statement alone does not state this
mixed-rank multiset conclusion. This statement proves neither rigidity
nor the invariance step, and it changes no published declaration.
