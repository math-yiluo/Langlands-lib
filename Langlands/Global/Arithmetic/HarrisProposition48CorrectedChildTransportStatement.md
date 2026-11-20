# Arithmetic transport of the corrected Mackey child

`Proposition48CorrectedChildTransportStatement` takes the actual arithmetic
isomorphisms in the Mackey relation for a child `R`. The specified base
and inducing-field isomorphisms commute with the inclusions, and the latter
identifies `R.ξ` with the pullback of the original Mackey character. The
input realization `T` is weakly induced from the norm-corrected character,
is regular algebraic and is the actual determinant multiple of a supplied
raw realization `S` by `ν`. These three facts are supplied by the exact
branch hypotheses.

Pull `S`, `T` and `ν` back by the inverse of `e : R.E ≃+* D`. The resulting
character is `ω = HeckeCharacter.comap e.symm ν`. The arithmetic maps of
adelic general linear groups commute with the determinant. Precomposition
therefore transports the equality of the two function spaces in the
`IsDeterminantMultiple` predicate. Naturality of the norm in the
commuting square of inducing fields gives the transported inducing
character `Q.mackeyCharacter D a · (ω ∘ N)`.

For weak induction, pull back each local factor of the actual spectral
presentation of `T` along the appropriate completion isomorphism. It
transports the finite tensor slice, the unramified reference vectors,
valuation-unit groups and spherical Hecke operators. On the unramified
comparison the upper places correspond bijectively, and each factor
keeps its residue degree and the value at the transported uniformizer.
The output spectrum is therefore attached to the actual transported
realization and weakly induced from the displayed corrected character.

At an archimedean place the field isomorphism identifies the completion
and the compact and Lie algebra actions. For the complex coordinates
this is the identity or complex conjugation. The two lists of weights
are unchanged or exchanged, preserving regular algebraic infinitesimal
character in the Library normalization. This yields regular algebraicity
of the class of the transported corrected realization.

The raw child and its corrected multiple are both carried through the
same arithmetic pullback. In the prime-orbit application, changing
representatives identifies the raw classes by Euler constituent recovery.
The corrected classes can then be compared by changing the determinant
correction by the ratio of the two transported characters. Conjugate
self-duality and the auxiliary supercuspidal property use the separate
arithmetic transport statements.

Source: M. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), `harris-1998-local-langlands`,
printed pp. 191 and 195 for parity normalization and pp. 202–203 for
transport from the conjugate inducing fields. The companion TeX locators
are 866–875, 1186–1219, 1574–1614 and 1646–1664. This is a derived
arithmetic-transport statement for the explicit parity correction of the
Library's branch. It uses the full fibre product in Definition 1.3(b),
p. 186, as in `WeakInduction.inducedEulerPolynomial`.
