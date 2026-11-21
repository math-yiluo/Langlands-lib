# Clozel's one-place existence from a global realization theorem

`ClozelOnePlaceExistenceReductionStatement` asks for the published
one-place conclusion at every rank and finite place, given global
realization of compatible unitary local profiles over the same CM
extension. The proof `clozelOnePlaceExistence_at_of_localProfile` takes a
distinguished real embedding as an input. It uses the singleton profile at
the given split finite place with residue `1` in `ZMod n`. The prescribed
positive dimensions are `n − 1` at the distinguished embedding and `n`
elsewhere. When `2` divides `n`, the sum of the split residues is one in
`ZMod 2`, the sum of the negative dimensions is one, and the remaining
term is \([E:\mathbb Q]\,(n/2)\) modulo two. Either `4 ∣ n` or even real
degree makes that term zero. The compatibility condition holds vacuously
in odd rank. This is the specialization in Clozel 1991,
Proposition 2.3(i)–(ii) and its prescribed-place remark, pp. 105–106.
The reduction is derived by expressing that specialization through
the Library's local-profile and completed-algebra interfaces.

The realization premise supplies actual local completion equivalences and
invariants. Injectivity of the denominator embedding and the order of one
in `ZMod n` give order `n` for the two signs of the prescribed invariant.
`isDivisionAt_of_brauer_order` gives division at each completed CM place.
`isDivision_of_isDivisionAbove` uses a place above the given finite place
and reflects division from its completion. The same realized real and
finite charts give the two signature clauses and the required quasi-split
models. The proof `clozelOnePlaceExistence_of_localProfile` takes a real
embedding from the equivalence between real and complex embeddings of a
totally real field and packages the resulting signature clauses as the
Harris signature.

The companion reflex-field theorem applies the Library's `RealReflex`
comparison to supplied Harris signature charts and a Harris CM section.
Rank at least three is an immediate case of that comparison. In rank two
the parity branch forces even real degree. The degree is positive and
counts the real embeddings, so there is a second real embedding. The
global realization proposition is the remaining premise for the one-place
existence reduction.
