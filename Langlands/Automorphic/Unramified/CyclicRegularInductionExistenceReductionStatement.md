# Actual regular induction from prime regular-orbit realization

In `Langlands.Automorphic.Unramified`, the propositions
`CyclicRegularInductionExistenceReductionStatement.{uF, uE, uV, uW}` and
`CyclicRegularInductionExistenceReductionTCStatement.{uF, uE, uV, uW}` give
the actual cuspidal existence common to regular induction and regular
orbit lifting. The upper cusp is regular under the cyclic Galois group and
has unitary central character. The conclusion is an actual lower cusp with
unitary central character, the multiplied rank and the attached weak
induction relation. The totally complex reduction uses the totally complex
prime realizations, pair comparison and Euler constituent recovery.

Induct on the degree with the lower field `F` fixed, allowing the top field
to range in `Type uE`. In degree one the algebra map is a field isomorphism.
Pull the cusp and its unitary central character back along that map. Take
spectral attachments to the upper cusp in both `uV` and `uW`, transport the
first along the field isomorphism and use equality of the Euler systems
attached to one class to compare it with the second. At each retained place
the single upper place has residue degree one. This is the degree-one weak
induction formula.

In prime degree apply `CyclicPrimeRegularOrbitRealizationStatement` to the
given cusp. Its full orbit has distinct constituents and is unitary, by
arithmetic transport of the unitary central character. The self-pair of the
orbit counts exactly `[E : F]` equal pairs. The supplied pair-multiplicity
formula expresses that number as a sum of `[E : F]` counts for twists of
the lower singleton, each zero or one. Every count is therefore one, so
the twist by the norm-kernel character fixes the lower class. Use
`CyclicOrbitBaseChangeWeakInductionStatement` to infer the weak induction
polynomial from this self-twist and the actual orbit lift.

In composite degree take the fixed field `K` of a subgroup of prime order.
The upper cusp remains regular for `E/K`, so the prime argument gives an
actual cusp over `K` and its weak induction relation with the upper cusp.
If a nonidentity automorphism of `K/F` fixed the middle class, extend it
to an automorphism of `E/F`. Weak base-change equivariance along `E/K`
makes the translated orbit another weak lift of the same middle singleton.
The residue-degree power rule and Euler constituent recovery over `E`
identify the two upper multisets. Thus some element of `Gal(E/K)` takes
the translated upper cusp back to the original one. Their composite fixes
the original class and restricts to the given nonidentity automorphism of
`K/F`, contradicting regularity. Apply the induction hypothesis to `K/F`
and compose the weak inductions using `WeakInductionTransitivityStatement`.
The rank equations compose by the tower law.

The prime argument uses the stated universe instantiations over both
`E/F` and `E/K`. The intermediate field and its spectral carrier are in the
upper field and carrier universes respectively. Over a totally complex
`F`, `NumberField.isTotallyComplex_of_algebra` gives the required instances
for `K` and `E`.

## Source

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), `arthur-clozel-1989-base-change`,
SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
Theorem III.4.2(e), printed pp. 202 and 207–210 (PDF pp. 216 and
221–224), supplies the prime realization. The norm-twist pair comparison
uses III.(2.2)–(2.3), printed p. 200 (PDF p. 214).
The weak-induction formulas and composition come from Definition III.6.1
and Theorem III.6.2, printed pp. 214–217 (PDF pp. 228–231).
The regularity argument is the one in Lemma III.6.4, printed pp. 217–218
(PDF pp. 231–232), using equivariance III.4.4(iii), printed pp. 210–211
(PDF pp. 224–225), and recovery III.(2.4), printed p. 200 (PDF p. 214).
The reductions expose the separate arithmetic and existence inputs of
this argument for actual cuspidal classes.
