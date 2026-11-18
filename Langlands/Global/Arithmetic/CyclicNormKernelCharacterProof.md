# Norm-kernel Hecke characters for cyclic number-field extensions

`Langlands.Global.HeckeCharacter.cyclicNormKernelCharacter` proves
`CyclicNormKernelCharacterStatement.{uF, uE}` for independent universes
`uF` and `uE`.

## The norm quotient

For fields in a common universe, `exists_normReciprocitySameUniverse` uses
`localRelativeClassFormation` and `fundamentalClass_exists` to obtain an
arithmetically normalized family of global fundamental classes. Relative Weil
transfer then gives a surjection \(W_{E/F}\to C_F\) with kernel the commutator
subgroup. The Weil projection to \(\operatorname{Gal}(E/F)\) kills this
subgroup because the Galois group is cyclic. It therefore descends along
transfer to a surjective homomorphism \(C_F\to\operatorname{Gal}(E/F)\).
Exactness identifies the kernel of the Weil projection with the image of
\(C_E\) in \(W_{E/F}\). Transfer on that image is the idele-class norm, so the
descended homomorphism has kernel \(N_{E/F}C_E\).

For independent universes, `exists_normReciprocity` applies this result to
\(E/B\), where \(B\) is the bottom intermediate field of \(E/F\) and lives in
the universe of \(E\). The equivalence `baseImageAutEquiv` identifies the
Galois groups and their actions on \(C_E\). Galois descent identifies both
\(C_F\) and \(C_B\) with the same subgroup of fixed elements in \(C_E\), giving
a multiplicative equivalence \(C_F\simeq C_B\). After inclusion into \(C_E\),
the two norms of an idele class are products of its Galois conjugates. These
products agree by reindexing along `baseImageAutEquiv`. Injectivity of the
inclusion of \(C_B\) shows that the equivalence carries each norm for \(E/F\)
to the corresponding norm for \(E/B\). This transports the surjective
homomorphism and its kernel to the original \(C_F\).

## Existence, order and powers

The quotient \(Q=C_F/N_{E/F}C_E\) is thus cyclic of cardinality \(n=[E:F]\).
The norm map is open, so its range is open and \(Q\) has the discrete
quotient topology. A multiplicative equivalence from \(Q\) to the complex
\(n\)th roots of unity gives a faithful character into \(\mathbb C^\times\).
Its pullback along the continuous quotient map is a Hecke character whose
kernel is exactly the norm image.

Every Hecke character trivial on norms descends to a homomorphism on \(Q\).
For a character \(\eta\) with exactly the norm kernel, the descended
homomorphism is injective. Its value at a generator of \(Q\) has order \(n\).
Evaluating \(\eta^{\operatorname{orderOf}(\eta)}=1\) at a representative of
that generator shows that \(n\) divides \(\operatorname{orderOf}(\eta)\).
The existing norm-of-inclusion power lemma gives \(\eta^n=1\), establishing
the reverse divisibility.

If \(\chi\) is trivial on norms, its value on the generator after descent is
an \(n\)th root of unity. The value of the descended \(\eta\) is a primitive
\(n\)th root, so the value of the descended \(\chi\) is its \(i\)th power
for some \(i<n\). Homomorphisms from \(Q\) are determined by their value at
that generator, yielding \(\chi=\eta^i\) on pullback. Conversely, every such
power is trivial on norms.

## Sources

The quotient identification is the cyclic case of the global reciprocity
isomorphism \(\operatorname{Gal}(E/F)^{\mathrm{ab}}\simeq C_F/N_{E/F}C_E\)
in J. Neukirch, *Algebraic Number Theory* (1999), VI (5.5), printed p. 391
(PDF p. 403), `neukirch-1999-algebraic-number-theory`.

J. Arthur and L. Clozel introduce the character of \(\mathbb A_F^\times\)
with kernel \(F^\times N_{E/F}\mathbb A_E^\times\) for prime cyclic degree
before Theorem 4.2. Just after Lemma 6.3 they describe the character for
cyclic degree as a generator of the character group of
\(\mathbb A_F^\times/(F^\times N_{E/F}\mathbb A_E^\times)\).
On \(C_F\) the kernel is \(N_{E/F}C_E\).
See *Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula* (1989), III §4, printed p. 202 (PDF p. 216), and III Lemma 6.3,
printed p. 217 (PDF p. 231), `arthur-clozel-1989-base-change`.
