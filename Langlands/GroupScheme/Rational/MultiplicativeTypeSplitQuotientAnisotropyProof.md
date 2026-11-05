# Structural anisotropy of multiplicative-type maximal-split quotients

Authors: Worker 1467 and Worker 1341.

`Langlands.GroupScheme.multiplicativeTypeSplitQuotientAnisotropy.{u}` proves
exactly the unchanged proposition
`MultiplicativeTypeSplitQuotientAnisotropyStatement.{u}`. For any field, an
actual finite-type multiplicative-type group `Z`, a maximal split-subtorus
inclusion `j`, and the specified represented fppf quotient `q : Z ⟶ C`, it
constructs `HasAnisotropicTorusFiniteQuotient C`. This gives an actual closed
torus in `C` with split rank zero and an actual finite schematic fppf quotient
of `C` by that torus.

The implemented proof first applies `IsMultiplicativeType.isAffine` and
`.isCommMonObj` to `Z`. Commutativity makes `j` central on every test scheme.
`IsMaximalSplitTorus.isAnisotropic_quotient` then proves `splitRank C = 0`.
Its underlying pullback argument lifts any closed split torus in `C` to a
central extension by the original split torus. The split-extension theorem
makes the pullback a split torus; maximality of `j` and cancellation along the
flat surjective projection force the tested inclusion to be trivial.
Coordinate cocharacters then establish the split-rank-zero conclusion.

The flatness, surjectivity and local finite presentation supplied by `hq`
allow `IsMultiplicativeType.of_fppfHom` to show that `C` is multiplicative
type. That helper descends finite-type and affine geometry, obtains an
injective Hopf coordinate map after the original arbitrary splitting
extension, and uses coefficient contraction to prove group-like spanning.
Reconstruction from group-like elements and finite generation of their
character subgroup supply the actual diagonalizable splitting model for `C`.

`IsMultiplicativeType.exists_torus_finiteQuotient` now provides an actual
torus `T`, a closed immersion `i : T ⟶ C`, and an actual quotient `p : C ⟶ Q`
with finite structure morphism for `Q`. Its construction takes the schematic
image of a power map killing the finite character factor. After the supplied
splitting extension, closed dominant factorization identifies that image with
the free-factor split torus. Effective affine descent supplies the quotient,
and fpqc descent supplies finiteness of its target.

Finally, `splitRank_le_of_isClosedSubgroup i hi` bounds the split rank of
`T` by that of `C`. Since the latter is zero, `T` is anisotropic. The proof
returns `T`, `i`, `Q`, `p` and the established properties as the exact
existential witnesses. The quotient predicates retain equality of the full
represented kernel with the all-test range of the specified inclusion.

The source context is Milne, *Algebraic Groups* (2017), registered source
`milne-2017-algebraic-groups`: Definition 12.17, printed p.236 / PDF p.252;
Theorem 12.23 and Corollary 12.24, printed p.240 / PDF p.256; Notation 12.29,
printed p.241 / PDF p.257; and Exercises 12-2, 12-5 and 12-6, printed p.252 /
PDF p.268. This is a derived structural assertion. The proof establishes the
Library's split-rank convention directly; it does not assume an identification
with the character-anisotropy convention of Exercise 12-5 or a Galois
classification theorem. The complete registered official errata snapshot of
2 November 2026 has no correction to these cited passages.

The theorem holds in every universe `u` and in arbitrary characteristic.
The splitting extension is arbitrary. All torsion characters and nonsmooth
finite scheme structure are retained. No rational-point surjectivity,
finite point-cokernel, topology or compactness conclusion is asserted.
