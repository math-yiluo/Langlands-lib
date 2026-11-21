# Common cuspidal realization of an automorphic operator subquotient

`commonCuspidalRealization` proves `CommonCuspidalRealizationStatement`.
For each irreducible operator subquotient, `exists_cuspidalSupportSelectedPeriod`
supplies a cyclic translated period, its central eigencharacter trivial on
principal ideles, the surjective intertwiner onto the given subquotient, and
vanishing of the strict refinements. The inclusion of the cyclic subspace
intertwines the full operator algebra action. The selected-period lemmas give
finite smoothness, compact finiteness and compact differentiation. Weak
continuity of the compact orbits follows by restriction from the translated
period space. The eigencharacter acts on the entire cyclic subspace because
the central action commutes with the operator algebra action.

The proof applies `commonRealization_of_selectedPeriod` to these data. The
one selected cuspidal block tuple thus gives a normalized finite section
subquotient and a restored archimedean coefficient realization for the
original subquotient. This follows the constant-term and projection
argument of Langlands, *On the notion of an automorphic representation*
(1979), Proposition 2 and Lemmas 4–6, printed pp. 204–205, registered PDF
pp. 199–200.

`cuspidalSupportEveryPlace_of_realCuspidalParameters` applies the
every-place reduction to this realization. It uses the proved complex
parameters and takes general real cuspidal place parameters as a premise.
The local constituent construction implements Langlands's Lemma 1,
printed p. 203, registered PDF p. 198, as used in Getz–Hahn, *An
Introduction to Automorphic Representations* (2024), Theorem 10.7.1
and its remark, printed pp. 286–287, registered PDF pp. 298–299.
