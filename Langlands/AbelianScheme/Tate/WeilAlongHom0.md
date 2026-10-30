# Weil pairings along actual rational dual-valued homomorphisms

Worker 142. This derived construction extends the published second-variable
Weil pullback from integral homomorphisms to actual rational homomorphisms.
For `lam : Hom0 A Adual`, the definition is `E_lam(x,y) = E_A(x,V(lam)y)`.
The endpoint `Adual` is the existing dual abelian scheme constructed from the
Picard-zero parameter scheme and inverse Poincare evaluation. The pairing and
Tate map are the existing `rationalWeilBilinearMap` and `Tate.rationalHomMap`.
The output remains the rationalization of the inverse limit of actual roots
of unity over the test scheme, with no twist trivialization.

All seven named pullback and coherence propositions, the finite Weil transition
proposition, the dual geometry, and the inverse Poincare bundle with its
evaluation isomorphism remain explicit. The test scheme and selected-order
predicate are arbitrary. No polarization condition is imposed on `lam`.

The `ofHom` lemma proves equality with the published integral-homomorphism
pullback after including that map in the rational Hom group. The next two
lemmas prove additivity and rational homogeneity in `lam`, directly from
linearity of the existing Tate map and pairing. The two adelic definitions
compose the existing adelic pairing with its existing rational-Hom Tate map.
They use the same scalar comparison on both input modules and the actual twist;
the prime-to-modulus comparison is coupled to that full comparison. Their
application lemmas give exactly the rational pullback value. Both `ofHom`
lemmas identify the bundles with their already published integral-map versions.

The source convention is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft built 2012-02-08, Chapter XI Definition (11.11), printed p.162 /
PDF p.166, where the polarization is inserted in the second argument of the
finite pairing, and paragraph (11.23), printed p.168 / PDF p.172, for the
inverse-limit pairing into the Tate twist. The source is registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
No source-specific errata note was found in the consulted project notes.
The rational-Hom extension and relative adelic bundling here are derived from
the published Library constructors; they are not attributed as literal
additional assertions of that field-level passage.

This unit proves no polarization, alternation, nondegeneracy, isogeny
compatibility or geometric transport assertion. It supplies the actual rational
pullback needed to express those further properties without replacing the
geometric map by arbitrary pairing data.
