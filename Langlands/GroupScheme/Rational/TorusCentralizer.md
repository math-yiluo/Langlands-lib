# Torus centralizers on all test schemes

`torusCentralizer i` is the subgroup functor of points commuting with the whole
image of the torus homomorphism `i`. For a point over `U`, the defining condition
tests every morphism `V → U` and every point of the torus over `V`. It includes
non-affine and nonreduced test schemes.

The source centralizer is the common Levi group `Z(S)` of Borel–Tits,
*Groupes réductifs* (1965), Theorem 4.15(a), printed pp.90–91 (PDF pp.37–38),
source `borel-tits-1965-groupes-reductifs`. Milne, *Algebraic Groups* (2017),
Theorem 25.6(b) and its proof, printed pp.545–546 (PDF pp.561–562), source
`milne-2017-algebraic-groups`, describes the same centralizer and its comparison
with a suitable cocharacter centralizer.

The all-test-scheme formulation and its extension to arbitrary bases and
commutative group schemes are derived constructions. Neither splitting nor
maximality is needed to define this subgroup functor. The construction uses the
published `SubgroupFunctor`; closure under products and inverses and naturality
follow from commutation in each group of points.

`mem_torusCentralizer_iff_universal` identifies the defining condition with
commutation of the two universal points on `U ×_S T`. Pullback along `(a,t)`
proves the converse. `mem_torusCentralizer_base_iff` identifies the subgroup over
the base with the points whose published `innerIso` fixes `i`, using its point
formula and Yoneda extensionality.

`torusCentralizer_gm_eq_dynamicCentralizer` identifies this construction on the
multiplicative group with the published `Dynamic.centralizer`. Its proof rewrites
the universal-point condition as constancy of the conjugation orbit.

`torusCentralizer_le_dynamicCentralizer` proves that centralizing the whole
torus implies centralizing every cocharacter through it, by evaluating the
commutation condition on the universal multiplicative-group point. Rational
parabolic, Levi and unipotent subgroups keep the published definitions
`Dynamic.parabolic`, `Dynamic.centralizer` and `Dynamic.unipotent` of the
composite cocharacter. This convention follows Milne 25.1, printed p.544
(PDF p.560), and Borel–Tits 4.15. No equality for a generic cocharacter or
representability theorem is proved here.
