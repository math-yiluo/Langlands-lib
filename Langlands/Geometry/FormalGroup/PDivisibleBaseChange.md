# Base change of actual p-divisible groups

`PDivisibleGroup.baseChange` pulls back each finite group scheme and both
arrows along the morphism of affine bases. Finite local freeness is
preserved by pullback. The scalar factorization is preserved because
pullback of commutative group schemes is additive.

An affine test on the new base identifies the corresponding pullback
points with points of the original group scheme after restriction of
scalars. This identification respects both group scheme maps and test
maps. It transports the injection and kernel of the two original maps.
For local surjectivity, take an affine fppf lift of the restricted test.
The composite with the original structural algebra map equips the lift
with its new coefficient algebra structure. The same ring map is still
faithfully flat and finitely presented. The identity ring map between
the two presentations of the lift transports its point. This proves the
short exact sequence on the new base.

`baseChangeFunctor` makes the pullbacks of all actual level maps an
additive functor. The construction applies to the finite level definition
and sequence (2) of Tate 1967, §2.1, printed p. 161 (PDF p. 2). It provides
the pullbacks used in the moduli problem of Rapoport–Zink 1996, Definition
2.15, printed p. 54 (PDF p. 69).
