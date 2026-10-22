# Left-translation compatibility for the actual enveloping action

For every number field K and natural rank n, `EnvelopingLeftTranslation`
states that the actual operator D(u) commutes with the pullback
L(a)f(x) = f(ax), for every element u of the actual complex universal
enveloping algebra and every element a of the completion-coordinate
archimedean general linear group.

The operators, Lie algebra and smooth-function space are the already
constructed objects; this proposition introduces no abstract replacement
action or assumed commutator law. Multiplication of endomorphisms means
composition, so the formula is D(u)(L(a)f) = L(a)(D(u)f).
This gives the compatibility needed to preserve invariance under any
specified left translations, including the archimedean part of a rational
adelic translation.

This is a derived implementation statement in the framework of
Borel–Jacquet, *Automorphic forms and automorphic representations*, sections
1.1, 1.3 and 4.1 (printed pages 189–190 and 194; one-based PDF pages
184–185 and 189). Registered source `borel-jacquet-1979-automorphic`,
SHA256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The precise bundled equality is derived from the differential and
universal-enveloping constructions rather than quoted from the source.
