# Compact real forms of complex semisimple groups

Workers 693 and 685 prove `Langlands.GroupScheme.RealCompactFormExistenceStatement`
as `Langlands.GroupScheme.realCompactFormExistence`. The witness is a real group
scheme whose complexification is isomorphic to the input group scheme and whose
full real point space is compact in the regular-function evaluation topology.

The source for the compact-form assertion is Armand Borel, *Lie Groups and Linear
Algebraic Groups, I. Complex and Real Groups*, Hong Kong lecture notes, 2000–2001,
§§5.5–5.7, printed and one-based PDF pp. 39–40, especially the last paragraph of
§5.6. The Lean proof constructs the form by affine Galois descent. [Registered source `borel-lie-groups-linear-algebraic-groups-2000`](https://hkumath.hku.hk/~imr/records0001/borel.pdf)

1. Apply the published self-adjoint realization theorem to the connected
   reductive group underlying the complex semisimple group. This gives a closed
   representation whose image on complex points is stable under conjugate
   transpose. On the nonidentity Galois component, compose coefficient base
   change of the ambient general linear group with its contragredient
   isomorphism. On complex points the resulting action sends a matrix \(g\) to
   \((g^*)^{-1}\), with \(g^*\) its conjugate transpose.
2. Smoothness and rational-point density give both inclusions between the closed
   subgroup ranges of the original and twisted representations. Equality of
   these ranges produces an isomorphism on each Galois pullback. The
   inverse-adjoint action squares to the identity. Computing on twice-pulled
   sections and using density upgrades the matrix action law to the
   group-scheme cocycle on the overlap.
3. Assemble the Čech datum and apply affine finite-Galois effective descent.
   The solution supplies the real group scheme and the complexification
   isomorphism. Semisimplicity transports across that isomorphism and reflects
   along \(\mathbb R \subset \mathbb C\).
4. The descent solution intertwines canonical base-change transport with the
   constructed semilinear action. The pullback projection shows that canonical
   transport fixes extended real points, so their matrices satisfy
   \(g=(g^*)^{-1}\).
   The map from the real point space to the complex point space of the original
   group is a closed embedding. On affine coordinate points the extension step
   is postcomposition with the isometric inclusion \(\mathbb R\to\mathbb C\),
   and the base-change and group-scheme isomorphism steps are homeomorphisms.
   The inverse image of the compact unitary subgroup for the closed
   representation is the full real point space, hence is compact.
