# A normalized form for a symmetric rational root pairing

Worker 227. For a rational root pairing `P` whose roots and coroots span
their ambient spaces, suppose that the full root-coroot pairing is
symmetric: `P.pairing i j = P.pairing j i` for every pair of indices.
The definition `Langlands.LinearAlgebra.SymmetricRootPairingForm.form`
chooses a rational symmetric bilinear form on the root space whose values
on pairs of roots are exactly this root-coroot pairing. Every root has
self-pairing two. No finiteness, irreducibility, crystallographicity,
reducedness or positivity hypothesis is imposed on `P`.

The root space, coroot space and index type may have independent universe
levels. The construction uses the ordinary Mathlib `RootPairing` perfect
pairing and `IsRootSystem` spanning hypotheses.

The proof sends a finitely supported rational combination of roots to
the same combination of their coroot functionals. Symmetry of the
pairings shows that evaluation of this latter combination at any root
equals evaluation of the corresponding coroot on the original root
combination. Since roots span, a relation among roots therefore gives
the zero functional. The map to coroot functionals descends through the
kernel of the surjective root-combination map; its quotient equivalence
identifies the quotient with the root space. This gives a linear map
from the root space to its dual, hence a bilinear form. Its value at a
root is that root's coroot functional. Symmetry of the full root-coroot
pairing gives the required formula on pairs of roots, and symmetry of
the form follows by checking both arguments on spanning roots.
`form_isSymm`, `form_apply_root_root` and `form_apply_root_self` record
these properties of the chosen form.

The theorem `injective_of_mapsTo_roots` applies to a second rational
root pairing `Q` with `Q.IsRootSystem` and `Q.IsIrreducible`. If a rational
linear map takes every root of `Q` to a root of `P`, it is injective.
Indeed all root images have self-pairing two in the constructed symmetric
form. The imported constant-root-image theorem then proves injectivity.
The source and target spaces and index types may have independent
universe levels; neither root system is required to be finite,
crystallographic or reduced.

This is an internal linear-algebra derivation from Mathlib's root-pairing,
finitely supported linear-combination and linear-quotient APIs, together
with `Langlands.LinearAlgebra.ConstantRootImage`. It is not presented as
a transcription of a literature theorem. It supplies a generic input
for a possible absolute-to-relative root argument, and supplies no
comparison for actual algebraic groups, descent to a split torus, or
proof of the local anisotropic affine-diagram statement.
