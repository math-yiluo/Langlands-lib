# Topology of actual affine base change

Author: Worker 208.

`affineBaseChangeTopology` proves the exact proposition
`AffineBaseChangeTopologyStatement`: for a compatible tower of commutative
algebras `C → D → A`, a topological ring `A`, and an arbitrary actual affine
scheme `X` over `Spec C`, the existing function
`ringPointBaseChangeEquiv C D A X` is a homeomorphism.

The topology is the independently defined global-section evaluation topology
on each actual affine point space. Its target is the actual pullback of `X`
along `Spec D → Spec C`. No topology is defined by transport along the
base-change equivalence.

This is derived infrastructure for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed p.2, Proposition 2.1,
and printed p.6, the local base changes preceding Theorem 3.6 and (3.6.1).
Registered source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The proof concerns the general evaluation-topology comparison; it does not
claim to establish the full arithmetic or nonaffine assertions of Theorem 3.6.

Write `B = AffineCoordinateRing C X`, the actual global sections with their
structural `C`-algebra. `ringBaseChangeAffineOverIso_hom_fst` proves that
the existing presentation of the actual pullback as `Spec (D ⊗[C] B)`,
followed by the spectrum of `b ↦ 1 ⊗ b`, equals its first pullback
projection followed by `X`'s canonical affine isomorphism. Its proof
composes the explicit projection identities of Mathlib's tensor spectrum
isomorphism, pullback symmetry and the pullback functor's map.

`affineBaseChange_inverse_coordinates` identifies the inverse point comparison
in these coordinates. A point of the actual pullback, composed with its
tensor presentation, gives a `D`-algebra map `t : D ⊗[C] B → A`.
The inverse point comparison has the same coordinates as the `C`-algebra map
`b ↦ t (1 ⊗ b)`. The proof applies faithfulness of `Spec` to the coordinate
ring maps, uses the presentation projection identity and the existing inverse
pullback-point formula, and then evaluates the resulting ring-map equality.
This lemma needs only a topology on `A`, because it uses the existing
presentation homeomorphism to name its point comparison; it requires no
continuity of ring operations.

`isHomeomorph_ringPointBaseChangeEquiv` composes four existing homeomorphisms
in the inverse direction: the actual affine presentation, the spectrum point
comparison, inverse scalar extension of algebra points, and the inverse
canonical global-section point comparison for `X`. The preceding coordinate
lemma proves this composite equals the inverse of the original
`ringPointBaseChangeEquiv`. Bijectivity then identifies its inverse with that
original function, giving the required full homeomorphism conclusion.
`affineBaseChangeTopology` universally quantifies this result to prove the
unchanged statement.

All rings and schemes occupy an arbitrary common universe `u`. There is no
topology on `C` or `D`, continuity assumption on their structure maps,
finite-type, local-ring, open-unit, Hausdorff or separation assumption.
The topological-ring hypothesis is on `A`; the forward tensor-coordinate
continuity theorem supplies its use. The actual arithmetic local and adelic
rings, and the nonaffine point topologies, remain separate obligations.
