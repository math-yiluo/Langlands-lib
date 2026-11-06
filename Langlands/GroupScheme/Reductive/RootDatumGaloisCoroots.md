# Ordinary Galois transport of actual root data and coroots

This is an internal construction from the published ordinary lattice Galois
representations, all-test root-support transport, normalizing-point base change,
and coroot uniqueness from a finite actual normalizer image. The fields `k` and
`E` are arbitrary in universe `u`, with an algebra structure `k → E`; the
root-index type has independent universe `v`. No finite-extension or Galois
extension hypothesis is used: the acting group is the ordinary `Aut_k(E)`.

`CommGroupScheme.descentBaseChangeIso` equips the canonical group-scheme descent
comparison with its commutative structure. Over arbitrary schemes, a normalizing
point for a descended map remains realizable after base change by an endomorphism
over the original base and this descent comparison. This follows from the
published normalizing-point base-change and isomorphism-transport lemmas and
naturality of the comparison. Direct composition of characters proves that
inverse precomposition by the transported torus automorphism intertwines
ordinary character transport.

`galoisTransportRootDatum` maps a supplied root datum by the ordinary character
and cocharacter Galois linear equivalences, retaining its index type. Its roots
and coroots are their literal ordinary Galois transforms. Cancellation of the
equivalences gives the displayed pairing and root-reflection formulas.

`IsRootDatumOf.galoisTransport` proves that this mapped datum is again an actual
root datum of the same descended torus map into an affine group scheme. The
ordinary simultaneous pairing identity identifies its pairing with the actual
lattice pairing. Ordinary all-test adjoint-weight transport identifies its root
range with the original actual root set. For each root reflection, transport an
actual normalizing representative and its torus automorphism through base change
and descent. The character-intertwining identity identifies the new action with
the transported reflection, using surjectivity of the ordinary character action.

Assume that the base-changed torus map is a monomorphism on underlying schemes and
its full actual character Weyl image is finite.
`IsRootDatumOf.galoisRootIndexEquiv_coroot` then compares the original actual
datum and its Galois transport using the published
`IsRootDatumOf.coroot_eq_of_finite_weylImage`. The already constructed actual-root
index permutation identifies their roots, so coroot uniqueness gives
`P.coroot (eσ j) = σ (P.coroot j)` with the ordinary cocharacter action. This uses
neither root spanning nor integral generation by coroots.

`IsRootDatumOf.galoisRootDatumAut` packages these identities as an actual
`RootPairing.Aut P`. Its weight map is exactly the ordinary character map for
`σ`. Mathlib root-pairing morphisms use a contravariant coweight map, so that map
is exactly the ordinary cocharacter map for `σ⁻¹`. Its index equivalence is the
ordinary actual-root permutation. Pairing preservation proves the transpose
condition, and the coroot identity proves coroot compatibility.
`IsRootDatumOf.galoisRootDatumAction` proves the group law using the two ordinary
representation laws and the existing root-index action law.

`IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus` specializes this action
when the original ambient group is affine and locally of finite type, the
base-changed torus is split, and its base-changed map is a closed immersion.
Base change preserves the ambient finiteness and affineness properties. The
published `splitTorusWeylImageFinite` supplies the finite full normalizer image;
a closed immersion supplies the monomorphism. The specialization therefore has
no separate finite-Weyl-image premise. The final three formulas identify its
weight map, coweight map and index equivalence exactly.

The supplied root datum remains an input. This module constructs no root base,
Weyl correction restoring a chosen base, maximal torus, or character-annihilator
comparison, and does not prove the host Levi cocenter root-model statement.
