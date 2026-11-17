# Anti-affine groups and supplied affinization quotients

Over an arbitrary field `k`, `IsAntiAffine G` asserts that the actual structure
map induces an isomorphism `Γ(Spec k, O) → Γ(G, O)`. The canonical
identification of `Γ(Spec k, O)` with `k` makes this precisely the condition
`O(G) = k`. This is the anti-affine condition of SGA 3, Exposé VI_B,
Theorem 12.2 and Lemma 12.3 (Gille–Polo recomposed edition, 13 October 2024,
printed pp.430–431 / PDF pp.100–101; registered source
`sga3-expose-vib-gille-polo-2024`). The official Tome I errata of the same
date do not change these results.

`IsAntiAffine.hom_eq_zero` proves that every actual group homomorphism from
such a group to an affine group is trivial. The proof compares global-section
maps after evaluation at the identity section. Since the source structure
map is an isomorphism on global sections, evaluation is its inverse. Unit
preservation gives equality after evaluation, and maps to an affine scheme
are determined by their global-section maps. This uses all scheme morphisms,
so its consequence holds on every test scheme.

`IsAntiAffine.isUnipotent` is an internal consequence for the existing Library
predicate: every matrix representation is trivial, so the constant vector
with all coordinates equal to one is a nonzero fixed vector on all tests.
No affineness of the anti-affine group is asserted.

`IsAffinization q` is a predicate on a supplied homomorphism `q : G → Q`:
`Q` is affine and `q` induces an isomorphism on global sections.
`IsAffinization.targetIso` identifies the actual target with `Spec Γ(G, O)`,
and `comp_targetIso` identifies `q` itself with the canonical scheme
morphism `G → Spec Γ(G, O)`.

`AntiAffineQuotient G` packages a supplied affinization homomorphism to a
smooth connected affine group. Its projection is smooth, surjective and
quasi-compact; its actual scheme-theoretic kernel is smooth, connected and
anti-affine. These are the properties of the canonical quotient in SGA 3
VI_B, Theorem 12.2, specialized to smooth connected algebraic groups. This
file defines the data and proves the elementary consequences just described;
it does not assert existence of the quotient, construct the group law on the
affinization, or prove preservation under field extension.
