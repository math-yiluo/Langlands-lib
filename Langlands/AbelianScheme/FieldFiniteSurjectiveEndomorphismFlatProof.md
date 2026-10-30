# Flatness of finite surjective abelian endomorphisms over fields

`Langlands.GroupScheme.fieldFiniteSurjectiveEndomorphismFlat.{u}` proves
exactly the unchanged published proposition
`Langlands.GroupScheme.FieldFiniteSurjectiveEndomorphismFlatStatement.{u}`.
For every field `K : Type u`, commutative group object
`G : Grp (Over (Spec (CommRingCat.of K)))`, and endomorphism `f : G ⟶ G`,
smoothness, properness, and geometric connectedness of `G.X.hom`, together
with finiteness and surjectivity of `f.hom.hom.left`, imply flatness of
that same scheme morphism. The universe and characteristic are arbitrary.
There are no additional theorem arguments.

## Implemented proof

The proof uses generic flatness, group translations, and faithfully flat
descent. Put `Ω := AlgebraicClosure K`, in the original universe, and let
`b : Spec Ω ⟶ Spec K` be the morphism induced by the field inclusion.
The functor `(Over.pullback b).mapGrp` constructs the base-changed group
`GΩ` and its actual endomorphism `fΩ`.

The private helper `pullback_over_map_isPullback` proves that the
underlying morphism of this base-changed endomorphism fits into the
cartesian square over the original endomorphism, with the target and
source projections `pullback.fst G.X.hom b`. It cancels the defining
pullback squares using `IsPullback.of_right` and the over-category map
identities. Finiteness and surjectivity therefore pass to `fΩ`.

Smoothness is stable under this base change. It implies local finite
type over the field `Ω`, so the underlying scheme of `GΩ` is locally
Noetherian. The published theorem
`Langlands.AbelianScheme.smoothGeometricIntegrality` derives geometric
integrality of `G.X.hom` from its given smoothness and geometric
connectedness. Applying it to the algebraic-closure pullback gives
`IsIntegral GΩ.X.left`.

The published theorem `Langlands.AlgebraicGeometry.finiteGenericFlat`
now supplies a nonempty open subset of the target on which the finite
morphism `fΩ` is flat. The published theorem
`Langlands.GroupScheme.translationFlat` applies over the algebraically
closed field `Ω`, using finiteness, surjectivity, and this nonempty open,
to conclude that `fΩ` is flat everywhere. Its proof propagates the open
flat region by group translations; its paired documentation gives the
closed-point and group-compatibility details.

Finally, the field inclusion induces a surjective, flat, quasi-compact
map `b`. These properties also hold for the target projection
`pullback.fst G.X.hom b`. The first private helper,
`flat_codescendsAlong_faithfullyFlat`, proves codescent of flat ring
homomorphisms along faithfully flat maps using Mathlib's
`Module.Flat.of_flat_tensorProduct`. The private instance
`flat_descendsAlong_fpqc` uses `HasRingHomProperty.descendsAlong_flat`
to obtain scheme descent of flatness along surjective flat
quasi-compact morphisms. Applying this descent to the cartesian square
and the established flatness of `fΩ` proves `Flat f.hom.hom.left`.

Properness and commutativity are retained as hypotheses of the exact
target, although this route does not need them. The algebraic closure,
local Noetherianity, integrality, and nonempty flat open are constructed
inside the proof. No perfectness, kernel smoothness or reducedness,
flatness certificate, locally free direct image, or constant-rank
hypothesis is supplied.

## Provenance and contributions

The mathematical claim is the endomorphism specialization of
Proposition 8.1, (b) implies (d), on p.12 of J. S. Milne,
*Abelian Varieties* (1986 article, author revision January 2, 2022),
registered as `milne-abelian-varieties-1986-author-2022`. The retained
source is `literature/J. S. Milne - Abelian Varieties (1986 article,
author revision 2022).pdf`; §20, p.42 supplies the group-scheme
presentation. These passages and Theorem 4.2 on p.6 were read during
route selection, together with the retained errata notes.

This is an internal assembly of the three imported proof modules and
Mathlib's pullback and descent machinery. It implements the valid
generic-flatness route described above. Milne's printed Theorem 4.2
already assumes flatness; it is not used to establish flatness here.
The proof also does not use the parent finite-kernel isogeny statement
or the relative fibrewise-flatness theorem.

Worker 415 wrote this assembly, its private helpers, and this companion.
The imported generic-flatness theorem is by Worker 667, translation
propagation by Worker 668, and smooth geometric integrality by Worker
416; their paired documentation records their proofs and further
contributions. These results are reused by importing their published
Lean modules.
