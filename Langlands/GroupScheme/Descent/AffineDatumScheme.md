# The underlying affine scheme of a Čech datum

This is an internal construction from the actual group-scheme Čech datum
`Descent.Datum`, the all-test relation in `Descent.DatumRelation`, and the
published ring theorem
`FaithfullyFlatCoalgebraDescent.isPushout_eqLocus_of_groupoid`.
It follows the affine-duality argument implemented in the Library's
`EtaleEquivalenceRelationCartesianAffineQuotientProof`, retaining the
base-change square as data. No new assertion from external literature is
introduced.

For schemes `B` and `S` in arbitrary universe `u`, a morphism `p : S ⟶ B`,
a group scheme `G` over `S`, and an actual datum `D`, the structure
`AffineSchemeSolution D` consists of:

- an object `obj` of the actual slice category `Over B`, with affine underlying
  scheme;
- a morphism `proj : G.X.left ⟶ obj.left`;
- the pullback square `IsPullback G.X.hom proj p obj.hom`;
- the equality `D.source ≫ proj = D.target ≫ proj`.

The structure is a solution for the underlying scheme. It does not supply a
group structure on `obj`.

## Construction and hypotheses

`Datum.nonempty_affineSchemeSolution` proves that this structure exists when
`B`, `S` and `G.X.left` are affine and `p` is flat and surjective.
`Datum.affineSchemeSolution` chooses the constructed solution. These hypotheses
imply quasi-compactness of `p`; no finite, étale, field, smoothness,
reducedness, finite-type or commutativity hypothesis is used.

The proof first obtains the relation's diagonal and composition from the
all-test reflexivity and transitivity already derived from the datum. The
target pullback square, pasted with `S ×_B S`, expresses the relation as the
scalar extension of `G.X.left` along `p`. Every scheme in these squares is
affine, so global sections yield the pushout presentations required by the
ring-level groupoid theorem. The ring map induced by `p` is faithfully flat.
The relation's common structure map to `B` puts the image of the base ring in
the equalizer subring

`A = D.source.appTop.hom.eqLocus D.target.appTop.hom`.

Effective ring descent gives the pushout square over `A`. The proof takes
`Spec A`, obtains its structure morphism from the base ring's map into `A`,
and obtains `proj` from the inclusion of `A` into the coordinate ring of `G`.
Affine duality and the actual `isoSpec` comparisons give the asserted
pullback square. Membership in the equalizer gives the relation equality.
Thus neither the descended scheme nor its base-change square is an assumed
premise.

## Properties of any supplied underlying solution

The following consequences apply to any `s : AffineSchemeSolution D`:

- `s.iso` identifies `(Over.pullback p).obj s.obj` with `G.X` in `Over S`.
  The lemmas `iso_hom_proj` and `iso_inv_fst` identify its underlying
  projections. They use the isomorphism supplied by the actual pullback square.
- `s.kernelPair` proves `IsPullback D.source D.target s.proj s.proj`.
  Paste the target square with the base's kernel pair, substitute the
  solution's commuting square, and cancel its right pullback square. This is
  the entire scheme-theoretic kernel pair, valid on every test scheme.
- Flatness, surjectivity and quasi-compactness of `p` separately imply the
  corresponding properties of `s.proj`, by stability under base change.
- `s.comp_eq_of_proj_eq` uses the kernel-pair lift to show that a morphism
  equalizing the relation takes equal values above equal quotient images.
  This lemma needs no geometric hypothesis on `p`.
- With `p` flat, surjective and quasi-compact, `s.desc f hf` factors every
  scheme morphism `f` equalizing the relation through `s.proj`. The quotient
  map is fpqc, hence an effective epimorphism. `desc_fac` proves the
  factorization, and `desc_unique` proves uniqueness by epimorphism
  cancellation. The target is any scheme in universe `u`.

These constructions establish affine effectivity of the underlying scheme
and its quotient universal property. Descending group operations and their
laws, verifying compatibility of a group-scheme identification, and proving
the host simply connected cover-existence proposition remain separate work.
