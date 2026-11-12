# Symmetric ample line bundles over an arbitrary field

`Langlands.GroupScheme.fieldSymmetricAmpleExistence` proves the entire
published proposition
`Langlands.GroupScheme.FieldSymmetricAmpleExistenceStatement.{u}`.
For every field `K : Type u` and actual commutative group object
`G : Grp (Over (Spec (CommRingCat.of K)))`, smoothness, properness and
geometric connectedness of `G.X.hom` imply existence of an actual ample
line bundle on `G.X.left` isomorphic to its pullback by multiplication
by `-1`. The theorem has no additional outer premise.

## Implemented proof

Apply the published unconditional theorem
`Langlands.GroupScheme.fieldAmpleExistence` to obtain an actual
`M : LineBundle G.X.left` with `M.IsAmple`. That theorem supplies
arbitrary-field existence by ample existence over an algebraic closure,
finite-stage spreading and finite-extension norm descent. Its proof is
independent of symmetric ample existence.

Let `f := (multiplication G (-1)).hom.hom.left`. Apply the forgetful
functor from group schemes over `Spec K` to schemes to the published
`multiplicationNegOneIso G`. Both its underlying homomorphism and its
inverse are `f`, giving `IsIso f` and `f ≫ f = 𝟙 G.X.left`.
In particular, `f` is a closed immersion.

Construct actual line bundles

```text
N := (LineBundle.pullback f).obj M
L := LineBundle.tensor pullbackTensorComparisonIsIso M N.
```

The pullback construction proves local rank one of `N`. The tensor
construction uses the unconditional published
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso` to prove local
rank one of the actual tensor sheaf `tensorObj M.obj N.obj`. Thus `L`
is an actual locally free rank-one module sheaf, rather than supplied
data with an assumed rank-one property.

The published `closedImmersionPullbackAmple` proves `N.IsAmple` from
`M.IsAmple` and the closed-immersion instance for `f`. The published
`ampleTensor` proves `L.IsAmple`; the required isomorphism from the
tensor sheaf to `L.obj` is the identity.

For symmetry, the canonical invertible pullback-tensor comparison gives

```text
f*(M tensor N) ≅ f*M tensor f*N.
```

The actual pullback composition isomorphism, transport along
`f ≫ f = 𝟙`, and the pullback identity isomorphism give
`e₂ : f*N.obj ≅ M.obj`. Apply the tensor bifunctor to the identity
of `N.obj = f*M.obj` and `e₂`, then apply `tensorComm N.obj M.obj`.
Their composite is exactly
`(Scheme.Modules.pullback f).obj L.obj ≅ L.obj`, which is placed in
`Nonempty` as the target requires.

## Actual ampleness and dependency boundary

The imported `LineBundle`, `IsAmple`, multiplication and module pullback
definitions are unchanged. Ampleness includes quasi-compactness and a
positive tensor-power section through every point whose entire generation
open is affine. Both imported preservation proofs establish this same
predicate. Tensor ampleness uses actual tensor-power isomorphisms,
generation loci of tensor sections and the affine-generation-locus
intersection theorem. Closed-immersion pullback ampleness identifies
the whole pulled-back generation open with the inverse image of the
original affine open.

The published tensor-power rank-one and pullback-section comparison
proofs discharge the corresponding obligations in this infrastructure.
This proof does not apply the conditional
`LineBundle.isAmple_iff_nonvanishingLocus` criterion.

All substantial prerequisites are reused from the current Library:
arbitrary-field ample existence, tensor and pullback local rank one,
pullback-tensor coherence, ampleness preservation, and inversion as an
involutive automorphism. The construction retains arbitrary universe
`u`, every characteristic, imperfect fields and dimension zero.
Projectivity, an existing ample bundle, algebraic closure, perfectness
and polarization are not additional hypotheses.

## Provenance and authorship

The construction follows J. S. Milne, *Abelian Varieties*, author corrected
version of January 2, 2022, Corollary 7.2, printed/PDF p.12: symmetrize an
ample invertible sheaf `M` as `M tensor [-1]*M`. The registered source is
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Theorem 7.1, pp.10–12, supplies the arbitrary-field projectivity
background; Section 20, p.42, supplies the smooth proper geometrically
connected group-scheme presentation. The imported ample-existence proof
explains its implemented spreading and norm-descent route.

These original passages and the retained author errata were read during
development. The errata source
`milne-abelian-varieties-1986-errata-2026-10-25`, SHA256
`e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`,
directs readers to the corrected author version and does not change this
corollary.

The whole affine nonvanishing-open convention and its interpretation as
the frame locus are Stacks Project Definition 28.27.1, tag `01PS`, and
Lemma 17.25.10 with proof, tag `01CY`. Both originals were read in the
registered retained source
`stacks-invertible-picard-ampleness-2026-10-21`, directory SHA256
`2a0bbd01484fc7cef97110a88cf4b3e472574fbbb9469d037170744a1462f835`.
The imported preservation proofs work directly with generation opens.

Worker 291 authored the historical conditional assembly retained in this
task's shared draft. Worker 833 discharged its comparison and ampleness
premises with published proofs and completed the unconditional assembly
using Worker 1318's published arbitrary-field ample-existence theorem.
The imported companions retain the authorship of their prerequisites.
