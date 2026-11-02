# Dense affine open subspaces of separated algebraic spaces over a field

Authors: Worker 1001 and Worker 399. The Lean formula is reused unchanged from
Worker 1001's supplied, checked formulation; Worker 399 checked the retained
originals and supplied this documentation.

`Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedDenseAffineOpenStatement.{u}`
is a Prop-valued definition for every universe `u`. It states a derived
consequence of the schematic-locus arguments listed below. No cited source
states this precise proposition. This module contains the statement only;
it supplies no Lean proof of the proposition.

For every field `k : Type u`, put `S = Spec (CommRingCat.of k)`. The variable
`X : FppfSheaf S` is an actual fppf sheaf on schemes over `S`, valued in
`Type (u + 1)`. The hypotheses require `IsAlgebraicSpace S X` and the
closed-diagonal condition `IsClosedImmersion (Limits.diag X.obj)`. They then
quantify over every actual scheme `U : Over S` and every natural transformation
`a : (schemeYoneda S).obj U ⟶ X.obj` that is étale and surjective, with
`U.left` affine and `U.hom` locally of finite type over `k`.

The conclusion gives actual schemes `V W : Over S`, an open immersion
`i : (schemeYoneda S).obj V ⟶ X.obj`, a scheme morphism `p : W ⟶ U`, and a
natural transformation `b` from the functor of points of `W` to that of `V`.
The scheme `V.left` is affine. The condition

```lean
IsPullback b ((schemeYoneda S).map p) i a
```

asserts the pullback universal property of the square with top map `b`, left
map `p`, right map `i`, and bottom map `a`. Thus `W` represents the preimage
of the open subspace represented by `V`. Finally, `Dense (Set.range p.left)`
means that the image of the underlying continuous map into `U.left` is dense.
The density is asserted on the entire given atlas, including all its
irreducible components. The letter `W` in this Lean conclusion denotes the
represented pullback; the finite-locus open called `W` in the source argument
below is an intermediate object.

The statement reuses `FppfSheaf`, `IsAlgebraicSpace`, `schemeYoneda`, `IsEtale`
and `IsSurjective` from the published `AlgebraicSpace.Basic`, the
closed-immersion convention imported through `AlgebraicSpace.Thickening`,
and `IsOpenImmersion` from `AlgebraicSpace.SchemeLocalGeometry`. Each of these
morphism properties includes representability and tests the corresponding
scheme property on every represented scheme base change. In particular the
open immersion is a geometric presheaf morphism property, not merely
injectivity on field-valued points. Separatedness is exactly the same
closed-diagonal hypothesis used by
`SeparatedAddCommGroupSheafSchemeRepresentabilityStatement`.

There is no additional Noetherian, quasi-compactness, reducedness,
irreducibility, group-structure or perfectness premise. The Noetherian property
used in the source-based derivation follows from the stated hypotheses:
an affine scheme locally of finite type over a field is of finite type and
Noetherian. The hypothesis list assumes no invariant open, affine open
subspace, or scheme representation of `X`.

## Sources and derived provenance

The Stacks Project Authors' registered originals are:

- `stacks-schematic-locus-06NH-06NG-03JH-2026-11-01`, the retained folder
  `literature/Stacks Project - Schematic locus of algebraic spaces, Tags 06NH,
  06NG, 03JH (HTML snapshot 2026-11-01)`, directory SHA-256
  `37beca892cbaad6c179987f8183413967523d5591520e16db5ba386d19f7d81b`.
  The precise passages are `06NH.html`, Properties of Algebraic Spaces,
  [Proposition 66.13.3 and its proof](https://stacks.math.columbia.edu/tag/06NH);
  `06NG.html`, Decent Algebraic Spaces,
  [Lemma 68.10.4, third proof](https://stacks.math.columbia.edu/tag/06NG);
  and `03JH.html`, Properties of Algebraic Spaces,
  [Lemma 66.13.1 and its proof](https://stacks.math.columbia.edu/tag/03JH).
- `stacks-groupoid-schemes-chapter-pdf-2026-07-14`, retained at
  `literature/Stacks Project - Groupoid Schemes chapter (PDF 2026-07-14).pdf`,
  SHA-256 `4506a39201063afc270cbb68c9c0c1d3c90937c03f98cfee074605b402e7a30f`.
  The precise passages are Groupoids,
  [Proposition 39.23.9, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM),
  PDF pp.50–51, and
  [Lemma 39.24.1, Tag 03JE, with its proof](https://stacks.math.columbia.edu/tag/03JE),
  PDF p.52.

All three HTML statements, their proofs and their comment sections were read;
each tag has no direct comments in the retained snapshot. The two Groupoids
passages were read in the retained PDF. No source-specific errata note was
present in the checked workspace, current Library or project `notes/errata/`
locations.

The following explains the provenance of the proposition and the extra
finite-set step needed for its affine conclusion. It describes the intended
mathematical derivation from the original arguments, not a proof implemented
in this Lean module.

1. Put `R = U ×_X U`, with projections `s,t : R ⟶ U`. The closed diagonal
   of `X` makes `R` a closed subscheme of `U ×_k U`. This product is affine,
   so `R` is affine. The projections are étale and surjective. Their affine
   sources and targets give quasi-compactness; they are also separated and
   quasi-finite. These are the conditions used for the finite-locus argument
   in the proof of 06NH.
2. As in that proof, let `W ⊆ U` be the largest open over which `s` is
   finite. The proof invokes Morphisms Lemma 29.52.1 to place every generic
   point of every irreducible component of `U` in `W`, and More on Groupoids
   Lemma 40.6.4, together with locality of finiteness on the target, to show
   that `W` is `R`-invariant. Hence `R_W = s⁻¹(W) = t⁻¹(W)` and its two
   projections to `W` are finite étale, in particular finite locally free.
3. Let `E` be the set of all generic points of irreducible components of `U`.
   It is finite because `U` is Noetherian. Étale projections carry the
   relevant generic points to generic points, so the finite set `E` is
   invariant under the restricted relation. It lies in an affine open of
   `W`: since `U` is affine, prime avoidance gives a principal open of `U`
   contained in `W` and containing `E`.
4. Apply the construction in the proof of 03JE to this finite invariant
   set, giving an `R_W`-invariant affine open `V' ⊆ W` containing `E`.
   The printed lemma concerns one point and its finite orbit; this is the
   finite-set adaptation of its proof. More explicitly, choose an affine
   neighbourhood of the finite union of these orbits, shrink inside it to
   a principal open `D(f)` containing the union, and take the norm of
   `t* f` along the finite locally free map `s`. The resulting nonvanishing
   locus is invariant, contains the whole finite set, and is contained in
   `D(f)`. Its restriction there is principal, hence affine. In the present
   situation one can start directly with the principal open in step 3.
   Since `W` is invariant in `U`, so is `V'`.
5. Both `V'` and `R_{V'}` are affine, and the two projections are finite
   étale. Proposition 03BM therefore represents the fppf quotient
   `V'/R_{V'}` by an affine scheme `V`. As in the third proof of 06NG,
   Spaces Lemma 65.10.2 identifies this quotient with an open subspace of
   `X`. The correspondence recalled in the proof of 03JH identifies its
   preimage in `U` with exactly the invariant open `V'`. This supplies the
   geometric square expressed by `IsPullback` in the statement. The open
   `V'` contains all generic points of `U`, so its inclusion has dense
   image. This is the density required of the map `p` in the Lean formula.

This adaptation combines the finite locus from 06NH with the invariant affine
open and affine quotient method in the third proof of 06NG. It strengthens the
intermediate schematic-open conclusion to a single affine open by retaining
all finitely many generic points at once. Establishing this argument in Lean
requires a separate proof successor; compilation of the Prop definition does
not establish its truth.
