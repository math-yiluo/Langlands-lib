# Finite kernel implies local quasi-finiteness over a field

The theorem `Langlands.GroupScheme.fieldFiniteKernelQuasiFinite` proves exactly
`Langlands.GroupScheme.FieldFiniteKernelQuasiFiniteStatement.{u}` from the
published [statement module](FieldFiniteKernelQuasiFiniteStatement.md).
For every field `K : Type u`, group object
`G : Grp (Over (Spec (CommRingCat.of K)))` with `IsCommMonObj G.X`, and
endomorphism `f : G ⟶ G`, it takes the four stated hypotheses on the structure
map and kernel and concludes `LocallyQuasiFinite f.hom.hom.left`.
The universe, field, and characteristic are arbitrary.

The proof uses properness of `G.X.hom` and finiteness of the actual kernel's
structure morphism. Smoothness, geometric connectedness, and commutativity are
accepted as required by the exact target but are not needed by this argument.
No assumption is added on the kernel, the image, or any fibre.

## Source and derived provenance

The motivating source is J. S. Milne, *Abelian Varieties*, the 1986
*Arithmetic Geometry* article in the author's corrected version dated
January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The retained original is
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
Proposition 8.1 and its proof on printed/PDF page 12 use translation to
identify scheme-theoretic fibres with the kernel after extending the base
field. The opening definition of section 20 on printed/PDF page 42 gives
the smooth proper group-scheme setting with connected geometric fibres.
Both pages were read directly.

The complete retained author errata page,
`literature/J. S. Milne - Abelian Varieties (1986 article errata, HTML snapshot 2026-10-25).html`,
registered as `milne-abelian-varieties-1986-errata-2026-10-25`, was also read.
It says its corrections are incorporated in the author's corrected article;
none of its listed entries changes the two passages used here.

This is a derived intermediate result, rather than a separately stated
proposition of Milne. Its implemented descent differs from Milne's
algebraically closed field argument: the residue field of a chosen source
point already supplies a splitting section. The published
[KernelBaseChange](KernelBaseChange.md) and
[KernelFiberTranslation](KernelFiberTranslation.md) provide the actual
kernel comparison and translation isomorphism. The remaining comparisons
are categorical pullback calculations and Mathlib's scheme pullback range
formula. The proof constructs no new translation map.

## Finiteness of split fibres

The private lemma `finite_kernel_baseChange` handles an arbitrary map
`b : T ⟶ S`. The structure map of the base change of `kernel f` is
`pullback.snd (kernel f).X.hom b`, which is finite by stability of finite
morphisms under base change. Forgetting the group structure in
`kernelBaseChangeIso b f` gives an isomorphism in `Over T` to the kernel
of the base-changed homomorphism. The inverse isomorphism's over-category
compatibility equation factors the latter structure morphism through the
former. Composition with an isomorphism preserves finiteness.

The private lemma `finite_split_fiber` then applies the published identity
`kernelFiberIso_inv_structure`. For a section `x` of the source over its
base, that identity factors the structure map of
`pullback f.hom.hom (x ≫ f.hom.hom)` through the finite kernel structure
map by the inverse of `kernelFiberIso f x`. This proves finiteness of the
split fibre over the base, not merely finiteness of its inclusion.

The private lemma `finite_points_over_field` shows that a scheme finite
over a field has finitely many underlying points. A finite morphism is
locally quasi-finite, so Mathlib's
`IsLocallyArtinian.of_locallyQuasiFinite` makes its source locally
Artinian, hence discrete. Quasi-compactness of the morphism and compactness
of the field spectrum make the source compact. A compact discrete space
is finite. This works for nonreduced and empty finite schemes as well.

## The residue-field comparison and point-set descent

Write `q = f.hom.hom.left`. For a source point `x`, set

```text
T = Spec κ(x),
a = G.X.left.fromSpecResidueField x,
b = a ≫ G.X.hom,
f' = ((Over.pullback b).mapGrp.map f).
```

The pair `(a, id_T)` defines a section `x'` of the base-changed source.
The fibre `F` in `Over T` over the image section `x' ≫ f'.hom.hom` is
finite over `T` by the two kernel lemmas. Its underlying point set is
therefore finite.

The private lemma `baseChange_isPullback` proves that the naturality square
from the base-changed morphism to the original morphism is Cartesian. It
cancels the target's base-change pullback square from the source's one,
using the over-category morphism equations. Forgetting the split-fibre
pullback to schemes and pasting with this naturality square gives a
Cartesian square with right map `q` and bottom map `a ≫ q`. The section's
first projection is `a`, which identifies that bottom map. Thus the actual
scheme `pullback q (a ≫ q)` is isomorphic to `F.left` and has finitely many
points.

Mathlib's `Scheme.range_fromSpecResidueField` and the range formula for a
composite give `Set.range (a ≫ q) = {q x}`. The scheme pullback range
formula `Scheme.Pullback.range_fst` now gives

```text
Set.range (pullback.fst q (a ≫ q)) = q ⁻¹' {q x}.
```

The range on the left is finite because its source scheme has finitely
many points. This proves `finite_preimage_image_point`. It is the required
point-set descent: the split fibre's projection covers the entire original
topological fibre. It uses the range theorem for scheme pullbacks, without
identifying a scheme pullback's points with arbitrary pairs of points.
No algebraic-closure hypothesis or unproved faithful-flat descent criterion
is used.

## The exact target

Properness of `G.X.hom` includes separatedness. Since `f` is a morphism
over the base, `q ≫ G.X.hom = G.X.hom`; Mathlib's `IsProper.of_comp`
therefore proves that `q` is proper, in particular locally of finite type.
For each target point `y`, the proof distinguishes whether some source
point maps to `y`. In the nonempty case the preceding lemma supplies the
finite fibre; otherwise the preimage of `{y}` is empty and finite.
`LocallyQuasiFinite.of_finite_preimage_singleton` concludes the exact
published proposition.

The theorem asserts neither surjectivity nor flatness and does not complete
`FieldFiniteKernelIsogenyStatement`. All lemmas supporting its assembly
are private; the public result is the exact target theorem above.
