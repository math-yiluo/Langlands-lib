# A proper field scheme with an ample trivial line bundle is finite

Author: Worker 412.

`Langlands.AlgebraicGeometry.Picard.ProperAmpleTrivialFiniteStatement.{u}`
is a proposition definition. It quantifies over every field `K : Type u`, every
`X : Scheme.{u}`, every structure morphism
`f : X ⟶ Spec (CommRingCat.of K)`, and every actual `L : LineBundle X`.
Its three hypotheses are `IsProper f`, `L.IsAmple`, and
`Nonempty (L.obj ≅ SheafOfModules.unit X.ringCatSheaf)`. Its conclusion is
`IsFinite f`, finiteness of the entire scheme morphism.

The line bundle is the published locally free rank-one sheaf of modules.
Ampleness is exactly the published `LineBundle.IsAmple`: compactness of `X`
and affine whole generation loci of global sections of positive actual
`Langlands.Scheme.Modules.tensorPow` powers of `L.obj`. The isomorphism is an
isomorphism of actual module sheaves. No operation on a substitute family of
bundles is introduced. This statement needs no pullback construction.

There is no nonemptiness, reducedness, smoothness, connectedness, dimension,
affineness, projectivity, finite-fibre, or global-section-finiteness premise.
In particular, empty and nonreduced schemes and fields of every characteristic
are included. No residue-locus comparison or rank-one assertion about tensor
powers is assumed as an additional hypothesis.

## Derived mathematical provenance

This is a general geometric criterion derived from standard scheme geometry;
it is not the literal statement of Milne's Theorem 8.2. The intended geometric
argument is as follows. Transport ampleness through the given isomorphism to
obtain an ample structure sheaf. By Stacks Lemma 28.28.1, `X` is quasi-affine.
Writing `A = Γ(X, 𝒪_X)`, quasi-affineness gives the canonical open immersion
`j : X → Spec A`. The structure map factors through `j`. Since `Spec A` is
separated over `Spec K`, properness of `f` makes `j` proper. A proper open
immersion is a closed immersion, so `X` is a closed subscheme of the affine
scheme `Spec A`, hence affine. Its structure morphism to `Spec K` is therefore
affine and proper, hence finite. Properness is used at the closed-immersion
step; ampleness of the structure sheaf by itself yields quasi-affineness.

The last implication is present in the pinned Mathlib as
`AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom` in
`Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`. That file also has
`AlgebraicGeometry.IsProper.of_comp`, the separated-target cancellation used
in the argument above. These observations describe a future proof route,
not a Lean proof supplied by this module. Any missing geometric comparisons
must be proved or bypassed by a valid argument, rather than inserted as
premises of this target.

Milne's Theorem 8.2, p.13, first proof paragraph applies the idea to the
scheme-theoretic multiplication kernel on an abelian variety: restriction of
the pulled-back ample invertible sheaf is both trivial and ample, and Milne
concludes that the kernel has dimension zero. The present statement isolates
a more general proper-scheme finiteness criterion for that application; it
asserts neither the multiplication formula nor an isogeny theorem.

## Original sources and verification

- The Stacks Project, Section 28.28, Lemma 28.28.1, tag
  [01QD](https://stacks.math.columbia.edu/tag/01QD), including its proof and
  comments. Registered source:
  `stacks-ample-powers-restriction-quasiaffine-2026-10-24`, file `01QD.html`,
  directory SHA256
  `03dddd39b5528263fbc3633f1545b8544e937bb29c9752ffe4a351bb6e093e9a`.
  The source states the equivalence of quasi-affineness and ampleness of the
  structure sheaf, and its proof uses the canonical map to the spectrum of
  global sections. The comments confirm that Stacks includes quasi-compactness
  in quasi-affineness; the Library's ampleness already includes compactness.
- J. S. Milne, *Abelian Varieties*, 1986 article, author corrected version
  January 2, 2022, [Theorem 8.2, p.13](https://www.jmilne.org/math/xnotes/AVs.pdf),
  first proof paragraph. Registered source:
  `milne-abelian-varieties-1986-author-2022`, SHA256
  `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.

Both retained originals were read at these locations. No erratum file for
either source is present in `notes/errata/` at the working Library base.
The statement is pinned to environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. This module states the criterion;
it does not prove it.
