# Finite-kernel endomorphisms of abelian group schemes are isogenies

`Langlands.GroupScheme.fieldFiniteKernelIsogeny.{u}` proves exactly the published
proposition `Langlands.GroupScheme.FieldFiniteKernelIsogenyStatement.{u}`.
Its statement pair and import closure are unchanged.

For every field `K : Type u`, group object
`G : Grp (Over (Spec (CommRingCat.of K)))` with `IsCommMonObj G.X`, and
endomorphism `f : G ⟶ G`, assume smoothness, properness and geometric
connectedness of the structure map `G.X.hom`, and finiteness of
`(kernel f).X.hom`. The conclusion is `IsIsogeny f`: the actual scheme
morphism `f.hom.hom.left` is finite, flat and surjective. The kernel hypothesis
concerns its structure morphism to the field spectrum. Surjectivity concerns
scheme points.

## Implemented proof

Write `q := f.hom.hom.left` and `p := G.X.hom`. Install the given properness
of `p` as a local instance. Since `f` is a morphism over the field spectrum,
`Over.w` identifies `q ≫ p` with `p`. The composite is therefore proper.
The target structure morphism is separated, as follows from its properness,
so Mathlib's `IsProper.of_comp q p` gives `IsProper q`.

The published theorem `Langlands.GroupScheme.fieldFiniteKernelQuasiFinite`
takes exactly the four geometric and finite-kernel hypotheses of the target
and gives `LocallyQuasiFinite q`. Its implementation uses the actual kernel
base-change and translation isomorphisms. It splits each nonempty fibre over
the residue field of a source point, then uses the range formula for scheme
pullbacks to prove finiteness of the original topological fibre. Empty fibres
are treated explicitly. Its paired documentation supplies these details.

Mathlib's `IsFinite.of_isProper_of_locallyQuasiFinite` now gives `IsFinite q`.
This is the proper and locally quasi-finite case of Zariski's main theorem;
the present proof does not require projectivity.

The published theorem `Langlands.GroupScheme.fieldFiniteEndomorphismSurjective`
uses the given smoothness, properness and geometric connectedness, together
with the finiteness just proved, to give `Surjective q`. That theorem derives
geometric integrality and Noetherian topology from the structure morphism,
then applies the independently proved surjectivity of finite endomorphisms of
irreducible Noetherian schemes.

Finally, `Langlands.GroupScheme.fieldFiniteSurjectiveEndomorphismFlat` uses
the same structure hypotheses and the established finiteness and surjectivity
to give `Flat q`. Its proof passes to an algebraic closure, obtains a nonempty
flat open by generic flatness, propagates flatness by group translations,
and descends along the field extension. These intermediate constructions are
internal to the imported theorem.

The proof assembles `IsFinite q`, `Flat q` and `Surjective q`, in that order,
into the existing `IsIsogeny f` definition. Every field, characteristic and
universe is retained. There are no additional theorem arguments or hypotheses
on projectivity, dimension, the image, the kernel's reducedness, or flatness.

## Provenance and contributions

This is the endomorphism specialization of Proposition 8.1, (c) implies (d),
on printed/PDF p.12 of J. S. Milne, *Abelian Varieties*, the 1986 article in
the author's corrected revision of January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The retained source is
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
For an endomorphism the equal-dimension condition in (c) is automatic.
Section 20, opening definition on p.42, supplies the smooth proper group-scheme
presentation with connected geometric fibres. The target's companion explains
this correspondence. These passages were read during development; the retained
author errata does not change them.

The implementation is an internal assembly of the three imported published
proofs and Mathlib's properness and finiteness results. Its route differs from
Milne's dimension and coherent-sheaf argument. In particular, the flatness step
uses generic flatness, translations and descent; Milne's printed Theorem 4.2
already assumes flatness and is not used to establish it.

Worker 139 wrote this assembly and companion. The imported quasi-finiteness
proof is by Worker 419, surjectivity by Worker 414, and flatness by Worker 415.
Their companions record their implementations and further contributions.
