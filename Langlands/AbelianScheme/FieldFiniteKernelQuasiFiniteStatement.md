# Local quasi-finiteness from finite kernel over a field

`Langlands.GroupScheme.FieldFiniteKernelQuasiFiniteStatement` is a `Prop`-valued
definition. It states, without supplying a proof, that for every field
`K : Type u`, every group object
`G : Grp (Over (Spec (CommRingCat.of K)))` with `IsCommMonObj G.X`, and every
endomorphism `f : G ⟶ G`, the hypotheses

- `Smooth G.X.hom`;
- `IsProper G.X.hom`;
- `GeometricallyConnected G.X.hom`;
- `IsFinite (kernel f).X.hom`

imply `LocallyQuasiFinite f.hom.hom.left`.

The universe `u`, field, and characteristic are arbitrary. The conclusion is
Mathlib's predicate on the actual underlying scheme morphism. The kernel is the
published construction in `Langlands.AbelianScheme.Kernel`: the pullback of the
group homomorphism along the target unit section. Its scheme pullback square is
`Langlands.GroupScheme.kernel_isPullback_scheme`. The hypothesis concerns the
kernel's structure morphism to `Spec K`; it says that the kernel is a finite
`K`-scheme. It is not a finiteness hypothesis on the inclusion `kernelι f`.

## Source and derived provenance

The source is J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic Geometry*
article in the author's corrected version dated January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The retained file is
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
Proposition 8.1 and its proof on printed/PDF p.12, and the opening definition of
§20 on printed/PDF p.42, were read directly. No source-specific errata note was
present in the project notes.

Proposition 8.1 relates finite kernel, equal dimension, and the finite, flat,
surjective isogeny condition for homomorphisms of abelian varieties. Its proof
uses translation to identify scheme-theoretic fibres with the kernel after
extending the ground field, and then obtains quasi-finiteness. Section 20
presents abelian schemes as smooth proper group schemes with connected
geometric fibres, and identifies their fibres with abelian varieties. Over
`Spec K` this supplies the group-scheme formulation used here. Commutativity is
retained explicitly, as in the parent finite-kernel isogeny target.

This statement is a derived intermediate step extracted from that proof, not a
verbatim separately stated proposition of Milne. Milne has already reached
surjectivity when using the translation argument. The present step needs only
the finite-kernel hypothesis together with the displayed ambient hypotheses:
fibres outside the image may be empty and still satisfy the quasi-finiteness
criterion. The next section explains this planned adaptation; this file proves
none of it.

## Planned proof and arbitrary-field descent

For a point `y` of the target scheme, consider the scheme-theoretic fibre over
its residue field `κ(y)`. Its structure map and the underlying endomorphism are
of finite type: the latter is proper because the source is proper over the
field and the target is separated over the field.

An empty fibre is a finite scheme over `κ(y)` and has a finite underlying set.
For a nonempty fibre, pass to an algebraic closure `Ω` of `κ(y)`. The geometric
fibre remains nonempty, and finite type ensures it has an `Ω`-point `x`.
Right translation by `x` identifies the kernel of the base-changed group
homomorphism with this fibre; translation by the inverse point gives the inverse
map. This identification is between schemes over `Ω`; it is not asserted to be
an isomorphism of group schemes for a fibre over a nonidentity point.

The published `Langlands.GroupScheme.kernelBaseChangeIso` from
`Langlands.AbelianScheme.KernelBaseChange` identifies that kernel with the base
change of the original kernel. Finiteness is preserved by base change, so the
geometric fibre is finite. To return to `κ(y)`, one may descend finiteness along
the faithfully flat field extension. Alternatively, the projection from the
geometric fibre to the residue-field fibre is surjective on points, so its
finite set of points gives finiteness of the latter's underlying set. Neither
route assumes that every target point lies in the image of `f`.

Mathlib supplies `LocallyQuasiFinite.of_fiberToSpecResidueField` and, with
quasi-compactness, `locallyQuasiFinite_iff_isFinite_fiber`. The alternative
point-set route uses `LocallyQuasiFinite.of_finite_preimage_singleton` with
local finite type. The later proof must justify its chosen descent route and
all fibre comparisons. It should reuse the separately constructed split-fibre
translation isomorphism based on `GrpObj.mulRight` once published. No translation
construction is needed to define this proposition, and none is imported here.

## Scope and proof boundary

The statement adds no algebraic-closure, perfectness, dimension, projectivity,
surjectivity, flatness, or geometric-fibre-identification hypothesis. It requires
no smoothness or reducedness of the kernel and takes no conclusion certificate.
It concerns endomorphisms over arbitrary fields, with exactly the four displayed
geometric hypotheses.

This module supplies only a statement. Its exact proof is a separate obligation
after independent statement acceptance and Library publication. It neither
proves nor weakens
`Langlands.GroupScheme.FieldFiniteKernelIsogenyStatement`: finiteness,
surjectivity, and flatness of the endomorphism remain conclusions of that parent
target. For the finiteness step, Mathlib already proves
`IsFinite.of_isProper_of_locallyQuasiFinite` in
`Mathlib.AlgebraicGeometry.ZariskisMainTheorem`; no duplicate is required.
