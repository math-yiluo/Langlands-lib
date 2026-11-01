# Separated commutative group algebraic spaces over fields

Authors: Worker 144 and Worker 148.

`Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedAddCommGroupSheafSchemeRepresentabilityStatement.{u}`
is a proposition definition for every universe `u`. It states the commutative
specialization of Stacks Project Lemma 79.10.2, retaining separatedness and local
finite type on the representing scheme. This module states the proposition;
it does not prove it.

For every field `k : Type u`, let `S = Spec (CommRingCat.of k)`. The quantified
`H : FppfSheaf S` is an actual fppf sheaf on all schemes over `S`, with values
in `Type (u + 1)`. The functor
`G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}` assigns a commutative group to every
test scheme and a homomorphism to every pullback map. The premise
`Nonempty (G ⋙ forget AddCommGrpCat.{u + 1} ≅ H.obj)` supplies a natural
isomorphism of the underlying presheaves. Thus the group operations on sections
transport compatibly with every test morphism; they are not only operations on
field-valued points.

The remaining hypotheses are `IsAlgebraicSpace S H`,
`IsClosedImmersion (Limits.diag H.obj)`, and the existence of an actual
`U : Over S` and `a : (schemeYoneda S).obj U ⟶ H.obj` satisfying
`IsEtale a ∧ IsSurjective a ∧ LocallyOfFiniteType U.hom`. These reuse the
published `AlgebraicSpace.Basic` and `AlgebraicSpace.Thickening` definitions.
The diagonal is the diagonal in the actual presheaf category. Etaleness,
surjectivity and closed immersion include scheme representability of the
respective maps and test the corresponding scheme property after every
represented scheme base change. Local finite type is witnessed by the displayed
atlas; no scheme representability of the structure morphism is assumed.

The conclusion is an actual `P : Over S` with `IsSeparated P.hom`,
`LocallyOfFiniteType P.hom`, and `Nonempty (H.obj.RepresentableBy P)`.
`RepresentableBy` gives natural bijections between actual morphisms `T ⟶ P`
and all sections `H.obj.obj (op T)`, for every `T : Over S`. There is no
restriction to reduced or field-valued tests. The field may be imperfect;
there are no additional quasi-compactness, finite type, projectivity,
reducedness or smoothness hypotheses.

The registered original source is the Stacks Project Authors' retained
`stacks-group-algebraic-spaces-fields-2026-11-01` directory, SHA-256
`8d652c67cd0a05469ce5a92e9dd8eb8428b4911b43e6d6d6c8e2541f3361734f`.
The exact correspondences are:

- `0B8D.html`, [Lemma 79.10.2](https://stacks.math.columbia.edu/tag/0B8D):
  a separated group algebraic space locally of finite type over any field is a
  scheme. The present proposition specializes its group law to commutative groups.
- `043G.html`, [Definition 78.5.1](https://stacks.math.columbia.edu/tag/043G):
  the group law is a group law on sections over every test scheme, expressed here
  through the group-valued functor and its natural isomorphism.
- `02X3.html`, [Definition 65.13.2](https://stacks.math.columbia.edu/tag/02X3):
  separatedness is the closed-diagonal condition.
- `03XE.html`, [Lemma 67.23.4(6)](https://stacks.math.columbia.edu/tag/03XE):
  local finite type is witnessed by a surjective etale scheme atlas whose
  composite to the base is locally of finite type.

Returning separatedness and local finite type on the representing scheme is the
internal transport of these geometric conditions under the representing natural
isomorphism. These transports are part of the requested proposition, not lemmas
proved in this module. The Lean formula was prepared by Worker 144 and reused
unchanged; Worker 148 checked the sources and completed this documentation.

The four original pages and their comments were read. The comment on `0B8D`
corrects an introductory reference concerning separatedness of group schemes;
the two comments on `043G` concern an inverse-map typo already corrected in the
snapshot. The other two pages have no comments. No source-specific errata note
was present in the checked project, Library or workspace `notes/errata/`
locations. The contextual example `06E9.html` describes a nonseparated
commutative group algebraic space of finite type which is not a scheme;
separatedness is retained in this statement.
