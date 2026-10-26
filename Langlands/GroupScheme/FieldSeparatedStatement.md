# Group schemes over a field are separated

Author: Worker 727.

`Langlands.GroupScheme.FieldSeparatedStatement.{u}` is the proposition that,
for every field `k : Type u` and every group scheme
`G : Langlands.GroupScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))`,
the structure morphism `G.X.hom : G.X.left ⟶ Spec k` is separated, in the
sense of Mathlib's `AlgebraicGeometry.IsSeparated`: its diagonal
`G.X.left ⟶ G.X.left ×_{Spec k} G.X.left` is a closed immersion.

The group scheme is the existing `Langlands.GroupScheme S = Grp (Over S)` of
`Langlands.AbelianScheme.GroupScheme`, with `S` exactly the spectrum of `k`.
Its object `G.X : Over S` is the underlying scheme `G.X.left` with its structure
morphism `G.X.hom` to `S`. The multiplication, unit and inverse of `G`, with
their laws, are part of `G`. The module defines no new group-scheme notion.

## Scope

The field `k` and the universe `u` are arbitrary. The statement assumes nothing
more about `G`: it need not be commutative, of finite type, quasi-compact,
smooth, reduced or proper. The field need not be algebraically closed or
perfect, and its characteristic is unrestricted. No hypothesis makes the unit
section closed. The conclusion concerns the structure morphism of the actual
group scheme to `Spec k`, not only its geometric points.

## Source correspondence

The source is the Stacks Project, Groupoid Schemes, Section 39.7, Lemma 39.7.3
(Tag 047L): "Let `G` be a group scheme over a field. Then `G` is a separated
scheme." The lemma has no further hypotheses. This matches the arbitrary field
and arbitrary group scheme above.

The source concludes that the scheme `G` is separated, which means that
`G ⟶ Spec ℤ` is separated. The Lean statement concludes that `G ⟶ Spec k` is
separated. Over `S = Spec k` these conditions are equivalent. A morphism of
affine schemes `Spec k ⟶ Spec ℤ` is separated. Separated morphisms are closed
under composition, so `G ⟶ Spec k` separated implies `G ⟶ Spec ℤ` separated.
Conversely, if a composite `G ⟶ Spec k ⟶ Spec ℤ` is separated then so is its
first factor. In Mathlib, `AlgebraicGeometry.Scheme.IsSeparated X` is
separatedness of the morphism from `X` to the terminal scheme. The corresponding
lemmas are the composition instance for `IsSeparated` and `IsSeparated.of_comp`.
The relative form is also what the source proof establishes. It shows that the
unit section `e : S ⟶ G` is a closed immersion, which by Lemma 39.6.1 is the
criterion for `G ⟶ S` to be separated.

## Proof boundary

This module only states the proposition. It adds no proof, axiom or auxiliary
hypothesis, and its publication does not prove separatedness. A separate
exact-target proof must establish it for every field and universe.

The source proof uses Lemma 39.6.1 to reduce separatedness to the unit section
being a closed immersion. The image of `e` is a closed point, by Morphisms,
Lemma 29.21.2. The map `𝒪_G ⟶ e_*𝒪_S` is surjective because `e_*𝒪_S` is the
skyscraper sheaf with value `k` at the neutral point. Schemes, Lemma 26.24.2
then shows that `e` is a closed immersion. A Lean proof may follow a different
valid route.

Source: The Stacks Project Authors, *The Stacks Project*, Groupoid Schemes,
Section 39.7, Lemma 39.7.3 (Tag 047L), statement and proof,
<https://stacks.math.columbia.edu/tag/047L>. Registered source
`stacks-group-scheme-field-separated-047l-2026-10-22`, the HTML snapshot
retrieved 2026-10-22, SHA256
`ccfc0293f9d03d241ebc1eedf41e90008022156f5dd6d4a8c889821483acb391`. The
complete statement and proof in the retained snapshot were read. No erratum for
this source was present in the project or in the published notes at authoring.
