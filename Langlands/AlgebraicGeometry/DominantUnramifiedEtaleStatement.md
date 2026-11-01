# Dominant unramified morphisms over geometrically unibranch integral bases

Author: Worker 57.

`Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{u}` states
a proposition for an arbitrary universe. Its parameters are actual
`X Y : Scheme.{u}` with `IsIntegral X` and `IsIntegral Y`, and an actual
scheme morphism `f : X ⟶ Y`. It assumes the existing predicate
`GeometricallyUnibranchIntegralScheme Y`, local finite type, formal
unramifiedness and dominance of that same `f`, and concludes `Etale f`.
This module defines the proposition and supplies no proof or default witness.

The base predicate applies to each actual local structure-sheaf stalk of
`Y`. As defined in `Picard.GeometricallyUnibranchDomain`, its normalization
in its fraction ring is local, its canonical normalization map is local,
and the induced residue-field extension is purely inseparable. Thus the
base condition concerns the actual normalization, not a supplied conclusion
certificate. `IsDominant f` means that the underlying continuous map has
dense range. `LocallyOfFiniteType f`, `FormallyUnramified f` and `Etale f`
are Mathlib's predicates on the same scheme morphism. Together the local
finite type and formal unramifiedness assumptions express the source's
unramified morphism condition.

The source is the Stacks Project, Lemma 37.37.1, stable tag
[0GS8](https://stacks.math.columbia.edu/tag/0GS8). For each source point, it
deduces etaleness from unramifiedness, local finite type, geometric
unibranchness at its image and a generalization mapping to the target's
generic point. Here the integral source's generic point specializes to
every source point; dominance maps it to the integral target's generic
point. This gives the displayed global specialization. The source proof
uses the injective local unramified criterion, Lemma 15.109.2, stable tag
[0GSC](https://stacks.math.columbia.edu/tag/0GSC).

The retained source is
`stacks-dominant-unramified-etale-2026-11-01`, folder SHA-256
`1216511f5e584381bec8be680f09519c8133ff0ea406fc89ca7e275a68f4a103`.
The exact files are `0GS8.html`, `0GSC.html`, and the contextual section
`0GS7.html`, downloaded from the original site on 2026-11-01. Those original
pages, proofs and comment sections were read. They displayed no comments;
no source-specific project errata note was found.

No noetherianity, finiteness, properness, surjectivity, smoothness, flatness,
birationality, isomorphism of function fields or characteristic condition is
added to this proposition. Source integrality is a real restriction of the
pointwise source theorem, and includes nonemptiness. The statement extends
the separately proved birational open-immersion result in a different
direction: generic extensions of degree greater than one are allowed, and
the desired conclusion is etaleness.

This is a substantial generic prerequisite for the remaining Harris normal
projection etaleness argument. That application must still establish
integrality, geometric unibranchness and dominance for the actual restricted
component maps, transfer the resulting etaleness back to the original map,
and supply a proof of this proposition. Stating it establishes none of those
facts or of the host task's remaining existence, rigidity, canonical-model
and coefficient-descent obligations.
