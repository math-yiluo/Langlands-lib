# Gluing the parameters of local universal smooth families

Helper module for the proof of
`Langlands.AbelianScheme.SmoothFamilyAbelianRepresentabilityOfOpenCoverStatement`,
in the namespace `Langlands.AbelianScheme.SmoothFamilyOpenCover`. It builds
the glued parameter scheme and a universal family on it from local universal
families, assuming the published gluing statement
`RigidifiedClassesZariskiGluingStatement` as a hypothesis of
`exists_gluedClass` and `exists_universal`. The final proof module
discharges that hypothesis with the published theorem
`rigidifiedClassesZariskiGluing`. This module uses the lemmas of
[`SmoothFamilyOpenCoverLocal`](SmoothFamilyOpenCoverLocal.md).

## The basis cover

For a family `W : ι → S.Opens` covering `S` (`TopologicalSpace.IsOpenCover W`),
`SubOpens W` is the set of opens contained in some `W i`. It is a basis of
the topology (`isBasis_subOpens`), so `basisCover W hW`, the open cover of `S`
by all these opens through `Scheme.openCoverOfIsOpenCover`, is locally
directed for inclusion by Mathlib's
`Cover.LocallyDirected.ofIsBasisOpensRange`. Its transition maps are the
open immersions between members. For a test `T`, `testCover hW T` is the
pulled-back cover `pullback₁ T.hom`, locally directed by Mathlib's
`locallyDirectedPullbackCover`; `test`, `testIncl` and `testTrans` view its
members as tests over `S`. Members of a quasi-separated test are
quasi-separated, and their structure maps land in the corresponding open
(`range_test`).

## Local parameters

`LocalData A W` bundles, for each `i`, a parameter `P i` over `S` with
quasi-separated structure map and a family `M i` that is smooth-family
algebraically trivial and universal over `W i` (`IsUniversalOn`). For a basis
open `V`, `idx V` chooses a member `W (idx V)` containing it, `param V` is the
actual preimage `pullback (P (idx V)).hom V.ι` with structure map through
`V.ι`, and `family V` is the actual rigidified pullback of `M (idx V)`. By
`isUniversalOn_of_isPullback` it is universal over `V` (`family_universal`).
When `S` is quasi-separated, so is every `param V`.

For `V ≤ V'`, `transition` is the unique map `param V ⟶ param V'`
classifying `family V` by `family V'`. Uniqueness gives the functor laws
(`transition_id`, `transition_comp`), so the underlying schemes form a
functor `functor` on the basis cover, with the projections to the opens as
the natural transformation `natTrans`.

`equifibered`: every naturality square is a pullback. With `Y` the actual
pullback of `param V' → V'` along `V → V'`, which is also the pullback of
`param V'` along `V.ι` (`pullbackIsPullbackOfCompMono`), the pulled-back
family on `Y` is universal over `V`. The comparison map `param V ⟶ Y` built
from the transition classifies `family V` by it, hence is an isomorphism by
`isIso_of_isUniversalOn`, and `IsPullback.of_iso_pullback` concludes.

This is a relative gluing datum (`gluingData`) in the sense of Mathlib's
`Scheme.Cover.RelativeGluingData` (Stacks 01LH). Its colimit with
`toBase` is the glued parameter `glued` over `S`, with inclusions `glueι`.

## Gluing the classes

`localClass V` is the class of `family V`, transported to the corresponding
member of the cover `(gluingData hW).cover` of the glued scheme.
`exists_gluedClass` applies the gluing statement to these classes. Their
pullbacks to an overlap agree by the published
`rigidifiedClassesZariskiSeparated`, applied to Mathlib's cover
`intersectionOfLocallyDirected` of the overlap: on each of its members both
pullbacks are the class of the family of a smaller basis open, by
`transition_spec` (`cp_toParam`). The result is a class `q₀` on the glued
parameter with `cp (glueι V) q₀ = cl (family V)` for every `V`.

## Universality

Fix a quasi-separated test `T` and an algebraically trivial class `q` on it.
On each member of the test cover, `testMap` is the unique classifying map to
`param V` of the restriction of `q`. These maps are compatible with the
transitions (`testTrans_testMap`, by `eq_of_cm_eq`), so their composites with
`glueι` glue, by Mathlib's `glueMorphismsOverOfLocallyDirected`, to
`classify : T ⟶ glued`. It classifies `q` (`cp_classify`), by
`rigidifiedClassesZariskiSeparated` on the test cover. It is unique
(`classify_unique`): another such map restricts on each member to a map that
lifts through `param V` by Mathlib's `isPullback_natTrans_ι_toBase`; the lift
classifies the restriction of `q`, so equals `testMap`, and Mathlib's
`Cover.hom_ext` concludes.

`exists_universal`: a representative `q₀.out` of the glued class is
universal on quasi-separated tests. Its classifying maps are pullbacks of
`q₀`, so the previous paragraph applies. It satisfies the smooth-family
condition by `isAlgebraicallyTrivialFamily_of_openCover` on the glued cover,
since its pullback to each member has the class of a pullback of
`family V`.

## Provenance

The route is internal: a Yoneda-style reconstruction of the representing
scheme from local representing objects, using Mathlib's relative gluing over
a locally directed basis cover instead of explicit overlap comparison
isomorphisms. The only mathematical inputs beyond Mathlib are the published
separatedness theorem `rigidifiedClassesZariskiSeparated` and the gluing
statement `RigidifiedClassesZariskiGluingStatement`, taken as a hypothesis.
