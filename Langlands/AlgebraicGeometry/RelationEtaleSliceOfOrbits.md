# Etale surjective slices from local slices on every orbit

`EtaleRelationSliceData t s` packages a scheme `V` and a locally finite type
morphism `g : V → U` for which the associated map
`V ×_{g,U,t} R → R → U`, using `s` after the second projection, is etale and
surjective. The universe of `V` is the same as those of `U` and `R`.

For a scheme equivalence relation, `etaleRelationSliceOfOrbits` chooses such
data under two explicit hypotheses. First, every point `x` is the target
`s(r)` of a relation arrow whose source `t(r)` satisfies a supplied predicate
`P`. Second, every point satisfying `P` lies in the image of a locally finite
type morphism whose associated relation slice map is etale. There is no
smoothness assumption on the relation in this conditional construction.

The implemented existence proof first uses reflexivity to put the source
`t(r)` in the associated slice image. The forward image saturation theorem
then puts `s(r)=x` in that image. Thus local etale slices meet every point,
and in particular every finite type point. The included globalization proof
forms a coproduct of one slice for each finite type point. Source locality
gives local finite type and etaleness; openness of the etale image and the
affine closed-point test give surjectivity. The included saturation and
globalization Markdown files describe those proofs in detail.

The data are selected by classical choice from this proved existence result,
so they are not canonical. This is an internal construction by Worker 424,
using Worker 303's orbit-saturation and globalization route. The contribution
includes the unchanged supporting statement pairs and the complete proofs of
both statements. It does not assume or prove existence of good points on
orbits, or the unconditional smooth equivalence relation slicing theorem.
Those are separate obligations of the host task.
