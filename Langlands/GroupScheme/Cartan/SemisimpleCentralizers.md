# The semisimple-centralizer step of Cartan generation

Worker 1296.

This internal derived module assembles the semisimple branch of the Lie-dimension
induction. `Lie.IsNoncentralSemisimpleElement X` combines the published
representation-tested semisimplicity predicate with the assertion that the
actual tangent centralizer of `X` is proper. The noncentrality convention is
exactly that of `SemisimpleCentralizerSpanningStatement`.

`isGeneratedByCartanSubgroups_of_semisimpleCentralizers` works over an arbitrary
field with a smooth connected affine ambient group. It retains as explicit
premises the universe-general centralizer smoothness target, tangent spanning
by all ground-field noncentral semisimple centralizers, Cartan generation for
all smaller-dimensional smooth connected affine groups over that field, and
preservation of maximal tori by the identity-component inclusion of every
semisimple centralizer. It concludes the all-test Cartan-generation property.

The implemented proof chooses actual closed representatives of the
centralizers using the published representability theorem. The smoothness
premise makes them smooth, and closedness in the affine ambient group makes
them affine. Their identity components give a smooth connected affine closed
family. The identity-component differential has image equal to the original
centralizer's tangent submodule. Hence this family spans the ambient Lie
module. Properness of each tangent centralizer gives strict decrease of Lie
dimension, so the induction hypothesis supplies Cartan generation for every
member. The maximal-torus preservation premise and the published
`isGeneratedByCartanSubgroups_of_lieSpanningFamily` finish the proof through a
smooth generated envelope. Arbitrary closed competitors, including nonsmooth
and nonreduced ones, are retained throughout.

`isGeneratedByCartanSubgroups_of_geometricSemisimpleElement` specializes the
assembly to an infinite field and an actual noncentral semisimple tangent
vector on the base change to its algebraic closure. It applies the explicit
`SemisimpleCentralizerSpanningStatement` premise and uses its tangent-spanning
conclusion. It does not need to choose the separately supplied ground-field
noncentral vector.

The provenance is composition of existing actual-centralizer, identity-component,
Lie-dimension and generated-family interfaces. The module is internal derived
content. It does not prove the smoothness or spanning targets, maximal-torus
preservation, the nilpotent branch, isogeny transport, or the final unconditional
Cartan-generation statement. No rational-point argument, splitness or perfection
hypothesis is introduced.
