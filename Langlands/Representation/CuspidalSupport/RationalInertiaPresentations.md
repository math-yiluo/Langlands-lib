# Actual rational inertia blocks and generator presentations

This internal bridge applies the actual smooth constituent Serre construction
to `rationalInertiaBlockProperty G π` and its complement. Both predicates
quantify over every actual irreducible subquotient. Their full subcategories
inherit the abelian structure, and both inclusions preserve finite limits and
finite colimits. `rationalInertiaBlockInclusion` and
`rationalInertiaComplementInclusion` name these actual full-subcategory
inclusions. No finite-length or admissibility condition is used.

An exact row in the inertia block remains exact in the smooth category by
preservation of homology. The inclusion preserves epimorphisms, so a block
epimorphism is surjective on actual smooth carriers.

`rationalNormKernelGeneratorPresentation` assumes the existing exact
`IsRationalNormKernelSmallProgenerator G π` predicate. Its membership witness
places the actual compact induction in the inertia block of the actual
universe lift of π. Its faithful integer-module-valued Hom functor makes this
object a generator, and its explicit coproduct-existence condition supplies
coproducts indexed in the Hom universe `max uF uV`. Applying
`Langlands.Renard.generatorPresentation` gives two such coproducts, an exact
row ending in any object of this block, and an epimorphism onto that object.
The preceding inclusion results give exactness and actual surjectivity in
smooth representations.

The generator-presentation theorem constructs the first map by evaluating
all morphisms into the kernel of the second evaluation map. The index sets
therefore have the required Hom size. The projective-lifting and smallness
parts of the progenerator predicate are stronger than needed for this
particular construction.

This is derived infrastructure for the uniform compression proof, assembled
from the actual constituent Serre helper, the published rational inertia and
compact-induction definitions, and the published categorical presentation
theorem. The small-progenerator predicate remains an explicit premise. This
module proves neither that premise nor preservation of infinite coproducts
by the inertia-block inclusion, nor any compression-stability assertion.
