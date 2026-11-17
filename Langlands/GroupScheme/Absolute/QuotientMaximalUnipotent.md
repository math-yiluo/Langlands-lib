# Maximal unipotent subgroup images and their realization

Worker 883.

`PreservesMaximalUnipotentSubgroups q` packages the maximal-unipotent image
clause of `AlgClosedQuotientSubgroupImageStatement`, using the definitionally
equal public maximal-unipotent predicate. An image is a supplied smooth closed
subgroup together with a surjective homomorphism and a commuting square.

`preservesMaximalUnipotentSubgroups_of_borel_images` assumes that every Borel
has a Borel image under `q`. It proves maximal-unipotent image preservation
over an algebraically closed field for smooth connected affine source and
target groups. It retains the Borel-image premise explicitly.

Classify the given maximal unipotent subgroup as the unipotent part of a
Borel. Choose the assumed Borel image. Schematic dominance of the surjection
onto the supplied unipotent image factors that closed image through the
Borel image. The resulting square is a square of unipotent parts of solvable
groups. The proved solvable unipotent-part image theorem identifies the
supplied subgroup with the unipotent part of the Borel image. Classification
then makes it maximal in the whole target.

`exists_maximalUnipotent_image_of_images` assumes that `q` is surjective and
preserves maximal unipotent subgroups. It realizes every prescribed maximal
unipotent subgroup of the target as an image. Choose a maximal unipotent
subgroup of the source and its smooth connected schematic image. The
preservation premise makes that image maximal. Rational conjugacy of maximal
unipotent subgroups identifies it with the prescribed target subgroup.
Surjectivity over the algebraically closed field lifts the conjugating
rational point to the source. Conjugating the source embedding and composing
the original surjection with the target source-isomorphism yields the
required surjective map and exact commuting equation.

Both lemmas are derived reductions toward Milne 2017, Proposition 17.20
(printed pp.357–358), with the Borel-image or maximal-unipotent-image premise
left explicit. They do not by themselves prove the whole quotient-image
statement.

Source: James S. Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
Proposition 17.20, using Proposition 17.14 and Borel conjugacy.
