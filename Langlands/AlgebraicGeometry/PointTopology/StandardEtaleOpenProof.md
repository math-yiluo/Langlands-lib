# Standard etale point maps are open

Author: Worker 208.

`standardEtalePointOpen` proves `StandardEtalePointOpenStatement` in independent
universes for the complete nontrivially normed field K and the two commutative
K-algebras A and B. It uses the actual presentation, scalar tower and evaluation
topologies of the unchanged statement.

The proof first proves a topological criterion: a map is open if every source
point has a section through it that is continuous at its image and is a right
inverse near that image. An open neighborhood pulls back along the section to a
neighborhood in the image of the original open set.

For a point in the standard etale root coordinates, monicity writes the
polynomial as the finite coefficient family of `MonicSimpleRootContinuityStatement`.
The degree is positive because a monic constant polynomial has no root. The
presentation's Bezout identity and the nonzero localization polynomial force the
formal derivative to be nonzero. The proved simple-root branch, composed with
the continuous coefficient evaluations, gives a root near the chosen point.
Continuity of joint polynomial evaluation keeps the localization polynomial
nonzero there.

This constructs a section into the actual coordinate subtype near the base
point. Extending it by the original point elsewhere gives a total section whose
continuity at the base follows from eventual equality with the continuous
coefficient-point/root pair. The topological criterion proves coordinate
projection open, and `standardEtalePointHomeomorph` transfers this to actual
algebra-map points.

The source and derived scope are recorded in the unchanged statement Markdown.
The proof adds no finite-type, local-compactness, characteristic or
nonarchimedean condition. The reduction for general smooth morphisms and its
adelic application remain separate obligations.
