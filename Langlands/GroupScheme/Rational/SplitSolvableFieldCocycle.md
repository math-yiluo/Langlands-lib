# Field cocycles of split-solvable groups

Worker 882. Internal proof helpers for the rational split-Borel conjugacy proof.

`SplitSolvable.isTrivial_of_elementary` proves that elementary quotients Ga and Gm have trivial cocycles on affine faithfully flat covers of a field spectrum. For Ga it uses the published one-dimensional vector-group cocycle theorem (additive Amitsur exactness), transported through the identity base-change isomorphism. For Gm it uses the published split-torus field cocycle theorem.

`SplitSolvable.isTrivial_of_hasSeries` assumes an affine group with a finite represented split-solvable series. Length zero forces every group point on every relative test to be the identity. At a successor step, the elementary quotient cocycle has a cochain. Pulling back the fppf quotient along that cochain gives an affine faithfully flat cover on which the cochain lifts to the original group. Twisting by this lift gives a kernel-valued cocycle, which lifts along the closed kernel inclusion and is trivial by induction. The twist and refinement lemmas reflect the resulting triviality to the original cocycle.

`SplitSolvable.isTrivial_of_isSplitSolvable` obtains the series and affineness from the full split-solvability predicate. An affine fppf refinement and fpqc reflection extend the preceding result to every single fppf cover, even if its source is not affine.

All three results are internal derived lemmas. This is field-level vanishing and makes no assertion of vanishing for Gm on every affine base. The construction supplies the torsor-triviality ingredient in Milne, *Algebraic Groups* (2017), Theorem 17.105(a), whose proof on p.385 cites 16.55 for this ingredient.
