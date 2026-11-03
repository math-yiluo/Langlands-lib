# Group coordinate weight decomposition from the pointed case

This internal auxiliary reduces the published target
`CoordinateWeights.CoordinateWeightDecompositionStatement` to two inputs. The first
is the published pointed proposition
`PointedCoordinateWeights.PointedCoordinateDecompositionStatement`. The second is a
pair of cotangent facts for each action. The module does not prove either input.
Each one appears as an explicit hypothesis, so this file is a derived proof step,
not a proof of the target.

The proof reuses Mathlib's `iSupIndep.le_iff_eq_of_iSup_eq_top`. For
families `A` and `B` in a complete modular lattice, if `B` is independent,
`A i ≤ B i` for every `i`, and the supremum of `A` is `⊤`, then `A = B`.
This supplies the same lattice principle used by the pointed-coordinate
closed-immersion proof, without a second local copy.

`isInternal_and_map_eq_of_surjective` concerns a surjective linear map `π` from
`U` to `Q`. It takes an internal direct-sum decomposition `W` of `U` and an
independent family `W'` of submodules of `Q` with `(W i).map π ≤ W' i`. Its
conclusion is that `W'` is an internal decomposition of `Q` and that
`(W i).map π = W' i` for every `i`. The images of the `W i` span `Q` because `π`
is surjective, so the `W' i` span `Q` too. Together with independence this gives
internality. The equalities are the lattice lemma applied to the submodule
lattice of `Q`, which is modular.

`isInternal_weightSpace_and_augmentationWeightSpace_of_pointed` gives the
coordinate and augmentation decompositions for an actual automorphic action `b`
of a split torus on an affine group. It applies the pointed proposition to the
pointed action `PointedAction.ofGroup b`. That action is `b` on the underlying
scheme, with the identity section as the fixed point. Its weight spaces,
augmentation and augmentation ideal are definitionally those of `b`, so the
pointed conclusions are the first two conclusions of the target.

`coordinateWeightDecomposition_of_pointed` proves all four conclusions of the
target for one action. Beyond the pointed proposition, it assumes two facts.
The cotangent weight spaces `cotangentWeightSpace b` must be independent. For
each character `χ`, the image of `augmentationWeightSpace b χ` under
`cotangentMk G` must lie in `cotangentWeightSpace b χ`. Here `cotangentMk G` is
the quotient map of the augmentation ideal onto its cotangent space, and it is
surjective. The transfer lemma then gives the cotangent decomposition. It also
gives the equality of the image of each augmentation weight space with the
cotangent weight space of the same character. That equality includes the
lifting of cotangent eigenvectors, so no separate lifting argument is needed.

`coordinateWeightDecompositionStatement_of_pointed` proves
`CoordinateWeightDecompositionStatement` at universe `u`. Its hypotheses are the
pointed proposition at universe `u` and the two cotangent facts for every field
`k`, affine group `G`, split torus `S` and actual action `b`. The scope is the
target's scope: any field and any characteristic, with no smoothness,
connectedness, reducedness or finite-dimensionality assumption.

Provenance: the reduction was derived for the proof task of
`CoordinateWeightDecompositionStatement` from the imported Library definitions.
The lattice and transfer lemmas are standard modular-law arguments. The split
between augmentation and cotangent eigenspaces follows the passage from
augmentation to its quotient in Conrad–Gabber–Prasad, *Pseudo-reductive
Groups*, second edition (2015), §3.3, printed pp.107–108 (PDF pp.133–134),
registered source `conrad-gabber-prasad-2015-pseudo-reductive`. That source is
context only; the Lean argument does not follow its text.
