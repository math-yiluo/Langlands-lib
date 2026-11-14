# Parabolic conjugacy from a normalizer section on an open

This derived construction shrinks a supplied local normalizer section to obtain
conjugacy on a Zariski open of the original base. It is an intermediate input to
local Borel conjugacy, with Lie containment retained as an explicit premise.

Let `i` and `j` be relative parabolic subgroups of a reductive group scheme over
an arbitrary scheme `S`, both containing a closed fibrewise maximal relative torus
`t : T → G`. Assume `RelativeParabolicLieContainmentStatement`. For a field-valued
point `x : Spec k → S`, suppose `x` factors through an open `V` by a specified
`a`, and a section `nV ∈ G(V)` belongs to the full subgroup-functor normalizer of
`t`. Suppose `a ≫ nV` conjugates the ranges of `i` and `j` on every refinement of
`Spec k`, in the sense of `IsConjugatingPoint`.

`relativeParabolic_exists_open_conjugatingPoint_of_local_fieldPoint` produces
an open `U` of `S` containing the image of the unique closed point of `Spec k`
and an actual section `nU ∈ G(U)` in the full normalizer, conjugating those two
ranges on every refinement of `U`.
`relativeParabolicLocalNormalizerConjugacyOfLocalFieldPoint` chooses both `U`
and `nU`, retaining membership of the point, normalization and conjugacy.
No algebraic-closure assumption on `k`, splitting assumption or geometric-point
lifting assertion is included in this construction.

The proof pulls the group, parabolics and torus back to `V`. The canonical
point equivalences turn `nV` into a global section of the pulled-back group and
transport its normalizer membership and the conjugacy at `a.left`. Relative
parabolicity, the relative torus property, closedness, fibrewise maximality and
torus containment persist under this base change. The conditional global-section
spreading theorem `relativeParabolic_exists_open_conjugatingPoint_of_fieldPoint`
then gives a smaller open `W` of `V`. Its composite open immersion into `S` has
image `U` and canonically identifies `W` with `U.toScheme`. Transporting the
restricted section and conjugacy along this isomorphism gives the result over
the original base. Normalizer membership persists by restriction. This argument
uses the existing point-equivalence, base-change and open-immersion APIs; it
asserts no new original-source theorem.
