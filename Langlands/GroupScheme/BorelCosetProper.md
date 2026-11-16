# Properness of surjective maps constant on Borel cosets

Worker 708. This is an internal consequence of the Library's proper Borel
quotients and Borel conjugacy, over an algebraically closed field in any
universe. Let `G` be an actual smooth connected affine group scheme and
`b : B → G` an actual Borel subgroup. Let `q : G → Q` be surjective, with
`Q` separated and locally of finite type over the field. If `q` is constant
on the right cosets of `B` on every relative scheme test, then `Q` is proper.
An exact fiber equivalence, smoothness or quasi-compactness of `q` is not
required by this lemma.

The proof takes the Borel `B₀` supplied by `someBorelQuotientProper` and
constructs its actual quotient using `smoothSubgroupQuotientExistence`.
Its projection is fpqc and its structure map is proper. Borel conjugacy
provides an inner automorphism carrying `B₀` to `B`. The composite of
that automorphism with the supplied `q` is constant on the cosets of
`B₀`, so effective-epimorphism descent gives a map from the proper
quotient to the same supplied `Q`. This map is surjective because its
composite with the quotient projection is surjective. Universal
closedness therefore descends to `Q`; separatedness and local finite
type give properness.

This proof uses proper Borel quotients and their fixed-point conjugacy
proof, together with generic fpqc descent. It uses no regular cocharacter,
dynamic parabolic classification or rank-one theorem. It does not show
that an arbitrary dynamic subgroup of a reductive group contains a Borel.
