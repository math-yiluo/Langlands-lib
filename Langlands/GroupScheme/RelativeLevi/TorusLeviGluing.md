# Containment and uniqueness for descended torus-Levi witnesses

This derived construction completes containment and uniqueness after an actual
Levi representative of the matching local ranges is available. The base scheme
and universe are arbitrary.

`SubgroupFunctor.CoverDescent.subgroup_range_baseChange` recovers a supplied
closed subgroup from all of its pulled-back ranges along an étale covering
family. One inclusion follows by restriction of points. For the other,
factorizations through the monic closed inclusion on relative tests give
factorizations on the pullback of the cover to any global test scheme.
Subcanonicity of the fppf topology glues these unique lifts to a global
factorization. The equality concerns every test scheme, including nonreduced
tests; it is not a comparison only of geometric points.

`EtaleTorusLeviData.contains_subgroup` shows that the prescribed commutative
group is contained in the descended subgroup condition: each restricted point
lies in its local chosen Levi by that witness's containment field.

`unique_subgroup` assumes that the ambient parabolic group is affine over the
base. It pulls back an arbitrary competing relative Levi containing the
prescribed group to every cover member using the full étale Levi base-change
theorem. Local witness uniqueness identifies each of its pulled-back ranges
with the chosen local range. The preceding recovery lemma then identifies its
global range with the descended subgroup.

`witnessOfLeviRepresentative` takes the local data and an actual
`LeviRepresentative` of their descended range. It retains that representative's
group, inclusion and Levi certificate, and equips them with the containment and
global uniqueness just proved. The result is a `TorusLeviWitness` for the
original prescribed map.

The provenance is internal: the proof composes the local witnesses, actual
relative Levi base change, and sheaf gluing of lifts through a monomorphism.
It does not assume a local-to-global equality principle or any extra
uniqueness hypothesis. It retains the supplied local data and global Levi
representative; it does not by itself discharge the structure statements
needed to construct them.
