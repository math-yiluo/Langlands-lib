# Effective descent of prescribed-torus local Levi witnesses

Worker 638.

This is an internal derived construction toward
`RelativeTorusLeviStatement`. It composes the actual local witness data in
`TorusLeviLocal`, the radical transport theorem in `UnipotentRadicalDescent`,
and the effective descent construction in `LeviCoverDescent`. It retains
`DynamicRelativeLeviStatement` and `RelativeUnipotentRadicalStatement` as
explicit proposition inputs and does not prove either.

`TorusDynamicPresentation.isRelativeParabolicSubgroup` uses the supplied
dynamic structure statement to recognize the represented dynamic parabolic
as a relative parabolic subgroup. Reductivity supplies smoothness and
affineness of the ambient group. The existing `dynamicBaseRepresentability`
constructs actual representatives of the dynamic unipotent and centralizer
functors. Applying the dynamic statement to these representatives and the
given parabolic representation gives the conclusion.

`EtaleTorusLeviData.leviRepresentative` takes local prescribed-torus
presentations and Levi witnesses on an étale cover, the two structure
statements above, reductivity of the global ambient group, and the existing
relative parabolic predicate for the global inclusion. It also takes
`CoverDescent.IsMatching` for the family of local witness ranges; this means
compatibility on every relative test scheme.

The result is an actual `LeviRepresentative` of
`CoverDescent.subgroup` of those ranges. It consists of a global group
scheme and inclusion, equality of its all-test range with the descended
subgroup, closedness, and the unchanged `IsRelativeLeviSubgroup` certificate
for that inclusion. The base scheme and universe are arbitrary. Affineness
of the global parabolic follows from the supplied parabolic predicate.

The proof chooses a global radical from the supplied radical statement.
Each local Levi witness supplies its own radical and actual Levi-first
multiplication isomorphism. Étale transport makes the pullback of the global
radical a full relative radical on each cover member. The local dynamic
presentation gives local parabolicity by the first theorem, and reductivity
persists under base change. Applying the radical statement on that member
therefore identifies the two radical ranges, by comparing both with its
chosen radical. Closedness of each local Levi inclusion also gives its
all-test representation. These data are exactly the inputs of
`leviRepresentativeOfEtaleCover`, which constructs the global representative
and descends its Levi property.

This construction supplies the global Levi predicate, but makes no claim
here about torus containment or uniqueness of the descended inclusion.
Matching, the local presentations and witnesses, and both structure
statements remain explicit inputs. The unchanged full torus–Levi target is
a separate proof obligation.
