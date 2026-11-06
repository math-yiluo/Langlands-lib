# Invariant forms from actual parabolic presentations

This internal construction continues the invariant-form adapters for Renard
VII.2.6. It derives the full actual-parabolic modular identity from a compatible
root presentation and unimodularity of the specified Levi, and uses the
presentation coverage built into normalized-exponent temperedness. It does not
prove any of the three exact VII.2.6 statements.

The field `k : Type u` is a nonarchimedean local field with its supplied Hausdorff
topology. The actual connected reductive group `G`, parabolic map `p`, rational
Levi map `l`, geometric radical map `r`, and Levi-first multiplication
isomorphism are the existing Library objects. All rational-point topologies
and subgroup topologies are the published canonical ones.

`continuous_projection_of_presentation` chooses the cocharacter in the
presentation's specified split component. The presentation identifies its
parabolic and centralizer subgroup functors with the supplied parabolic and
Levi images. `ParabolicRootPresentation.range_comp_radical_eq` identifies the
supplied radical's image with its dynamic identity-limit subgroup, using
connected reductivity of the specified Levi. Evaluation on the identity test
scheme gives equality of all three literal point subgroups. Rewriting the
semidirect decomposition transports the published continuity theorem for the
dynamic projection.

`radical_isLimitOfCompactSubgroups_of_presentation` uses the same radical
identification and the published dynamic compact-open containment theorem.
For every compact subset of the actual radical it supplies a compact subgroup
containing that subset.

`modularCharacter_of_presentation` assumes unimodularity of the actual group
`M(k)` with its own canonical topology. The published `leviPointsEquiv` and
`modularCharacter_continuousMulEquiv` transport this to the literal Levi image.
The compact containment result implies that inner automorphisms of the
radical have trivial Haar modulus. The continuous semidirect-product formula
then identifies the modular character of every element of the full parabolic
image with its full positive action modulus on the radical. Closedness and
second countability follow from the supplied actual maps and connected
reductivity. No universal dynamic-centralizer or dynamic-radical theorem is
assumed.

`temperedIrreduciblePresentationForm` retains four explicit inputs: the exact
`TemperedIrreducibleDiscreteSeriesStatement`,
`RationalReductiveUnimodularityStatement`, its existing
`StandardCocharacterStatement` premise, and
`ArbitraryParabolicQuotientCompactStatement`. The discrete-series assertion
supplies the actual Levi representation, its square-integrability for every
Haar measure on its full-center quotient, and an injective intertwiner into
the exact `leviInductionFunctor`. The proved split-component existence theorem
chooses a split component of this Levi. Temperedness supplies a compatible root
presentation for that exact triple. The modular identity just derived supplies
the induction adapter's modulus premise. The existing square-integrable
unitarity adapter supplies a Levi form, the compact-quotient induction adapter
supplies the induced form, and injective pullback supplies a positive invariant
form on the original representation carrier.

The field and original carrier universes `u` and `v` remain independent.
The construction preserves the original smooth action and all-Haar
square-integrability predicate. Neither compatible presentation existence nor
the full parabolic modular identity is an additional premise of the final
constructor. Reductive unimodularity, standard cocharacters, quotient
compactness, and the exact discrete-series assertion remain proof obligations
through its explicit inputs. This is a derived composition of the cited
Library declarations, with no new claim of a literal literature theorem.
