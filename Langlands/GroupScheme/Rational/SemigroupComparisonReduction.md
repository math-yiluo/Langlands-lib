# Structural reduction of all semigroup comparison properties

Worker 1372. Internal assembly from the actual normal radical reduction,
radical existence and stability, algebraically closed radical transport, identity
components and fpqc reflection.

The only structural premise is the existing
`NormalSemigroupRadicalPrerequisites`: radical intersection, the five normal
reductive prerequisites, and solvable fixed-containment connectedness. This
module proves none of these seven components.

The module first proves that every generated semigroup subgroup lies in the
actual identity component. Its smooth connected representative factors through
the open and closed identity-component inclusion. Equivariant closed-inclusion
transport then identifies its inverse image with the semigroup subgroup for
the induced action on the identity component.

Over an algebraically closed field with smooth connected affine ambient and
subgroup schemes, `semigroup_comap_eq_of_normal_connected` chooses their actual
unipotent radicals. The smoothness of the split acting torus supplies full
radical stability through `IsUnipotentRadical.isStable`. Actual radical
quotient existence supplies pseudo-reductive quotients. The proved
`IsPseudoReductive.isConnectedReductive_of_isAlgClosed` from
`Reductive.AlgebraicallyClosedPseudoReductive` makes both quotients connected
reductive. The existing supplied-quotient normal radical reduction constructs
the compatible quotient actions and lifts the conditional reductive
comparison. Only the seven-component structural premise and zero membership
remain explicit; no general perfect-field comparison is assumed.

`semigroup_comap_eq_of_normal_algebraicallyClosed` removes ambient
connectedness. The connected source inclusion factors through the ambient
identity component. Cancelling its monomorphism identifies the full range of
the factor with the inverse image of the original range. Thus normality pulls
back, while closedness follows from the closed composite and equivariance
follows by cancellation. The identity-component semigroup equality and the
preceding connected theorem give the original inverse-image equality.

`semigroup_comap_eq_of_normal` removes algebraic closedness of the original
field. It base changes to the algebraic closure in the same universe. Actual
smoothness, affineness, geometric connectedness of the smooth connected affine
source, closedness, all-test normality and equivariance persist. Character
pullback preserves zero membership. The algebraically closed comparison and
the published semigroup base-change equality give containment after this
faithfully flat quasi-compact base change. Fpqc reflection in the represented
semigroup subgroup of the source descends that containment. Equivariant
functoriality gives the reverse containment. No radical base-change theorem
or descent of a radical representative is assumed.

Finally `semigroupComparison_of_structuralPrerequisites` has the exact existing
`SemigroupComparisonStatement` as its conclusion, conditional on the displayed
bundle. The published functoriality and smooth-quotient proofs supply the first
two components. For intersection comparison it uses the published zero-excluded
case, the conditional solvable case with the bundled connectedness premise,
and the new normal case. Every field, universe and all three alternatives of
the existing proposition are retained.

All equalities are full all-test subgroup-functor equalities, including on
nonreduced tests. The main theorem is conditional. It does not prove any
structural component of the prerequisite bundle and does not complete the host
proof task until those independent propositions have been proved and published.
