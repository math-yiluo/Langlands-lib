# Level naturality on arbitrary connected tests of Harris orbit covers

This is an internal deduction from the actual Harris raw-restriction comparison
and finite orbit covers. It concerns level arrows on arbitrary pointed connected
locally noetherian tests of a supplied family.

The arithmetic carriers have universe zero and retain the Harris CM fields,
central simple unitary data, normalized signature charts and scalar-tower
hypotheses of `HarrisIntegralCMLevelOrbitCoverTestEquivalence`. The family,
dual witness, dual-valued homomorphism and integral order action are supplied.
The tensor/Picard prerequisites, finite Weil transition compatibility,
rational profinite-integer/adele comparison, torsion finite etaleness,
invertibility of torsion orders and finite etale roots of unity remain explicit.

The base `T.left` and test `T'.left` are quasi-separated, connected and locally
noetherian. The test morphism `f : T' → T` is arbitrary in `Over S`. Points `s`
and `t` over the same algebraically closed field, the equality
`t ≫ f.left = s`, and finiteness of the finite-etale fibres at both points are
supplied. An actual orbit cover also retains a reference level `U` with a
nonempty original fixed-level set, as in the existing finite-orbit construction.
There is no finite-etale hypothesis on the test morphism.

Write `rawD` for the original direct level tower on `T'` with the literal action
`(relativeEndRestrict B f).comp a`, `rawEvaluation` for the original
`harrisIntegralCMRestrictionRawClass`, and `Gamma` for the base fundamental group.
For an original Harris level arrow `j : V → Z`, write `transport j` for its
original right-orbit translation. The chosen raw classes `q` and `r` satisfy
`transport j q = r`. This is precisely the condition used by the existing
actual cover transporter.

`harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_postcomp_transport` proves that
the underlying direct level obtained from an actual test-to-cover morphism
`k`, followed by that actual cover transporter, is the original direct-tower
transition `(rawD).map j` applied to the direct level obtained from `k`.

The proof applies the published injectivity of original raw restriction
values. The arbitrary-test equivalence's value formula identifies the left
side with the fibre comparison of the composite scheme morphism evaluated at
`t`. The published `harrisIntegralCMRestrictionRawClass_map` identifies the
right side with original right-orbit translation of the fibre comparison of
`t ≫ k.left`. The actual cover transporter's fibre formula equates these two
values. The comparison uses the original morphism and original tower map.

`harrisIntegralCMTestLevelOrbitMap` defines a map between the direct-level
subtypes whose raw restriction values lie in the specified target monodromy
orbits. Its underlying value is defined to be `(rawD).map j l.val`. To prove
orbit membership, raw restriction compatibility reduces to translation of an
orbit member. A monodromy witness for the input orbit gives the same witness
for the output, because the published raw right translation commutes with
monodromy. No orbit-preservation premise on the direct tower is assumed.

`harrisIntegralCMTestLevelOrbitMap_val` records that literal underlying value.
The identity and composition lemmas follow by subtype extensionality from
the original direct tower's functor laws. These three lemmas explicitly omit
connectedness, local noetherianity and algebraic closure, which their proofs
and subtype maps do not need.

`harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_natural` is the commuting square
in the actual target direct-level subtype. Its source-side operation is
postcomposition of `k` with the actual cover transporter; its target-side
operation is `harrisIntegralCMTestLevelOrbitMap`. Subtype extensionality and
the proved original direct-level transition formula establish the equality.

This comparison concerns changes of level on a supplied pointed connected
test. Naturality under precomposition by test morphisms, disconnected-test
gluing, geometric-point independence, normalized rational-isogeny comparison
and existence of a representing PEL scheme remain open. The contribution does
not prove admissibility, smoothness or division-case projectivity and does
not change `DivisionCMRepresentabilityStatement` or any imported pair.
