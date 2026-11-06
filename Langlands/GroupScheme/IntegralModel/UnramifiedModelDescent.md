# The original model image under actual maximal-unramified base change

Let `F` be any nonarchimedean local field and `M` a supplied integral model
of `G/F` over the actual valuation integers of `F`. All types have an
arbitrary common universe `u`; equal and mixed characteristic are included.

`baseChangeUnramified` constructs the actual coefficient base change of
`M` to `fixedFieldIntegers F`, the integer ring in the separable inertia
fixed field. It uses the published inclusion of integer rings induced by
the extension of the canonical base valuation to `fixedFieldValuation F`.
The generic group is the existing coefficient base change of `G`, and its
identification is obtained from the supplied `M.genericIso` by the existing
`IntegralModel.baseChange` construction. No local-field structure on the
inertia fixed field is assumed.

`unramifiedIntegerRange_intersection` proves that an element of `F` maps
into this actual integer ring precisely when it belongs to the original
integer ring. The proof identifies both inclusion ranges with valuation
at most one and applies the published valuation-extension comparison.
The general original-image descent theorem then proves
`mem_integralPoints_rationalExtend_iff_unramified` and
`integralPoints_eq_comap_baseChangeUnramified`. These refer to the
existing `rationalExtend` and the original generic-image subgroups.
`unramifiedIntegralPointExtend` restricts this actual homomorphism to
these subgroups; its forward coercion is exactly `rationalExtend`.

For an affine generic group, suppose `B` is supplied base-field building
data and `C` is supplied integer-normalized building data over the same
actual inertia fixed field. Suppose also that `e` is an injective map
between their existing reduced quotients, equivariant for the existing
rational actions along `rationalExtend`. At any base point `z`, an equality
between the integral image of `baseChangeUnramified` and the actual
upstairs norm-one stabilizer of `e z` implies
`M.integralPoints = B.compactStabilizer z`. The proof takes the preimage
of the given equality under the actual rational extension, uses the proved
original-image preimage equality, and applies the published exact
maximal-unramified norm-one stabilizer descent theorem.

This is an internal derivation from the published separable inertia-field
valuation, coefficient base change, original-coordinate image descent and
building stabilizer descent. No new literature claim is introduced.
The construction discharges the algebraic descent step for the original
supplied model. The upstairs stabilizer equality and injective equivariant
building map are explicit inputs. It does not construct either of them,
a metric, a special point or a building comparison.
