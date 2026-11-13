# Exact unramified descent of supplied neutral integral models

This internal result connects smooth full-model descent with recovery of an
actual relative identity-component model. It retains the smooth-model descent
assertion and the supplied upstairs models as hypotheses. The prescribed-point
split-torus theorem remains open.

Work in arbitrary universe `u` over a nonarchimedean local field `F`, in either
characteristic. Write `K` for `inertiaFixedField F` and `A` for
`fixedFieldIntegers F`. The generic group `G` is geometrically connected. The
supplied upstairs data `E` consists of smooth affine full and neutral integral
models of the actual base change `G_K`, their compatible inclusion, and the
all-test relative identity-component property. No separate stability assumption
on the neutral integral-point image is imposed.

`UnramifiedComponentModelRecovery D E` records actual full and neutral
isomorphisms from the unramified base changes of downstairs component-model data
`D` to `E`. Both isomorphisms respect the original generic identifications over
the identity of `G_K`. The inclusion square commutes with the actual pullback of
`D.inclusion.hom`. `ofFull` constructs this package from a supplied compatible
full-model recovery isomorphism, using `baseChangeNeutralIso` and its inclusion
square.

`UnramifiedNeutralModelDescentStatement` says that, assuming
`UnramifiedSmoothModelDescentStatement`, coefficient stability of the full-model
integral-point image of `E` implies existence of downstairs data `D` and a
nonempty recovery package. Its theorem `unramifiedNeutralModelDescent` proves
that precise conditional assertion.

The proof first applies the supplied smooth-model descent assertion to
`E.full`. It obtains a smooth downstairs full model with a compatible upstairs
recovery isomorphism. The published `relativeComponentModelDataOfSmooth`
construction over the discrete valuation ring of integers of `F` supplies its
affine relative identity component, preserving the full model and original
generic identification. `ofFull` then recovers the supplied upstairs neutral
model and the commuting inclusion square.

The additional theorems `full_integralPoints_eq` and
`neutral_integralPoints_eq` give literal equality of the original upstairs
subgroup images under the recovery isomorphisms. Their `_eq_comap` variants
identify the downstairs images with the inverse images of the supplied upstairs
images under rational scalar extension. `neutral_galois_stable` applies the
necessary direction of smooth-model descent to the recovered neutral model.
Thus neutral coefficient stability is a consequence of full-model recovery.

The fixed-point corollary takes an actual semilinear `G(K)`-set, a coefficient-
fixed point, and the supplied identification of `E.full.integralPoints` with
the intersection of the character-valuation kernel and the point stabilizer.
It uses `exists_descent_of_fixedPoint_integralPoints` and then the same component
construction and recovery. It retains both the supplied models and the
smooth-model descent assertion.

All results are internal deductions from the published relative-component
construction and functoriality, actual unramified model and integral-point
comparisons, and the coefficient-fixed stabilizer descent helper. This module
constructs no upstairs parahoric model or fixer identification, proves no smooth
full-model descent assertion, and supplies no residue parabolic, lifted torus or
special apartment. Those remain prerequisites of the host theorem.
