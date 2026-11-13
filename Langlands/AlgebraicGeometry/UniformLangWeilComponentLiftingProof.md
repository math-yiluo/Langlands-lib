# Uniform lifting over the finite target components

`Langlands.AlgebraicGeometry.uniformLangWeilComponentLifting.{u}` proves
`Langlands.AlgebraicGeometry.UniformLangWeilComponentLiftingStatement.{u}`.
The target's three clauses are implications from the uniform Lang–Weil
estimate. This proof leaves that estimate as an explicit premise.

The helper `uniformLangWeilComponentFiniteFieldPointLifts` first obtains local
noetherianity of the target from its finite-type structure map to the lifted
integer spectrum. Its actual connected-component index is finite, by
`finite_componentIndex_of_compact`. For each component it uses the existing
open component scheme, full inverse-image source scheme, restricted
morphism and selected smooth chart dimension. The component-geometry proof
gives the full pure residue-fibre property with that selected dimension.
The actual restrictions retain smoothness, separatedness, quasi-compactness
and geometric connectedness under their pullback squares; local finite type
follows from smoothness, and surjectivity from geometric connectedness by
Mathlib's instance. Their target component satisfies the helper's finite-type
hypotheses over the integers: its structure map is the open inclusion
followed by the original structure map, a composite of maps locally of finite
type; and its underlying space is compact, because the open inclusion into
the locally noetherian target is quasi-compact and the target is compact.

Apply `uniformLangWeilLargeFiniteFieldPointLifts` to every restriction. This
published helper already handles arbitrary finite fields of values, using an
integer affine-line enlargement to avoid replacing the finite field by a
possibly smaller image residue field. If its positive component constants
are `C_c`, set `C = 1 + ∑ c, C_c`. The sum is finite and nonnegative, so `C`
is positive, dominates every `C_c`, and its square dominates each component
square.

For a point `p : Spec K ⟶ B`, choose the component containing the image of
the unique point of `Spec K`. Every point of `Spec K` has that same image
component. The universal property of the actual component open immersion
therefore factors `p` through its component scheme. The component lifting
helper produces a point in the full inverse-image source scheme.
Composing with its inclusion and using the restriction square gives the
required lift to `Y`. If the target is empty, the finite sum is zero and
`C = 1`; the argument cannot be supplied a field-valued point, so no special
nonemptiness assumption is needed.

`uniformLangWeilComponentHenselianPointLifts` takes the same constant,
reduces a `Spec R` point along the given surjective map to `K`, obtains a
finite-field lift, and applies the published
`PointTopology.exists_smooth_lift_of_residue_point` to the whole original
morphism. No factorization of the whole `Spec R` through a component is used.

`PointTopology.uniformLangWeilComponentHenselianRingPointLifts` applies the
preceding construction to the underlying schemes. The specified coefficient
algebra homomorphism supplies the temporary `R`-algebra structure on `K`.
The lift's structure map agrees with the original `A`-structure by the
over-category compatibility equations of the morphism and the point.
`Over.homMk` and `RingPoint.ext` then give the actual relative lift and its
required equality.

The final theorem packages the outputs of these three constructions as the
three existential statements, keeping arbitrary common universe `u`.
The derivation is internal to the componentwise argument in Conrad's
Theorem 4.5, printed pp.12–13, and uses the already implemented lifting
helpers and geometric component constructions. It proves no Lang–Weil
estimate, arithmetic model existence or adelic openness, and it does not
remove the target's absolute finite-type hypothesis over the integers.
