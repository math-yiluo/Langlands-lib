# Complete-field realization of a multiplicative seminorm

`Langlands.Analytic.seminormRealization` proves
`SeminormRealizationStatement` at every universe `u`. Given a
commutative ring `A : Type u` and a nonarchimedean multiplicative ring
seminorm `q`, it constructs one complete ultrametric normed field
`L : Type u` and a unital ring homomorphism `f : A →+* L` with
`‖f a‖ = q a` for every `a`.

The proof first regards `q` as a valuation `v : Valuation A ℝ≥0`.
Nonnegativity supplies the subtype values, multiplicativity supplies
the valuation's multiplication law, and the strong triangle inequality
supplies its addition law. Mathlib makes the support `v.supp`, the zero
set of this valuation, a prime ideal. Thus `D = A ⧸ v.supp` is an
integral domain without any domain or reducedness assumption on `A`.

The valuation descends to `D` using `Valuation.onQuot`. Its value
vanishes precisely at zero: represent an element of `D` by an element
of `A` and apply `Ideal.Quotient.eq_zero_iff_mem`. Consequently every
nonzero divisor of `D` has nonzero valuation. The descended valuation
therefore extends to `R = FractionRing D` using
`Valuation.extendToLocalization`, and its values on the image of `D`
are unchanged.

On the field `R`, composing this valuation with the inclusion
`ℝ≥0 → ℝ` gives an absolute value. Multiplicativity and nonnegativity
come from the valuation; `Valuation.zero_iff` gives definiteness; and
the strong triangle inequality implies the ordinary triangle
inequality. The type `N = WithAbs abv` equips `R` with the norm from
this absolute value. The valuation's strong triangle inequality also
makes `N` ultrametric.

The evaluation map from `A` to `N` is the composite of the quotient
map, the fraction-field inclusion and the inverse of
`WithAbs.equiv`. The localization valuation formula proves its exact
norm identity with `q`. Finally, `L` is the actual metric completion
of `N`, with Mathlib's complete normed-field structure. The strong
triangle inequality extends to `L` by two-variable completion
induction: its defining weak inequality is closed, and it holds on
the dense image of `N`. Composing evaluation with the completion ring
homomorphism preserves the exact norm identity because that
inclusion preserves norms.

Quotients, fraction fields, `WithAbs` and metric completion all remain
in the universe of `A`. The construction therefore includes `u = 0`.
It uses no nontrivial valuation assumption or topology on the source
ring. Normalization of the supplied `MulRingSeminorm` makes the prime
quotient nonzero; no additional hypothesis on the source is needed.
The proof uses only `propext`, `Classical.choice` and `Quot.sound`.

This proof adapts Worker 74's published construction in
`Langlands.Geometry.Analytic.Spectrum.ResidueField.Definitions`,
removing its spectrum-point and coefficient-algebra inputs. Its
provenance is this internal generalization and Mathlib's valuation,
absolute-value and completion APIs. It does not supply the
tensor-seminorm construction or prove field amalgamation.
