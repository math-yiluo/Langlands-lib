# Opposite power coefficients from normalized Gauss relations

This is an internal derived helper for comparing opposite root restrictions of
actual group-scheme homomorphisms over an arbitrary commutative ring `R`.
The module keeps its geometric inputs explicit. It neither constructs root
restrictions for an isogeny nor proves that ambient root cells satisfy those
inputs. It is uniform in the universe of `R` and allows nonreduced rings and
rings with zero divisors.

`HasGaussRelation i xp xm` requires the following normalized relation on every
scheme `Z` over `Spec R`. If `u = 1 + x*y` is a unit of the global-section ring,
there is a point `t` of the supplied commutative group `T` such that

`xp(x) * xm(y) = xm(u⁻¹*y) * (i(t) * xp(u⁻¹*x))`.

The middle factor only has to lie in `T`; the definition specifies no coroot or
compatibility of middle factors under a homomorphism. `SeparatesPositive j yp ym`
says that equality of two products `ym(y) * (j(t) * yp(x))` implies equality of
their last scalar coordinates. It asserts neither openness nor an ambient
rank-one decomposition. `HasPowerFormula f xp yp c q` means
`f(xp(x)) = yp(c*x^q)` on every relative test scheme, with the base coefficient
pulled into its global-section ring. All maps in these predicates are actual
group-scheme homomorphisms.

`pow_eq_of_scaled_inverse_eq` is elementary commutative-ring algebra. An equality
`c*(u⁻¹)^q = v⁻¹*c`, with `c`, `u`, `v` units, gives `u^q = v` by cancelling `c`
and inverting the resulting equality of units.

`coefficient_eq_one` assumes `q > 0` and that the identity
`u^q = v` holds on every commutative `R`-algebra whenever
`u = 1+x` and `v = 1+a*x^q` are units. It proves `a = 1`. The proof takes the
total quotient ring of `R[X]`. Both `1+X` and `1+C(a)*X^q` are nonzero divisors:
their constant coefficient is one, and the imported polynomial criterion
`mem_nonzeroDivisors_of_coeff_mem` applies at index zero. They become units in
the total quotient ring. Its injective map from `R[X]` pulls the assumed identity
back to `(1+X)^q = 1+C(a)*X^q`; comparison of coefficient `q` proves `a=1`.
This argument also covers the zero ring. It uses no field-point criterion for
equality of morphisms or coefficients.

`denominator_pow_eq_of_gauss` assumes a commuting square `i ≫ f = τ ≫ j`, the
source and target Gauss relations, target positive-coordinate separation, and
power formulas of the same natural degree `q` for the positive and negative
maps. The positive coefficient `c` is a base unit; the negative coefficient `d`
is an arbitrary base element. For any relative test and units
`u=1+x`, `v=1+c*d*x^q`, apply the source relation at `(1,x)` and postcompose with
`f`. Apply the target relation at `(c,d*x^q)`. The torus square puts the middle
factor of the first decomposition in the target torus. Coordinate separation
compares their positive coordinates, giving
`c*(u⁻¹)^q = v⁻¹*c`. The elementary cancellation lemma gives `u^q=v`.

`mul_eq_one_of_gauss` applies that denominator comparison to every affine test
`Spec A` over `Spec R`. The canonical global-section isomorphism for `Spec A`
transports the scalars, units, and base coefficients. The all-algebra coefficient
lemma applied to `a=c*d` then proves `c*d=1`, for `q>0`. In particular, no prior
unit hypothesis on the negative coefficient is needed.

Finally, `opposite_maps_eq_of_gauss` considers two homomorphisms with the same
positive unit coefficient and the same positive degree. Their torus restrictions
may use distinct supplied maps. Each negative restriction is assumed to have a
power formula of that degree in the same target negative coordinate. The two
applications of `mul_eq_one_of_gauss` and unit cancellation identify the negative
coefficients. The imported `hom_ext_rootPoint` then proves equality of the actual
negative-root morphisms on all relative test schemes.

The provenance is the internal calculation just described, using Mathlib
polynomial and total-quotient-ring results and the Library's `LocalSplitCell`
point and extensionality interfaces. The module supplies a conditional comparison
step for the reductive-isogeny rigidity proof. Constructing normalized opposite
root maps, proving the ambient coordinate-separation and Gauss hypotheses, and
deriving compatible power formulas from arbitrary-base isogenies remain separate
obligations.
