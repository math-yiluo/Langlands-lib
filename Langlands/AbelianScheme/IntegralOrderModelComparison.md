# Original rational algebra actions and their integral order models

Let `A` be an actual abelian scheme over any base `S`, let `R` be a rational
algebra, and let `O` be a full integer subalgebra with a supplied integer
basis. Suppose `α : R →ₐ[ℚ] End0 A` is the original rational algebra action
and `M` is an `IntegralOrderModel` of its restriction to `O`. The model
retains the actual abelian scheme `M.B`, its integral order action, the actual
forward isogeny and inverse-multiple map, and equivariance of the forward
map's rationalization on every order element.

`IntegralOrderModel.rationalExtension_intertwines` extends that equivariance
to every element of the original rational algebra. The proof compares two
rational-linear maps into the actual rational Hom group: compose the original
action with the rationalized forward map, or compose that map with the full
rational extension of the model's integral action. The rational basis
extended from the integer lattice determines both maps. On each basis
vector the equality is exactly the model's order equivariance, using the
published `integralActionRationalExtension_coe` formula.

`rationalAlgebraIso` uses the model's actual integral inverse-multiple data
to obtain an isomorphism in the published category of actual abelian schemes
with rational algebra action. The forward map is the rationalization of the
actual quotient isogeny. The inverse is the rationalization of the actual
inverse-multiple map scaled by the inverse of its positive integer multiple.
The two simp lemmas retain these formulas. `rationalAction_classOf` gives
equality in the existing quotient by actual equivariant rational
isomorphisms.

This is an internal deduction from the published full-order extension and
rational-action interfaces and the supplied integral order model. It changes
neither the original action nor the rational-isomorphism quotient. It adds
no finite-basis, field-base or noetherian assumption: those are only needed
by the separate geometric model construction, not by this comparison.
Polarization, determinant, relative dimension, level data, naturality of
moduli comparisons and representability are separate obligations.
