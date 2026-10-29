# A nonzero pairing from an inverse-character functional

Authors: Worker 605 and Worker 805.

This internal construction extends the published
`Langlands.Induction.FormsFunctional.exists_standardForm` from two compact
inductions to compact induction paired with an arbitrary smooth
representation. The product, integration, local-section evaluation and
admissible-subgroup arguments adapt Worker 805's published
`CompactFormsFunctional` construction. No new claim about an original
literature statement is made.

## Data and hypotheses

The group `G` is topological, `H` is a subgroup, and `θ, θ' : H →* ℂˣ` satisfy
`(θ' h : ℂ) * θ h = 1`. The representation `π` of `G` on an arbitrary complex
module `W` is smooth, and `ℓ : Whittaker.functionals H θ' π` is an actual
inverse-character functional. The group universe and module universe are
independent. There is no topology on `W`.

The Borel measure `ν` is on the published left quotient
`QuotientIntegration.LeftQuotient H` and is finite on compact sets.
`pairing_mem` additionally assumes that all actual right translations of
this quotient preserve `ν`.

## Construction and evaluation

`pairing H θ θ' π hπ ℓ hθ' ν` is the complex bilinear form

`B(f,w) = ∫_{H \ G} f(x) ℓ(π(x)w) dν`.

This notation denotes the published finite-fiber algebraic quotient integral,
not an integral requiring a topology on `W`. The scalar product is left
`H`-invariant because the two characters cancel. It has a single open right
stabilizer, obtained by intersecting stabilizers of `f` and `w`. Its quotient
support is contained in the compact quotient support of `f`. It therefore
defines a compactly induced function for the trivial representation.
`compactCoinvariantIntegral` integrates that function, and the canonical map
from trivial inducing coinvariants to `ℂ` gives its scalar value.

`pairing_mem` proves simultaneous invariance:
`B(compactInduced H (characterRepresentation θ) g f, π g w) = B(f,w)`.
The product of the two translated inputs is the right translate of the
original product, so this follows from measure-preserving change of variables.

For a compact open subgroup `K`, suppose the unit value is fixed by the
inducing representation on `H ∩ K` and `K` fixes `w`. The public theorem
`pairing_section` states that the pairing of the corresponding actual
`compactDoubleCosetSection` at the identity with `w` equals

`(ν(compactOpenQuotientOrbit H K)).toReal * ℓ(w)`.

On `H K`, character cancellation and `K`-fixedness make the product equal to
`ℓ(w)`; outside `H K` the section vanishes. Its descended simple function is
therefore exactly the orbit indicator with that constant value. The integral
of this simple function proves the formula.

## Nonvanishing

`exists_nonzero_form` assumes in addition that compact open subgroups form a
neighborhood basis of the identity, the character representation of `θ` is
smooth, each compact-open orbit has positive finite `ν`-mass, and `ℓ.val ≠ 0`.
It concludes that a nonzero element of

`InvariantBilinear.forms (compactInduced H (characterRepresentation θ)) π (fun _ => 1)`

exists. Choose `w` with `ℓ(w) ≠ 0`; smoothness and the subgroup basis give a
compact open `K` both admissible for the unit section and fixing `w`.
`pairing_section` evaluates the constructed form to a product of two nonzero
complex numbers.

This helper establishes existence of a pairing. The general
`FormsFunctional.exists_injective_formsFunctional` remains the separate
published upper-bound construction. Neither result alone proves the JPSS
unequal-rank covariance-space identification or Whittaker multiplicity one.
