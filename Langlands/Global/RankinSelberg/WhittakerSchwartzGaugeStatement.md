# A weighted Whittaker–Schwartz estimate for analytic decay classes

This internal statement isolates a substantial analytic input for the
equal-rank Rankin–Selberg unfolding. Its motivation is the gauge
majorization and resulting convergent integral in Jacquet–Shalika,
*On Euler products and the classification of automorphic forms I* (1981),
§4.5, printed pp.550–551. The statement is a proposed sufficient analytic
generalization to the Library's `WhittakerDecayClass`; it is not presented
as a verbatim theorem of that source, and this module contains no proof.

`HasCentralPowerBound F r V` means that one real exponent `β` works for
every function `f` of the complex function space `V`: a constant `B ≥ 0`
depending on `f` bounds `‖f(g)‖` by `B |det g|^β` on the entire adelic
group `GL_{r+1}(𝔸)`. In particular, this applies to every iterated
archimedean derivative that remains in `V`.

`WhittakerSchwartzBound F r V` asks for a nonnegative real threshold `C`
such that

`∫ ‖W_f(g)‖ ‖Φ(e_n g)‖ |det g|^σ dg < ∞`

for every `σ > C`, every standard additive character, every `f : V`,
and every Schwartz–Bruhat function `Φ` on adelic row vectors of length
`n = r + 1`. The integral is a nonnegative lower integral on the actual
quotient `N_n(𝔸) \ GL_n(𝔸)`, evaluated at quotient representatives with
the Library's `whittakerQuotientMeasure`. The coefficient `W_f` is
`Unfolding.whittaker` with all simple-root coefficients equal to one.
The threshold may depend on the field, rank and space, but is uniform
over the character, `f` and `Φ`.

`WhittakerSchwartzGaugeStatement.{u}` universally quantifies the
implication from `WhittakerDecayClass F r V R` and
`HasCentralPowerBound F r V` to `WhittakerSchwartzBound F r V`.
It retains the compactness hypothesis on the additive Adele quotient
and the universe of the number field. A decay class supplies continuity,
rational invariance, finite level, boundedness on determinant bands,
and a real-linear family of archimedean right derivatives on `V`.
No central-growth bound is implicit in that class: it is explicitly
required here to obtain a single convergence threshold.

The intended consumers are the spaces of cusp functions of an actual
cuspidal realization and their transpose-inverse transports. Their
fixed central-power exponents come from `CuspCentralBound`, so this
formulation permits both primal and dual estimates without requiring
a new contragredient cuspidal realization.
