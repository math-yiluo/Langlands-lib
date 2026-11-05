# Finite chamber charts with prescribed generators

This internal refinement retains a supplied family of chamber generators.
Let `Δ` be any finite type, let `X` be any additive commutative group, and let
`pair α : X →+ ℤ` be integral pairings. The family `gen : Δ → X` has strictly
positive diagonal pairings and zero off-diagonal pairings. No freeness,
finite generation, primitivity or nonempty-label assumption is made.
The label, lattice and ambient group universes are independent.

`Langlands.chamberCoordinates pair gen B x` is the natural-valued function
whose `α` coordinate is the integer quotient
`(pair α x + B) / pair α (gen α)`, converted to a natural number.
`chamberRemainder` subtracts the sum of these coordinates times the given
generators. Both definitions are available for arbitrary data; their
Euclidean interpretation uses the stated positivity and chamber hypotheses.

`pair_chamberRemainder` assumes `-B ≤ pair α x` for every label and identifies
the remainder's pairing with
`(pair α x + B) % pair α (gen α) - B`.
The shifted pairing is nonnegative, so conversion of the integer quotient
to a natural number preserves it. Additivity and off-diagonal vanishing
reduce the sum to its diagonal term, and integer division gives the identity.

`exists_finite_prescribed_chamber_representatives` proves that for every
integer bound `B` there is a finite set `R ⊆ X` such that every lower-bounded
`x` is

`r + (∑ α, chamberCoordinates pair gen B x α • gen α) + z`,

where `r ∈ R` and all pairings of `z` vanish. The Euclidean remainders lie
in a finite product of integer intervals. The proof selects one actual
element for each attained tuple by `Function.invFunOn`; the difference
from the remainder has all pairings zero. This does not require the
bounded subset of `X` itself to be finite.

`exists_finite_prescribed_chamber_cartan_cover` additionally takes a group
`G`, an arbitrary subset `K`, a homomorphism `e : Multiplicative X →* G`,
and a finite set `F₀ ⊆ G`. It assumes that the common pairing kernel maps
into the full abstract center, and that every `g` has a factorization
`k₁ * e(x) * f * k₂` with `k₁,k₂ ∈ K`, `f ∈ F₀` and all pairings of `x`
bounded below by `-B`. It gives a finite set `T` and factorizations

`g = k₁ * e(∑ α, n α • gen α) * t * k₂ * z`,

with `t ∈ T`, `z` in the full abstract center, and the **same prescribed**
`gen`. The proof takes `T` to be the image of `R × F₀` under
`(r,f) ↦ e(r) * f`. Images of lattice elements commute with one another,
and the pairing-kernel term is central, which gives the displayed order.
The ambient group and residual elements need not commute. No topology or
compactness hypothesis is needed.

The proof is adapted from Worker 349's published `finiteChamberLattice`
and `finiteChamberCartanCover`: their standard-vector existence step is
replaced by an explicit generator argument, and the Euclidean coordinates
and remainder are exposed as definitions. The generic algebraic argument
is derived internally, with no additional literature claim. The original
declarations and their pairs are unchanged. This refinement supplies no
actual reductive Cartan data, simultaneous compact open level, or uniform
coefficient support; those remain separate application obligations.
