# Real characters on supports of square-integrable coefficients

Worker 89. These are internal derived lemmas for the convergence part of
Renard IV.3.3 Lemma (ii). They are not attributed to the book as separately
stated results. The original target is in Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, printed pp.101–102 /
PDF pp.107–108. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The proof below makes explicit the integrability needed when the two
essentially square-integrable representations have independent twists.

The measure is Haar and right invariant on the actual quotient by the center.
The representation `ρ` is irreducible and square-integrable in the published
sense, hence admissible. The lemmas also take an invariant positive form `b`
and compact-open cofinality. Both inputs are supplied from the exact group and
square-integrability hypotheses when the main Schur proof uses these lemmas.

## Local phase equivalences

For an open-kernel homomorphism `a : G →* Multiplicative ℝ`, `schurPhase a t`
is the complex unit character

`g ↦ exp(i*t*toAdd(a(g)))`.

The file proves its homomorphism laws, modulus one, and open kernel. If `a`
is trivial on the center, every such twist has the same central character
as `ρ`. Unitary twisting preserves square-integrability and the positive form.

`eventually_nonempty_phaseEquiv` proves that `ρ` is equivalent to these twists
for all real `t` sufficiently close to zero. Choose `v≠0` and `ℓ=b(v,-)`.
The mixed diagonal integrand for `ρ` and its phase twist is its untwisted
counterpart multiplied by the inverse phase. Its norm is unchanged.
The core integrability lemma supplies an integrable dominating function;
pointwise continuity of the complex exponential and dominated convergence
give continuity of the integral at zero. The positive self Schur relation
shows the value at zero is nonzero. It stays nonzero nearby. The weak Schur
form therefore yields a nonzero intertwiner; irreducibility of both actions
makes it bijective.

## One finite coefficient space

`schurFixedCoefficientMap ρ K` is the actual bilinear coefficient map,
linearized from the tensor product of `K`-fixed vectors and `K`-fixed smooth
functionals into `G → ℂ`. Its range is
`schurFixedCoefficientSpace ρ K`. Admissibility of `ρ` and its smooth
contragredient makes this range finite-dimensional.

Suppose `K ≤ ker(a)` fixes `v` and `ℓ`. If
`e : ρ.Equiv (twist (schurPhase a t) ρ)`, then the phase-multiplied coefficient
is the coefficient with vector `e.symm(v)` and functional `ℓ ∘ e`.
The proof transports the functional through the published smooth dual twist
equivalence and `contragredientMap`. Since the phase is trivial on `K`,
both transported inputs are still fixed by `K`. Thus all the local phase
multiples lie in the same finite-dimensional coefficient space.

## Finite frequencies by Vandermonde

`finite_real_image_support_of_phase_mem` is a general finite-dimensional
function-space lemma. Suppose all sufficiently small phase multiples of a
function `f` belong to a fixed finite-dimensional subspace `M` of `X → ℂ`.
If `a(support f)` were infinite, choose `n=dim(M)+1` points where `f≠0` with
distinct real `a`-values. For a sufficiently small positive `t`, the phase
multiples at `0,t,...,(n-1)t` belong to `M`, and all `t*a`-values lie in
`(-π,π)`.

The complex numbers `zᵢ=exp(i*t*a(xᵢ))` are distinct by injectivity of
the exponential on that strip. Evaluating a linear dependence of the `n`
phase multiples at the chosen points and cancelling the nonzero `f(xᵢ)`
gives the Vandermonde equations `∑ⱼ cⱼ zᵢʲ=0`. Mathlib's Vandermonde theorem
forces every coefficient to vanish. This contradicts the dimension of `M`.

`finite_real_image_coefficient_support` chooses a common open subgroup fixing
the vector and smooth functional and contained in `ker(a)`. The preceding
two arguments then give finiteness of `toAdd(a(support f))` for the actual
smooth coefficient `f(g)=ℓ(ρ(g)v)`.

## Bounding a nonunitary weight

`schurLogNorm η` is the additive real character `log|η(g)|`, written
multiplicatively. It has open kernel whenever `η` does, and is trivial on
the center if `|η|=1` there.

`character_norm_bounded_on_coefficient_support` applies the finite-support
result to this character. The resulting finite real set is bounded above
by some `r`; exponentiation gives a positive bound `C=exp(r)` for
`|η(g)|` whenever `ℓ(ρ(g)v)≠0`. This is a bound on each coefficient's
support; it does not assert a bound for the character on all of `G`.
