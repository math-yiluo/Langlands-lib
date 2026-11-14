# Unfolding for actual unequal-rank cuspidal pairs

`Langlands.Global.RankinSelbergGlobal.UnequalUnfoldingStatement` is
the unproved, Prop-valued ordinary and dual unfolding assertion from
Cogdell, *Analytic theory of L-functions for GL_n* (2004), §2.2,
printed pp.205–207 (PDF pp.208–210), source
`cogdell-2004-analytic-theory-gln`. The ordinary unfolding starts on
p.205 and ends on p.206; the dual unfolding and its rectangular
integral appear on p.207.

## Objects and uniformity

The statement quantifies over a number field `F : Type u`, with
`CompactSpace (AdeleQuotient F)`, positive ranks `n = r + 1`,
`m = t + 1`, `t < r`, and the Library's actual irreducible
`CuspidalOperatorRealization` objects `T` and `T'`.
The functions `φ` and `φ'` are obtained from every pair of vectors by
the existing `cuspFunction`, which transports the actual continuous
cuspidal functions to the group-scheme adelic carriers.

There exists a nonnegative real bound `C` depending only on these
realizations and ranks. After choosing `C`, the statement quantifies
over every continuous nontrivial unitary adelic additive character
`ψ` trivial on `F`, every vector pair, and the complex parameter.
Thus the half-planes are uniform in the vectors and the choice of
standard character. Using a common nonnegative bound and symmetric
conditions `Re(s) > C` and `Re(s) < -C` merely shrinks the source's
unspecified right and left half-planes; it asserts no optimal bound.

## Ordinary unfolding

Set `W = cuspWhittaker F T ψ v` and
`W' = cuspWhittaker F T' ψ⁻¹ v'`. These are the existing
`generalLinearWhittakerFunction` coefficients with all simple-root
coefficients equal to one. In `Re(s) > C`, the conclusion asserts
Bochner integrability of the actual Whittaker quotient integrand
and the equality

`I(s;φ,φ') = Ψ(s;W,W')`.

The left side uses the projection and rational reductive quotient
measure from `UnequalIntegrals`. The right side uses
`WhittakerIntegrals`, with determinant exponent `s-(n-m)/2`.
Its measure is the pushforward of the actual Haar/counting measure
on `N_m(F) \ GL_m(𝔸)` to `N_m(𝔸) \ GL_m(𝔸)`.
This fixes the unipotent rational quotient to have mass one and
matches the normalization of the Library Whittaker coefficients.
No local-product normalization or Euler identity is asserted here.

## Dual unfolding and absolute convergence

For a function on rank `j`, `dualFunction` means
`f̃(g)=f(w_j ᵗg⁻¹)`. Applied to `W` and `W'`, these are precisely
Cogdell's dual Whittaker functions on p.207, transforming with
characters `ψ⁻¹` and `ψ`, respectively. They are constructed from
the original Whittaker functions rather than supplied as data.

Let `w_(n,m)=diag(I_m,w_(n-m))`. Positive right translation is
`ρ(a)f(g)=f(g a)`. In `Re(s) < -C`, the conclusion is

`Ĩ(1-s;φ̃,φ̃') = Ψ̃(1-s;ρ(w_(n,m))W̃,W̃')`.

The Weyl translation is applied after forming the dual Whittaker
function. The inner matrix of the right side is
`[[h,0,0],[x,I_(n-m-1),0],[0,0,1]]`, with
`x ∈ M_(n-m-1,m)(𝔸)`, as on p.207. The rectangular measure
transports the Library's normalized two-block unipotent Haar,
whose rational quotient has mass one. Its determinant exponent
at parameter `1-s` is `1-s-(n-m)/2`. The left side uses exactly
the existing transpose-inverse dual projection and the same
character parameter `ψ` as the ordinary global integral.

The helper proposition `DualWhittakerAbsolutelyConvergent` has three
clauses: the inner complex kernel is integrable for almost every
outer quotient point; the real function obtained by integrating its
pointwise norm is integrable over the outer quotient; and the
complex outer integrand is integrable there. This spells out
absolute convergence of the iterated integral. It does not infer
inner convergence from the value of a totalized integral, or require
measurability of a chosen quotient section in a product space.

All integrals, measures, matrix maps, and Whittaker coefficients
are the concrete definitions of the two imported definition
modules. Every convergence claim and identity is in the conclusion.
The only additional premise is the stipulated additive-character
condition; no binder supplies analytic estimates, continuations,
unfolding identities, or integral values. This unit states no
equal-rank result, Euler factorization, or proof of unfolding.
