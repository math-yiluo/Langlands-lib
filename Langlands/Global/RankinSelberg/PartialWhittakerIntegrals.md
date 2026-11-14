# Unramified-place data for the global Euler factorization

This module defines the objects that the partial Euler factorization of the global
Rankin–Selberg Whittaker integrals needs at the finite places outside a finite set `S`.
The source is J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), registered
as `cogdell-2004-analytic-theory-gln`. The relevant pages are §2.2, printed p.206 (PDF
p.209), where the Whittaker functions of factorizable cusp forms factor and the global
integral becomes a product of local integrals, and Theorem 3.3, printed p.215 (PDF
p.218), which computes the unramified local integrals with the normalized
`GL(𝒪_v)`-fixed Whittaker functions. The objects below are the Library's actual groups,
functions and measures. All of them are concrete definitions; this module asserts no
convergence and no identity.

The ranks are `n = r + 1` and `m = t + 1` with `t < r`. `Points F n` is the Library's
group-scheme carrier of `GL_n(𝔸)` from `Langlands.Global.RankinSelberg.UnequalIntegrals`.

## Local components and the set `N_n(F_v) GL_n(𝒪_v)`

* `finiteComponent F n v g` is the component `g_v ∈ GL_n(F_v)` of an adelic point `g` at a
  finite place `v`. It is computed with the existing maps: `GeneralLinearGroupPoints.adelicEquiv`
  to adelic matrices, `AdelicGL.finite` to finite adelic matrices, then
  `FiniteAdelicGL.localProjection`, which evaluates the matrix entries at `v`.
* `IsUnipotentIntegral F n v x` says that `x ∈ N_n(F_v) GL_n(𝒪_v)`. Here `N_n` is the
  upper unitriangular subgroup and `GL_n(𝒪_v)` is the Library's
  `FiniteAdelicGL.localIntegral F n v`, the matrices with entries and inverse entries in
  `𝒪_v`. The Lean condition is that `x k` is upper unitriangular for some
  `k ∈ GL_n(𝒪_v)`. This is equivalent to `x ∈ N_n(F_v) GL_n(𝒪_v)`, because `x k = u`
  exactly when `x = u k⁻¹`.
* `unipotentIntegralOutside F n S` is the set of adelic `g` with
  `g_v ∈ N_n(F_v) GL_n(𝒪_v)` at every finite place `v ∉ S`. There is no condition at the
  places of `S` or at the infinite places. Left multiplication by `N_n(𝔸)` preserves the
  set, because the component of an element of `N_n(𝔸)` at `v` lies in `N_n(F_v)`.

## Spherical vectors

`IsSphericalOutside F T S x` says that the vector `x` of an actual cuspidal realization `T`
of `GL_(r+1)` is fixed by every `k ∈ GL_(r+1)(𝒪_v)`, for every finite `v ∉ S`. The group
acts through the realization's finite adelic action `T.realization.finiteRepresentation`,
after the place-`v` inclusion `FiniteAdelicGL.localInclusion`, which puts `k` at `v` and
the identity at every other finite place. The Library's finite action is right
translation of automorphic functions. So the condition says that the cusp form of `x`
is right invariant under `GL_(r+1)(𝒪_v)` for all finite `v ∉ S`. This is Cogdell's
condition that the local vectors outside `S` are the unramified ones (p.206 and p.215).
The condition does not require `x` to be a pure tensor. Since `T` is irreducible, every
vector with this property is a finite sum of pure tensors whose components outside `S`
are the spherical vectors. The factorization argument of p.206 therefore applies to `x`
by linearity.

## The partial Whittaker integral `Ψ_(S∪∞)`

`partialUnequalWhittakerIntegral F h S W W' s` is the Bochner integral of the existing
integrand `unequalWhittakerIntegrand F h W W' s` (from
`Langlands.Global.RankinSelberg.WhittakerIntegrals`) over the classes
`q ∈ N_m(𝔸) \ GL_m(𝔸)` whose representative `q.out` lies in
`unipotentIntegralOutside F m S`. It uses the restriction of the same measure
`whittakerQuotientMeasure F m`. Recall that this measure is the pushforward of
Haar/counting measure on `N_m(F) \ GL_m(𝔸)`. The selected set of classes depends only on
the class, because `unipotentIntegralOutside` is left `N_m(𝔸)`-invariant. The set is
open, since `N_m(F_v) GL_m(𝒪_v)` is open in `GL_m(F_v)` and equals `GL_m(𝒪_v)` up to
left `N_m(F_v)`-translation. In the source's notation this set is
`N_m(𝔸) \ (GL_m(𝔸_(S∪∞)) × ∏_(v ∉ S) N_m(F_v) GL_m(𝒪_v))`.

**Comparison with the source.** Cogdell writes the global integral as a product of local
integrals `Ψ_v`, each over `N_m(F_v) \ GL_m(F_v)` (p.206). He then identifies `Ψ_v` for
`v ∉ S` with `L(s, π_v × π'_v)` (Theorem 3.3, p.215), where `vol(GL_m(𝒪_v)) = 1` and the
spherical Whittaker functions are normalized by `W_o(e) = W'_o(e) = 1`. The integral
`Ψ_(S∪∞)` of this file is the product of the local integrals at the places of `S` and at
the infinite places. Writing it as an integral over the selected subset of the global
quotient avoids factoring the global quotient measure into local measures. On the
selected set the spherical local factors contribute `W_o(n_v k_v) W'_o(n_v k_v) = 1`, and
`|det h_v| = 1`. So the restriction carries the same local integrals at `S ∪ ∞`, with the
measure induced from the global one. In the factorization identity
`Ψ = Ψ_(S∪∞) · ∏_(v ∉ S) L_v`, both sides then scale in the same way under any change of
the global measure normalization. Up to this identification, `Ψ_(S∪∞)` is the integral
written `Ψ_S` in Cogdell's §4.1 (p.219). Because Lean `∫` is total, this definition
asserts no convergence; convergence is a clause of the statement that uses it.

## The partial dual Whittaker integral `Ψ̃_(S∪∞)`

`partialDualWhittakerIntegral F h S W W' s` is the Bochner integral of the existing dual
integrand `dualWhittakerIntegrand F h W W' s` over the same set of classes, with the same
restricted measure `whittakerQuotientMeasure F m`. Here the dual integrand is the inner
integral over `x ∈ M_(n-m-1,m)(𝔸)` (Library: `rectangleMeasure`) of
`W([[h,0,0],[x,I_(n-m-1),0],[0,0,1]]) W'(h) |det h|^(s-(n-m)/2)`. Only the outer variable
`h` is restricted. The inner integral still runs over the whole of `M_(n-m-1,m)(𝔸)`, at
every place.

The dual integral `Ψ̃(s; W, W')` is defined in Cogdell on p.207. Its partial Euler
factorization is used in the proof of Theorem 4.1 (p.220). There the local dual integrals
at the places `v ∉ S` are identified with `L(s, π̃_v × π̃'_v)`, through the local
functional equation (Theorem 3.2, p.214) and Theorem 3.3. The restriction is placed only
on `h`, because for spherical data the local inner integral is already constant on the
selected set. If `h_v ∈ N_m(F_v) GL_m(𝒪_v)` and the spherical Whittaker function is
normalized by `W_o(e) = 1`, then the local integral over `M_(n-m-1,m)(F_v)` equals the
volume of `M_(n-m-1,m)(𝒪_v)`. The reason is that the spherical function vanishes at
`[[I,0,0],[x,I,0],[0,0,1]]` unless `x` is integral (see the Markdown of
`UnequalDualEulerFactorizationStatement`). As for `Ψ_(S∪∞)`, such volumes appear in the
same way on both sides of the identity, so the identity does not depend on the
normalization of the global measures. Because Lean `∫` is total, this definition asserts
no convergence either.

## Provenance

The construction is internal. It specializes the Library's existing local factor maps,
integral subgroups, finite adelic action and quotient measure. The only source content is
the interpretation described above, from Cogdell pp.206, 207, 214–215 and 219–220.
