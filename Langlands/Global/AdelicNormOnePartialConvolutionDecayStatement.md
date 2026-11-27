# Uniform rapid decay of norm-one partial convolutions of cuspidal `L²` classes

Module `Langlands.Global.AdelicNormOnePartialConvolutionDecayStatement` states the proposition
`Langlands.Global.NormOnePartialConvolutionRapidDecayStatement` (universe `u`) and proves nothing.

## Statement

Let `F` be a number field and `H` an affine group scheme over `Spec F`, locally of finite type
and connected reductive. Fix the data of the Library's positive-central quotient
`PositiveRationalQuotient F H T i = H(F) T^+ \ H(𝔸)`: a commutative group scheme `T` with a
central morphism `i : T → H` (`IsCentral i`), an isomorphism `e` of `T` with a split torus, an
injective restriction of rational characters `characterRestrict i` with finite-index image, and
right invariance of the Haar measure of the norm-one subgroup `H(𝔸)¹ = normOneSubgroup F H`.
Let `S` be `fullAEL2CuspidalSubmodule F H parabolicDynamic hH T i hi I e hc`, the closed subspace
of `L²(PositiveRationalQuotient F H T i)` of classes whose constant terms along every proper
rational parabolic vanish almost everywhere (module `Langlands.Automorphic.GroupSchemeFullAEL2`).
For `h ∈ S` write `h̃(n) = h(H(F) T^+ n)` for `n ∈ H(𝔸)¹`.

Let `rho` be a closed matrix embedding of positive size, with adelic height
`‖x‖ = adelicHeight F H rho x`. For every test function `K` on `H(𝔸)`
(`IsAdelicTestFunction F H K`: smooth, compactly supported, bi-invariant under open subgroups of
`H(𝔸_f)`), every compact `B ⊆ H(𝔸)` and every `m : ℕ` there is `C ≥ 0` such that every
`x ∈ H(𝔸)¹` has a rational point `q ∈ H(F)` with

`‖∫_{H(𝔸)¹} conj K(n⁻¹ q x b) h̃(n) dn‖ · ‖q x‖^m ≤ C ‖h‖`

for all `h ∈ S` and all `b ∈ B`, the integral being taken for the Haar measure of `H(𝔸)¹`.

The function `y ↦ ∫_{H(𝔸)¹} conj K(n⁻¹ y) h̃(n) dn` on `H(𝔸)` is left invariant under `H(F)`.
On `y = x b` with `x ∈ H(𝔸)¹` it is the convolution of `h̃` over the norm-one subgroup with the
kernel `z ↦ conj K(z⁻¹ b)`. The proposition says that these partial convolutions are rapidly
decreasing on a set of representatives of the norm-one quotient, uniformly for `b` in a compact
set, with a constant linear in the `L²` norm of `h`. The representative `q x` depends on `x`
only, not on `h` or `b`.

## Provenance

This is a derived statement. Rapid decay of cuspidal functions of uniform moderate growth is
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.2.12, printed
pp. 34–35, applied to the smoothing of cuspidal `L²` classes by compactly supported smooth
kernels as in their I.3.4, printed pp. 45–46. The Library proves the corresponding facts for
convolutions over the whole group `H(𝔸)`: the growth of smoothed quotient classes
(`positiveQuotientLpSmoothing_globalGrowth`, module
`Langlands.Automorphic.GroupSchemeCuspidalConvolutionCompact`), rapid decay on norm-one
representatives (`adelicNormOneCuspidalRapidDecay`) and its uniform family version
(`StandardParabolicFamily.adelicRelativeCuspidalRapidDecay`). The convolution here runs over the
norm-one subgroup only. That is the form in which the norm-one Levi pairings of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series* (2024), §6.2, (6.8),
p. 202, meet the Iwasawa decomposition of a right convolution on the ambient group: the pairing
of a fibre `m ↦ f(m g)` with a cusp form on `M(F) \ M(𝔸)¹` becomes an integral of `f` against
such partial convolutions of the cusp form.

A proof can write `K` as a finite sum of convolutions of test functions
(`IsAdelicTestFunction.exists_eq_sum_convolution`), so that each partial convolution is a right
convolution on `H(𝔸)` of a continuous function bounded by a constant times a power of the height
times `‖h‖`, cuspidal because `h ∈ S`, and then apply the uniform rapid decay theorem on a Siegel
set enlarged on the right by `B`.
