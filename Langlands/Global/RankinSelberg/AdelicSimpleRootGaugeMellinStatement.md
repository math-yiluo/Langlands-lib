# Mellin convergence for a proper-block restriction of a simple-root gauge

`AdelicSimpleRootGaugeMellinStatement` is an internal, unproved proposition
definition. It contains no automorphic functions or cuspidal realizations.
It quantifies over `F : Type u` with `Field F`, `NumberField F` and
`CompactSpace (AdeleQuotient F)`, every `r t : ℕ` with `t < r`, and every
fixed gauge exponent `τ ≥ 0`. It asks for one real threshold `C ≥ 0` such that
every `Ξ` satisfying `IsAdelicSimpleRootGauge F r τ Ξ` obeys

`∫⁻ p, Ξ(pad p.out) · ofReal(detNorm(p.out)^σ) dμ(p) < ⊤`

for every real `σ > C`. Here `p` belongs to the actual quotient
`WhittakerQuotient F (t+1) = N_(t+1)(𝔸) \ GL_(t+1)(𝔸)`,
`μ = whittakerQuotientMeasure F (t+1)`, and `pad` is the published map
`g ↦ diag(g, I)` into the actual `Points F (r+1)`. The exponent on the
determinant is a real power of its normalized positive absolute value.
The conclusion is finiteness of this extended nonnegative lower integral.

The threshold can depend on `F`, `r`, `t` and `τ`. Its existential
quantifier precedes the quantifier over `Ξ`, so it is independent of both
the gauge and its Schwartz–Bruhat witness. There is no common numerical
bound on the values of these integrals. The case `t = 0` includes restriction
to `GL_1`, and the proper-block hypothesis excludes the full ambient group.

The measure is the Library's pushforward from the Haar quotient by the
rational upper unipotent subgroup to the quotient by the full adelic
upper unipotent subgroup, as defined in `WhittakerIntegrals`. The formula
uses the quotient representative `p.out`, consistently with the existing
Whittaker integrals. Full left unipotent invariance in the gauge definition
is the relevant invariance: padding carries the smaller upper unipotent
into the larger one, and the smaller determinant norm is constant on
unipotent cosets.

The source model is Jacquet, Piatetski-Shapiro and Shalika, *Automorphic forms
on GL(3) II* (1979), source `jps-1979-gl3-ii`. Section 12.1, formula
(12.1.1), printed page 226, defines gauges in arbitrary rank. Section 13.4,
printed pages 239–240, bounds the Mellin integral on `diag(a,1,1)` by
`∫ Φ(a,1)|a|^(Re(s)−τ−1) d×a`; the adjacent Lemma (13.4.3) treats a
rectangular integral and uses convergence of the unramified product.
Those applications concern `GL_3`. The assertion here, covering every
proper block in every rank with a threshold uniform over the Library's
norms of complex Schwartz–Bruhat functions, is an internal generalization.
It is not a literal numbered theorem of that source.

The intended analytic route uses simple-root coordinates. For a block of
size `m = t+1`, padding its diagonal by ones gives roots `a_1,…,a_m`
followed by ones, with block determinant `∏_(i=1)^m a_i^i`. Thus a positive
determinant power acts on every variable, including the block's central
direction. The upper triangular modulus contributes fixed shifts.
A proof must establish the integration formula for the actual quotient
measure, restriction of the Schwartz–Bruhat function to these coordinates,
and global Mellin convergence with the unramified Euler product. This
module supplies the proposition definition only; these conclusions remain
unproved here. Its imports contain no `UnequalGaugeReduction` dependency.
