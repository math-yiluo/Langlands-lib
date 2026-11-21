# Counting the torsion zeros of a cubic-power section

`Datum.TorsionZeros s` is the type of level coefficient tuples for which
the corresponding torsion point lies outside the generation open of `s`.
Here `s` is a global section of the actual `t`-th power of the cubic bundle
`M` of a datum over an algebraically closed field. The proof uses values at
the field's single scheme point.

Given `0 < g`, `0 < d`, `n` nonzero in the field, and an actual closed
immersion over the field with `i^*𝒪(1) ≅ M`,
`Datum.card_torsionZeros_le` bounds the number of such tuples by

\[
6^g d\,g!\,t\, n^{2g-2}
\]

if the generation open is nonempty. No extra nondegeneracy requirement on
the embedding is used. The degree parameter `d` is the square root of the
polarization degree. `Datum.sectionOpen_eq_bot_of_forall_torsion_notMem`
then shows that if `n^2 > 6^g d g! t` and every labelled torsion point lies
outside the generation open, this open is empty. Indeed the full level
supplies `n^(2g)` tuples, exceeding the bound under this inequality.
Both lemmas also apply when `t = 0`.

This is an adaptation of the Library's Bézout proof of Mumford–Fogarty–Kirwan,
*Geometric Invariant Theory*, 3rd ed., Chapter 7, Proposition 7.7 (printed
pp. 138–139). The pullbacks by `[n]` of sections from hyperplanes through the
embedded origin give the same system in `M^(n*n)` as in
`TorsionHyperplaneBezoutReduction.lean`. Its base locus is the actual
multiplication fibre, finite and consisting of closed points here. The
published Bézout theorem bounds its intersection with the zero locus of a
section of `M^t`: it is applied with the powers `(t,n*n)` and the published
leading Euler coefficient `6^g d` of `M`. Full level and evaluation of
sections over the field give an injection of the labelled zeros into this
finite intersection. Thus the factor in `t` is linear; the proof does not
form a new polarized datum with a scaled polarization or use an embedding
by a complete system of the higher power. It makes no claim about the scheme
structure of a configuration determined by these points.
