# Proof of the mirabolic Eisenstein series theorem

`Langlands.Global.RankinSelbergGlobal.Eisenstein.eisenstein` proves the Library's
`EisensteinStatement` for number fields in an arbitrary universe. The source is
J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), §2.3,
printed pp. 208–209 (PDF pp. 211–212), registered as
`cogdell-2004-analytic-theory-gln`. The construction uses the normalizations
described in `EisensteinStatement.md`.

The implemented proof unfolds the absolutely convergent Eisenstein series to
a theta Mellin integral over an idele fundamental domain. The Poisson formula
splits the integral at `log |det(a g)| = 0`. The two positive-height tails are
entire and their sum is uniformly bounded on strips for `g` in a compact set.
For the dual tail the upper bound on the real part is `1 - a` when the lower
bound for the original strip is `a`. The map `g ↦ ᵗg⁻¹` carries the compact
set to a compact set.

If the character is nontrivial on the norm-one ideles, both negative-height
boundary integrals vanish. In the norm-power case `χ = |·|^w`, write
`L(g) = log |det g|` and `n = r + 1`. The continuation adds
`exp(-w L(g)/n) Φ̂(0)/(n s + w - n)` and
`-exp(-w L(g)/n) Φ(0)/(n s + w)` to the entire part. The proof uses the
positive-real-part conditions for both denominators to identify this formula
with the unfolded integral on a right half-plane. A common abscissa also
ensures convergence for the inverse character and the Fourier transform.

The two denominators give the possible simple poles `1 - w/n` and `-w/n`.
Their reciprocal bounds on a strip follow from the prescribed distance to
the poles, and the common numerator factor is continuous in `g`, hence
bounded in norm on a compact set. For the functional equation,
`(χ, Φ, Φ̂, g, s) ↦ (χ⁻¹, Φ̂, Φ, ᵗg⁻¹, 1-s)` interchanges the two
entire tails. It also keeps the common numerator factor fixed and
interchanges the two denominators with a change of sign. Symmetry of the
Poisson pair supplies the decomposition for the dual series.
