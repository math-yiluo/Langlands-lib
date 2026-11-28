# Kottwitz's polynomial in the ordinary Hecke convention

`IsKottwitzFramePolynomial θ hΦ nfun hconj c π s P` describes the geometric
Frobenius polynomial of the right-frame Shimura datum in terms of the
ordinary local Hecke representation `π`. The normalized principal-series
parameter and its lift are those of `π` in the ordinary unramified chart
`c`. The detected polynomial is over the coefficient field, with the
comparison over its algebraic closure. `IsKottwitzFramePolynomialOver`
allows a specified extension in which to make the comparison.

## Cocharacter and L-group

The ordinary action on the Harris cohomology tower uses
`g ↦ op(g⁻¹)` on right frame transporters.
The inverse identification of groups sends the frame cocharacter, in its
underlying matrix coordinates, from `μ` to `−μ`. In particular its
multiplier changes from `z⁻¹` to `z`. This gives the same transformation
on double cosets. The frame double coset at `μ(ϖ)` corresponds to the
ordinary double coset at `μ(ϖ)⁻¹`. The group isomorphism preserves the
normalized spherical algebra by transporting the hyperspecial subgroup
and its volume-one measure. One can therefore use the ordinary normalized
Satake lift and evaluate with the cocharacter `−μ`. [Harris–Taylor, III.1
and III.2, pp. 90–91 and 94–96](https://press.princeton.edu/books/paperback/9780691090924/the-geometry-and-cohomology-of-some-simple-shimura-varieties).

In the ordinary pinned dual group, the dominant weight in the orbit of
`−μ` is `−w₀ μ`, where `w₀` reverses the coordinates at each factor. The
corresponding irreducible dual-group representation is `r_μ^∨`. The
normalization on the Weil group also agrees. The simultaneous signed
antidiagonal representative of `w₀` has determinant one in each factor.
It is fixed by reindexing and by the pinned inverse-transpose action, as
proved by `dualAction_signedAntidiagonal`. Since Frobenius over the
reflex completion fixes the highest weight vector of `r_μ`, it fixes its
translate by this representative in the lowest weight line as well. The
dual of that line is the highest weight line of `r_μ^∨`, on which
Frobenius acts trivially. This is Kottwitz's condition (b) for `−μ`.
The argument works with CM-factor permutations and crossings at an
unramified prime. [Kottwitz, Math. Ann. 269 (1984), §2.1, Lemma 2.1.2
and Theorem 2.1.3, p. 294](https://link.springer.com/article/10.1007/BF01450697).

## Geometric Frobenius and the normalization

Let `x` be the ordinary Satake lift, `f` the residue degree of the
reflex completion, `d` the Shimura dimension, and `s` the chosen
square root of `p`. Write `R = r_μ(N_f(x) ⋊ Φ_v)` so that the existing
operator `V(Φ_v)` on the Kottwitz space is `s^(fd) R`. The dominant
representative of `−μ` has the same dimension pairing as `μ`, since
`w₀ ρ = −ρ`. The operator on the dual has the original normalization
`s^(fd)` multiplying the inverse transpose of `R`. Its characteristic
polynomial is computed by `kottwitzFrameCharpoly` using the transpose
matrix, namely `s^(2fd) V(Φ_v)⁻¹`. In particular each eigenvalue `β` of
`V(Φ_v)` is replaced by `p^(fd)/β`, with multiplicity. The formation
uses geometric Frobenius at the same reflex place.
`kottwitzFrameFrobenius_eq` verifies the cancellation of one factor of
`s^(fd)` in the scaled inverse formula. [Kottwitz, Invent.
Math. 108 (1992), §1, pp. 655–657 and §5, pp. 662–663](https://doi.org/10.1007/BF02100620).

The Lean lemmas prove monicity, the dimension degree, nonzero constant
term, and compatibility with simultaneous change of the square-root sign
and the central Satake lift. These follow from the basis of the Kottwitz
space, invertibility of the endomorphism, and the corresponding sign
identity for `V(Φ_v)`. The reflex degree is unchanged because a power
of Frobenius preserves a cocharacter orbit exactly when it preserves the
negative orbit.

At a split rank-three prime with the Harris signature over an imaginary
quadratic field, take the ordinary component `|ν|ₚ⁻¹`, where `ν` is the
similitude multiplier. The ordinary normalized Satake lift has multiplier
coordinate `p` and matrix part `diag(p,1,p⁻¹)`. Here `f = 1` and `d = 2`.
The operator for the untransported cocharacter has eigenvalues
`p⁻¹, 1, p`. The transported polynomial has roots `p³, p², p`.
These agree with multiplying the trivial component's roots by `p`, as
the frame component `|ν_frame|ₚ` acts on the double coset of multiplier
`p⁻¹`. This also gives the source normalization used in power traces
after unramified base change. [Kottwitz, Math. Ann. 269 (1984), §2.2,
formula (2.2.1), p. 295](https://link.springer.com/article/10.1007/BF01450697).
