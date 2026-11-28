# Isobaric spherical Hecke data of the residual spectrum of `GL_n`

`Langlands.Automorphic.DiscreteHeckeIsolation.GeneralLinearResidualIsobaricHeckeDataStatement.{uV}`
uses a number field `F : Type` with compact additive adele quotient and the canonical right action
on `L²([GL_{r+1}])`. Let `P` be a nonzero irreducible closed invariant subspace which is not
contained in the full almost-everywhere cuspidal subspace for the canonical measure. The
conclusion gives the following data.

- A family of actual positive-rank cuspidal classes `c j` indexed by `Fin m`, with `m > 1` and
  total rank `r + 1`. Every class has an attached spectral system `t j`, using actual cuspidal
  presentations with carrier universe `uV`. The family retains repetitions.
- A spectral system `s` of rank `r + 1` whose Euler denominator polynomials agree away from a
  finite set with the products of those of the `t j`. At every finite place outside the
  exceptional set of `s`, the local restriction of `P` has nonzero spherical vectors and the
  spherical Hecke algebra acts on them through a character. Its values on the standard diagonal
  double cosets are the `standardHeckeScalar` values of `s`. The latter use the mass-one Haar
  normalization and the positive square root of the residue cardinality.

The mathematical source is the residual spectrum theorem of Mœglin and Waldspurger, which gives
an irreducible residual representation as a Speh representation. In the split-centre formulation,
Getz–Hahn give it as `(σ, m)` for a cuspidal `σ` of rank `d` with `md = r + 1`. The case `m = 1`
is the cuspidal spectrum. For `m > 1`, the constituents are the determinant norm twists of `σ`
with exponents `(m + 1)/2 - i` for `i = 1, …, m`. Away from the finite set of ramified places, the
Euler denominator polynomial of `(σ, m)` is the product of the polynomials of these twists.
The normalized Satake description of the spherical action in the Library gives the standard
scalar equations. The proposition records these numerical and spherical consequences for the
actual local restrictions of `P`.

- C. Mœglin and J.-L. Waldspurger, *Le spectre résiduel de GL(n)*, Ann. Sci. École Norm. Sup.
  22 (1989), 605–674. `moeglin-waldspurger-1989-residual-spectrum`, SHA-256
  `a46e3549d05d2cd39f396ef326840f4484f3935ff3daa17e6339091962de9e94`, Introduction and Théorème,
  pp. 605–606 (PDF pp. 2–3). The paper uses a fixed unitary central character.
- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, Springer, 2024.
  `getz-hahn-2024-automorphic-representations`, SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`, §10.8 and Theorem 10.8.1,
  pp. 289–290 (PDF pp. 301–302), including the isobaric description and the displayed
  unramified Euler factors. The identification of a spherical representation by its Hecke
  character is Proposition 7.1.2, p. 184 (PDF p. 197).
