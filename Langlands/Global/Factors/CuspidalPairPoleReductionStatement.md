# Reduction of the poles of cuspidal pair L-functions

Lean module: `Langlands.Global.Factors.CuspidalPairPoleReductionStatement`.

`CuspidalPairPoleReductionStatement` is the implication

`CuspidalArchimedeanParameterExistenceStatement` →
`RankinSelbergGlobal.CuspidalSlabPairingStatement` →
`CuspidalPairSemilocalRatioStatement` → `CuspidalPairVerticalStripStatement` →
`CuspidalPairPoleStatement`,

at universes `u` (number field) and `uQ` (factor universe of spectral presentations). It is
a proposition definition only; it is an internal reduction (no single source states it).

## The target and the premises

- Target: `CuspidalPairPoleStatement` (Getz–Hahn (2024), Theorem 11.7.1, poles and vertical
  strips; Cogdell (2004), Theorems 4.1 and 4.2). See its Markdown.
- `CuspidalArchimedeanParameterExistenceStatement` (Library, module
  `Langlands/Global/Factors/CuspidalPairFunctionalEquationReduction`): archimedean
  standard-module parameters of cuspidal realizations exist. It supplies the archimedean
  clause of the existence part of the target.
- `CuspidalSlabPairingStatement`: the residue clause of Cogdell (2004), Theorem 2.2.
- `CuspidalPairSemilocalRatioStatement`: the semi-local ratios of Cogdell (2004), §4.
- `CuspidalPairVerticalStripStatement`: the bound in vertical strips (GH 11.7.1; Cogdell
  Theorem 4.1(2)).

Each premise module's Markdown gives its sources.

## Proof route (implemented in a draft, for a proof task)

This is Cogdell's argument (2004, §4.1–4.2, printed pp.219–222) on top of the Library's
proved global theory:

1. The finite pair L-data exist (canonical local components of a standard character, their
   self-dual measures, and `exists_isAutomorphicPairLPolynomial`); the archimedean parameters
   exist by the first premise.
2. Fix a standard character `ψ` and `S` containing the exceptional sets and the ramification
   of `ψ`. For a datum, the global integral (`equalIntegral` or `unequalIntegral`) equals
   the global Whittaker integral (Library unfolding), which equals
   `Ψ_(S∪∞) · ∏_(v ∉ S) L_v` (Library Euler factorization), hence `E · G` with
   `G(s) = L_∞(s) ∏_v L_v(s)` and `E` entire (semi-local ratios), on a half-plane
   independent of the datum. In equal rank the continuation of the global integral is
   compared with the Whittaker integral, which is holomorphic on the half-plane of absolute
   convergence, by the identity theorem.
3. The quotients `I/E` glue to `Λ`, holomorphic off `{0, 1}`, equal to `G` on the half-plane
   (identity theorem on `ℂ ∖ {0, 1}`); at `0` and `1` the order of `Λ` is that of `I` for a
   datum with `E ≠ 0` there.
4. Poles: unequal ranks give entire integrals. In equal rank, the central characters satisfy
   `ω ω' = |·|^w`, `w = 0` by triviality on the split centres, or `ω ω'` is nontrivial on
   norm-one ideles (entire integrals). For `w = 0` the Library's explicit continuation has a
   pole at `1` exactly when `Φ̂(0) C(φ, φ') ≠ 0` and at `0` exactly when `Φ(0) C(φ, φ') ≠ 0`;
   the slab-pairing premise turns this into "`T` realizes the contragredient of `T'`",
   using a nonnegative standard Schwartz–Bruhat `Ψ` with `Ψ(0) = 1` for the pole at `0` and
   its Fourier transform (whose transform at `0` is `Ψ(0) = 1` by Fourier inversion) for the
   pole at `1`.
5. Vertical strips: the last premise.
