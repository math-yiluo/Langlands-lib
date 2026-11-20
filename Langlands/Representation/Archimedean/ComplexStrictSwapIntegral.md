# The complex adjacent-swap integral for strictly decreasing exponents

For adjacent positions occupied by characters with exponents \(t_d,t_e\)
such that \(\operatorname{Re}(t_d-t_e)>0\), `strictSwapIntegral` is the
linear functional integrating a compact-finite standard vector on the chart
`chart i j hj`. This chart is the product of the adjacent permutation matrix
and the upper-root transvection.

The absolute convergence proof factors the chart away from zero and uses the
absolute value of the normalized inducing character. The resulting power of
\(\lvert z\rvert\) at infinity is \(-2-2\operatorname{Re}(t_d-t_e)\). Bounding the
smooth vector on the compact unit disk in the lower-root chart gives an
integrable majorant. The local estimate on the complementary disk uses
continuity. This gives `integrable_chart_of_strict` on the whole smooth standard
module, so the ordinary integral defines a linear map on its \(U(n)\)-finite
vectors.

`functional_one_eq_strictSwapIntegral` identifies the Library's regularized
functional at \(c=1\) with \(2(t_d-t_e)\) times the ordinary integral. The chart
formula for the diagonal derivative expresses the regularized integrand as a
multiple of the original integrand plus its radial derivative. The radial
derivative has a majorant with the same decay because the right derivative
remains in the standard module. Differentiating the two-dimensional scaling
formula under the integral gives the radial derivative's integral as \(-2\)
times the original integral. Cancellation of the nonzero scalar then transfers
the swapped Jacquet exponents to `strictSwapIntegral_isJacquet`.

`strictSwapIntegral_ne_zero` uses the translate of `nzFunction` by the unitary
adjacent permutation matrix. Its chart restriction is a power of
\(1+\lvert z\rvert^2\) whose exponent has real part below \(-1\).
`integral_one_add_norm_sq_cpow` evaluates its integral as a nonzero number.
For `exists_strictSwapIntertwining`, the evaluation-preserving Frobenius map
gives the intertwiner into the swapped module. The identity at the identity
matrix extends to every \(k\in U(n)\) by compact equivariance.

The ordinary chart integral is the rank-one case of the intertwining integrals
in Wallach, *Real Reductive Groups I* (1988), Lemma 5.3.1 and §5.3.4, printed
pp. 144–145 and 147 (PDF pp. 164–165 and 167 of
`wallach-1988-real-reductive-groups-i`), in the Library's convention of left
Borel covariance and right translation. The Lean construction uses the
Library's regularized Jacquet functional in place of Wallach's verification of
the intertwining property. The application is the archimedean constituent step
in Getz and Hahn, *An Introduction to Automorphic Representations* (2024),
Theorem 10.6.4 and its proof, printed p. 286 (PDF p. 298 of
`getz-hahn-2024-automorphic-representations`).
