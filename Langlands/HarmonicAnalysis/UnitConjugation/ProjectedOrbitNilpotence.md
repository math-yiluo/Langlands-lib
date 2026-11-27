# Large projected orbit points near the nilpotent cone after rescaling

Let `R` be a proper ultrametric normed algebra of finite dimension over a complete nontrivially normed field `F`. Fix a continuous linear map `p` on `R`, a compact set `ω`, a scalar `d` with `‖d‖ > 1`, and a nonnegative transverse bound `C`. The compact set `projectedAnnulus p d` consists of vectors in the image of `p` of norm between `1/‖d‖` and `1`.

`ProjectedOrbitNearNilpotentsStatement` concerns an orbit of additive cosets meeting both the conjugacy saturation of `ω` and its image under a map `β` with transverse bound `‖x − p x‖ ≤ C ‖β x − x‖`. Given an open neighborhood `V` of the nilpotent points of the annulus, the theorem finds a uniform upper threshold on the conjugation displacement coefficient and a lower size threshold relative to the bound on the additive lattice. Every projected orbit point above that size threshold admits a nonzero scalar multiple in the annulus and in `V`.

The proof uses `almostFixedOrbitProjection` to control the distance from `p Y` to every point in the orbit. The ultrametric inequality shows that a sufficiently large `p Y` has the same norm as the almost-fixed representative. Rescaling `p Y` into the annulus makes both the scalar and the error to a normalized conjugate of a point of `ω` small. `nilpotentApproximation` then puts the rescaled point in `V` by comparing the coefficients of the characteristic polynomial of left multiplication.

The argument follows the normalization in Clozel, *Characters of non-connected, reductive p-adic groups*, Canadian Journal of Mathematics 39 (1987), §3.6, Lemma 10, printed pp. 159–162. It uses a fixed annulus and uniform coefficient estimates for conjugates of a compact set.
