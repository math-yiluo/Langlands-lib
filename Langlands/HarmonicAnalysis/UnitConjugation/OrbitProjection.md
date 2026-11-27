# Projection estimates for an almost fixed orbit of additive cosets

Let `R` be an ultrametric normed algebra over a nontrivially normed field `F`. `conjugationCosetOrbit K L X` consists of the points `Ad(k) X + l`, where `k` belongs to the subgroup `K` of units and `l` belongs to the additive subgroup `L`. If `K` preserves `L`, replacing `X` by a point of this set gives the same set. The proof composes conjugating units and uses preservation of `L` to adjust their additive terms.

`AlmostFixedOrbitProjectionStatement` treats the case in which the orbit contains two points `X₀` and `β X₀`. Suppose the elements of `L` have norm at most `a`, conjugation by `K` displaces every `x` by at most `δ ‖x‖`, and the continuous linear map `p` satisfies `‖x − p x‖ ≤ C ‖β x − x‖` with `C ≥ 0`. Then all orbit points are within `B = max(a, δ ‖X₀‖)` of `X₀`, and the transverse error `‖X₀ − p X₀‖` is at most `C B`. For any two orbit points `Y` and `Z`, the distance between `p Y` and `Z` is at most `max(1, ‖p‖, C) B`.

Rebasing the orbit at `X₀` and applying the ultrametric inequality give the common bound `B`. Applying it to `β X₀` gives the transverse estimate. The proof of the final bound writes `p Y − Z` as the sum of `p(Y − X₀)`, `p X₀ − X₀` and `X₀ − Z`, and uses the operator norm of `p` on the first term.

This is the norm argument of Clozel, *Characters of non-connected, reductive p-adic groups*, Canadian Journal of Mathematics 39 (1987), §3.6, Lemma 11 and its corollary, printed pp. 159–162. The norm bounds on the lattice and the conjugators are kept as parameters. In the semisimple descent application `p` projects onto the fixed algebra and `β` is the adjoint action at a point of the slice.
