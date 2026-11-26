# Order at one of the partial cuspidal pair L-function from the completed poles

`Langlands.Global.CuspidalPartialPairOrderOneFromPairPole` is the implication

```
CuspidalPairPoleStatement.{u, u} → CuspidalPairBoundaryNonvanishingStatement.{u, uQ} →
  CuspidalPartialPairOrderOneStatement.{u, uQ}
```

from the completed pair pole theorem and partial boundary nonvanishing to the exact order
at `1` of the partial cuspidal pair L-function. This file proves it as
`Langlands.Global.cuspidalPartialPairOrderOne_of_pairPole`. It does not prove the two
premises.

The pole statement is used at the universe `u` of the number field: the proof applies it
to auxiliary presentations whose factors lie in the form-space universe. Those come from
`Automorphic.cuspidalAllLocalIrreduciblePresentationExistence`. The boundary statement is
used at the original universes. The original ranks, presentations, admissible omitted set
`S`, and supplied meromorphic function `L` are arbitrary. The archimedean input is the
Library theorem `Automorphic.cuspidalArchimedeanPairRegularity`, used inside the
[completed-order comparison](CuspidalPartialPairOrderOneComparison.md).

## Proof

The proof normalizes the two cusps by determinant norm powers `-a` and `-b`, chosen by
`NormPowerTwist.exists_normPower_twist` so that the twisted realizations are trivial on the
split centre. On the positive scalar ideles parametrized by `exp y`, split-centre
triviality determines the original central character as
`exp (a * [F : ℚ] * (r + 1) * y)` in rank `r + 1`. Unitarity gives `a.re = 0`, and the
same argument gives `b.re = 0`. For an actual contragredient pair, unitary conjugation and
contragredient uniqueness show that the original central characters multiply to one.
Differentiating their exponential relation at `y = 0` gives `a + b = 0`. Twisting by
inverse characters preserves and reflects contragredience after the equal-rank cast. Thus
the original dual condition is equivalent to the conjunction of `a + b = 0` and the
normalized dual condition (`isDual_iff_shift_eq_zero_and_normalizedDual`).

At every finite place outside the original omitted set, the canonical spherical Hecke
scalar equations transfer to the auxiliary local components. Compact averaging gives
nonzero spherical fixed vectors in those components. Indeed, their intertwiner images
span the actual local realization, and averaging commutes with intertwining and acts as
the identity on the supplied nonzero spherical vector. This works even at a place in the
auxiliary exceptional set. The unramified norm twists scale the two spectra by `qᵥ^a`
and `qᵥ^b`. The certified local pair polynomial is the pair Euler polynomial of the
scaled spectra. Evaluating it at `qᵥ^(-(s + a + b))` cancels the two scalars, giving
the original Euler factor at `s` (`finiteL_shift_eq_partialEulerFactor`).

The completed pole statement applied to the normalized cusps and their auxiliary
presentations gives finite pair L-data, archimedean parameters, and a completed function
`Λ` with the simple pole profile at `0` and `1`. The shifted
[completed-order comparison](CuspidalPartialPairOrderOneComparison.md) identifies the
partial order at `1` with the completed order at `1 + a + b`. That point has real part
`1`. In the actual dual case it equals `1`, and the completed profile places its order in
the interval `[-1, 0)`, which gives `-1`. In the other case, the profile gives order at
least zero, by analyticity if the shifted point differs from `1` and by the pole criterion
otherwise. Boundary nonvanishing at `y = 0` applied to the original supplied function
gives the opposite inequality, hence order zero.

## Sources

Arthur–Clozel (1989), *Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula*, III.2 (2.2)–(2.3), printed p. 200 (`arthur-clozel-1989-base-change`), records
the shifted pole condition `π ⊗ |·|^(s-1) ≅ σ̃` on the line `Re s = 1` and the resulting
partial boundary behaviour. At `s = 1` the condition is actual contragredience. The
underlying partial results are in Jacquet–Shalika (1981), *On Euler Products and the
Classification of Automorphic Forms II* (`jacquet-shalika-1981-euler-products-ii`):
Proposition (3.3) (unequal ranks), stated on printed p. 795 with its proof on
pp. 795–802; Proposition (3.6) (equal ranks), pp. 802–804; and Theorem (3.7), p. 804. The Lean proof uses the
completed-function route, following the twist identity and Theorem 11.7.1 in Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), printed p. 309
(`getz-hahn-2024-automorphic-representations`). The archimedean regularity input is the
absolute convergence of the archimedean factors for `Re s ≥ 1` invoked there. The partial
nonvanishing premise is Shahidi (1981), *On Certain L-Functions*, Theorem 5.2, printed
p. 353 (`shahidi-1981-certain-l`).
