# Absolute convergence of adelic intertwining integrals

`Langlands.Global.intertwiningAbsoluteConvergence` proves the unchanged
`Langlands.Global.IntertwiningAbsoluteConvergenceStatement.{u}`. It gives
one integrable majorant on the specified discrete quotient of `V(𝔸)`,
uniform over a compact set `C` of adelic arguments and a compact set `Λ`
of sufficiently regular parameters in the supplied coordinates.
The regularity threshold is chosen before `C`, the coordinates, and `Λ`.

## Implemented proof

The proof applies [`intertwiningAbsoluteConvergence_of_eisenstein`](AdelicIntertwiningConvergenceReduction.md)
to the published theorem [`eisensteinAbsoluteConvergence`](AdelicEisensteinConvergenceProof.md).
The latter proves `EisensteinAbsoluteConvergenceStatement.{u}` by projective
height estimates and summability. The reduction keeps its threshold `R`
and uses its compact-uniform summable bound for the Eisenstein terms on
`Ω · C`, where `Ω ⊆ V(𝔸)` is compact and meets every `V(F)`-coset.

For `v = δ ω`, with `δ ∈ V(F)` and `ω ∈ Ω`, the value of the intertwining
integrand is the Eisenstein term at `P(F) w⁻¹ δ` and `ω g`. Two rational
points with the same image under `δ ↦ P(F) w⁻¹ δ` give the same class in
`Γw \ V(F)`, where `Γw = V(F) ∩ w U(𝔸) w⁻¹`: the Weyl conjugation lets the
reduction use `w⁻¹ V w ∩ P ⊆ U`. Thus each index in the image of the class
map needs just one translated copy of `Ω` in `Γw \ V(𝔸)`. The reduction
sums the indicators of these compact images with the nonnegative parts
of the corresponding Eisenstein bounds as weights. The measure of each
image for `intertwiningMeasure` is bounded by the normalized ambient Haar
mass of `Ω`; summability gives integrability. This yields the pointwise
bound on every quotient class for all `g ∈ C` and `s ∈ Λ`.

## Provenance and scope

Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
II.1.6, proof of (i), printed p. 88, deduces the intertwining convergence
from II.1.5 by bounding the integral with the absolute Eisenstein series
over the compact quotient `V(F) \ V(𝔸)`. Lean uses the same comparison to
construct the majorant directly rather than integrate the series. See
also Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series* (2024), §2.2, p. 191. The theorem proves the stated bound in the
sufficiently regular positive chamber, not the sharper region defined
only by roots reversed by `w`, and does not assert holomorphy or continuation.
