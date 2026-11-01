# Finite convolution of actual adjacent-rank determinant shells

This derived module implements the finite coefficient calculation in Jacquet,
Piatetski-Shapiro and Shalika, *Rankin–Selberg Convolutions* (1983), Section 6.3,
printed pages 433–435, formulas (5)–(10). The registered original is
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Worker 486 visually read printed pages 427–439 and reread pages 433–435 for
this implementation. No JPSS-specific registered erratum was found in the
available literature index or project notes during the preceding source audit.

## Actual functions and measures

Write `T = F.canonicalTopologicalData`, `G = GL_(r+1)(F)`,
`Q = N_(r+1) \ G`, and `η = generalLinearHaar F.Carrier r`.
All topological and valuation structures are the canonical ones. The quotient
measure `ν` in the main theorem is any measure compatible with the same
actual group and unipotent Haar measures; existing quotient-measure existence
makes this hypothesis inhabited.

The first vector `W` belongs to the actual coefficient image of a specified
Whittaker functional on a smooth representation `σ`. The second representation
`τ` is admissible, with a specified functional for `ψ.scale (-1)`; `W'` belongs
to that actual coefficient image. The imported
`InducedTailIntermediate.scaledStandardAsInverse` retains the underlying
function exactly and gives inverse covariance for `ψ`.

For a square-matrix Schwartz test `Φ`, a row Schwartz test `φ`, a continuous
quasicharacter `χ`, and an arbitrary complex exponent `s`, the new definition
`adjacentRankInnerMultiplier` is

`a_s(h) = χ(det h) |det h|^s`.

The actual inner slice weight, imported from `AdjacentRankInnerSliceSeparation`,
is

`b_(j,s)(h) = 1_{ord(det h)=j} Φ(h) χ(det h) |det h|^s`.

The imported joint-shell kernel has representative expression

`K_(m,s)(Ng,h) = 1_{ord(det g)+ord(det h)=m}`
`  * W(g) W'(gh) φ(lastRow g) Φ(h) a_s(h)`.

The before-shear kernel is the actual inverse-quotient-shear composition,
with representative expression

`Kbefore_(m,s)(Ng,h) = 1_{ord(det g)=m}`
`  * W(gh⁻¹) W'(g) φ(lastRow(gh⁻¹)) Φ(h) a_s(h)`.

These are functions on the existing quotient and group, with the supplied
measures unchanged.

## Implemented result

`adjacentRankShell_finiteConvolution` supplies integers `Lq,Lh`, a finite basis
family `B_i` in the same actual model of `τ`, and, for every second vector `W'`,
a family `f_i` in the bi-smooth matrix-coefficient span of that model's
right-translation representation. The bounds satisfy

- `W(g) ≠ 0` and `φ(lastRow g) ≠ 0` imply `Lq ≤ ord(det g)`;
- `Φ(h) ≠ 0` implies `Lh ≤ ord(det h)`.

The basis is chosen before `W'`, and its coefficients are chosen before every
shell order `m` and exponent `s`. For all those orders and exponents the theorem
proves

`∫_(Q×G) K_(m,s) d(ν×η)`
`  = Σ_(k ∈ [Lq,m-Lh]) Σ_i Ψ^k(W,B_i;φ)`
`      * ∫_G b_(m-k,s)(h) f_i(h) dη`,

where `B_i` on the right is recast as an inverse coefficient for `ψ`, and
`Ψ^k` is precisely the existing `equalRankSliceCoefficient T ν`.
The same finite sum equals the iterated integral of `Kbefore_(m,s)`.
Both product kernels are genuinely integrable. Every equal-rank quotient-slice
factor and every group-slice factor is genuinely integrable, for every integer
slice and every complex exponent. The assertions retain every canonical p-adic
field, independent universes for the field and the two representation carriers,
and every `r : ℕ`, including actual group rank one. No nonzero-vector,
irreducibility, full Whittaker-type, or large-real-part assumption is used.

## Proof

The preliminary `hasCompactSupport_equalRankSlice` bounds the support of the
actual equal-rank slice integrand at zero by the existing compact Whittaker
row-slice support. Nonvanishing of its product forces nonvanishing of its first
coefficient and row test. Continuity descends through the open quotient map;
the clopen slice cutoff preserves continuity. Consequently
`integrable_equalRankSlice` proves integrability for every Borel quotient
measure finite on compact sets.

`integral_eq_sum_determinantSlices` is a generic finite partition theorem for an
integrable quotient function whose pointwise support has orders in a finite set.
The integrable indicators sum to the original function. The pointwise helper
`adjacentRankJointShellKernel_mk_eq_innerSlice` identifies the joint cutoff on
the quotient slice `k` with exactly the group slice `m-k`.

For the main theorem, the existing Whittaker-row and matrix-test estimates
choose `Lq,Lh`. The actual compact-open averaging theorem
`adjacentRankInnerSlice_finiteSeparation`, applied at `ψ.scale (-1)`, chooses
`B_i,f_i` and separates each convergent inner integral. The imported
`adjacentRankShell_shear_fubini` proves absolute integrability before and after
the actual quotient shear, integrability of the outer integral, and exact
transport between the two iterated integrals. Compatibility supplies regularity
of `ν`; local compactness and second countability supply the measure instances.

A nonzero joint kernel has both individual lower bounds and fixed total order
`m`. Thus its quotient order lies in `[Lq,m-Lh]`. The outer integral vanishes
pointwise outside that interval, so the finite partition theorem applies.
On its `k` slice, the pointwise kernel identity and uniform inner separation
express the outer integrand as a finite sum of actual equal-rank integrands
times the group-slice constants. The proved quotient-slice integrability
justifies integrating this sum. The indicator-integral identity for the existing
slice coefficient gives the displayed formula. Finally, the exact shear/Fubini
identity gives the before-kernel formula.

## Scope

This is the fixed-total-shell coefficient calculation. It does not identify the
before-kernel with an induced integral-model zeta coefficient, sum a global
Laurent series, prove convergence on a half-plane, derive functional equations,
or certify either parent adjacent-rank gamma or L statement. The coefficients
`f_i` are explicitly coefficients of the actual Whittaker-image representation;
no unchecked identification with the original arbitrary representation is made.
The initial model substitution, global series and factor assembly remain
separate obligations. The imported joint-shell and quotient-shear helpers retain
their separate independent review and publication requirements.
