# Gauge bounds and torus expansions of Whittaker functions

Author: Worker 11. This file defines three proposition targets and their
conjunction. None of them is a proof, and none is assumed anywhere.

The targets restate the estimates recalled in JPSS (1983), Section 2.5,
printed pages 388-389. They are used there for the convergence of the
Rankin--Selberg integrals. The source cites JPS, *Automorphic forms on
GL(3) I* (1979), Section 2, for the proofs.

## Common data and conventions

Every target fixes a p-adic field `F` with its canonical local-field topology,
a rank `r = n + 1 ≥ 1`, and a complex representation `ρ` of `GL_{n+1}(F)` on a
carrier `V` in an independent universe `uV`. `GL_{n+1}(F)` carries the
matrix-unit topology. Every target also fixes an additive character `ψ` that
is continuous, nontrivial and unitary. The following conditions are written
out in the Lean statements.

- `unipotent g`: `g` is upper unitriangular, that is, `g ∈ N_r`.
- `θ g = ∏_{i < n} ψ(g_{i,i+1})`. This is the standard character of `N_r`
  (JPSS, printed page 377).
- A functional `ℓ ∈ Hom_ℂ(V, ℂ)` is *equivariant* when
  `ℓ(ρ(g)v) = θ(g) ℓ(v)` for every `g ∈ N_r`. This is condition (2.1)(1) of
  JPSS, printed page 385. The Whittaker function of `v` is
  `W_v(g) = ℓ(ρ(g)v)`, so `W(π; ψ)` consists of these functions.
- `torus a` is the diagonal matrix with entries `a 0, …, a n`, for
  `a : Fin (n+1) → F^×`. This is a monoid isomorphism onto `A_r`.
- `roots a i = a i / a (i+1)` for `i < n` are the simple-root coordinates
  `α_1(a), …, α_{r-1}(a)`. JPS (1979), display (2.3.2), printed page 183,
  writes `a = diag(a_1 a_2 ⋯ a_r, a_2 ⋯ a_r, …, a_{r-1} a_r, a_r)`, so the
  i-th coordinate is the quotient of consecutive diagonal entries. JPSS uses
  `α_i(a)` without redefining it.
- `integral k`: `k` and `k⁻¹` have entries in the ring of integers `O`. These
  are exactly the elements of `K_r = GL_r(O)` (JPSS, printed page 376).

Representations *of Whittaker type* (JPSS (2.1), printed page 385) are
admissible representations of finite type with `dim V*_θ = 1`. In Lean,
`IsAdmissible ρ` is the published admissibility predicate, which includes
smoothness. *Finite type* is `Module.Finite` over the group algebra
`MonoidAlgebra ℂ GL_{n+1}(F)`. `dim V*_θ = 1` is written as: there is a
nonzero equivariant `ℓ` of which every equivariant functional is a scalar
multiple.

## `WhittakerGaugeStatement`

Following JPSS (2.5), a *gauge* is a function `ξ : GL_r(F) → ℝ` that is left
invariant under `N_r`, right invariant under `K_r`, and satisfies

`ξ(a) = φ(α_1(a), …, α_{r-1}(a)) |α_1(a) ⋯ α_{r-1}(a)|^{-t}` on `A_r`,

display (2.5)(1), for some real `t ≥ 0` and some Schwartz--Bruhat function
`φ ≥ 0` on `F^{r-1}`. Here `|·|` is the normalized absolute value. In Lean
the nonnegative function is written `‖φ‖` for a complex Schwartz--Bruhat
function `φ`. This describes the same functions: `‖φ‖` is again locally
constant with compact support, and a nonnegative Schwartz--Bruhat function is
its own norm. JPSS calls a gauge "positive". The values on `A_r` are `≥ 0`,
and the Iwasawa decomposition `GL_r(F) = N_r A_r K_r` makes `ξ ≥ 0`
everywhere, so this needs no separate condition. The definition is also
JPS (1979), (2.3.1)-(2.3.2), printed page 183.

Statement: assume `ρ` is of Whittaker type and has a unitary central
character `ω`, that is, `ρ(z·1) v = ω(z) v` with `|ω(z)| = 1`. Then for every
`v` there is a gauge `ξ` with `|ℓ(ρ(g)v)| ≤ ξ(g)` for all `g`. Here `ℓ` is
the Whittaker functional. This is the sentence "each `W ∈ W(π; ψ)` is
majorized by a gauge" of JPSS (2.5), printed page 388.

## `WhittakerTypeAsymptoticStatement`

A *finite function* on `A_r` is a continuous function whose translates span a
finite-dimensional space. This is the definition recalled in JPSS (2.5) and
JPS (1979), Section 2.2. In Lean the torus is parameterized by
`Fin (n+1) → F^×` with its product topology.

Statement: assume `ρ` is of Whittaker type. Then there is a finite set `X` of
finite functions on `A_r`, depending only on `ρ` (and `ψ`), with the
following property. For every equivariant `ℓ` and every `v` there are
Schwartz--Bruhat functions `φ_χ` on `F^{r-1}` such that for all `a ∈ A_r`

`ℓ(ρ(a)v) = ∑_{χ ∈ X} φ_χ(α_1(a), …, α_{r-1}(a)) χ(a)`.

*Provenance.* JPSS states this expansion, display (2.5)(2), only for generic
`π`. JPS (1979), Remark (2.2.5), printed page 183, extends Proposition (2.2)
to any finitely generated admissible right-translation-stable space of
smooth functions with `W(ng) = θ(n)W(g)`. `W(π; ψ)` is such a space, since it
is a quotient of `ρ` under `v ↦ W_v`. Proposition (2.2) gives the expansion
on the elements `diag(a_1 ⋯ a_{r-1}, …, a_{r-1}, 1)`, that is, on the torus
elements with last entry 1, with finite functions of `α(a)`. Its extension
to all of `A_r` uses the first step of the proof of (2.2), printed page 181.
If the operators of a smooth representation of `F^×` span a
finite-dimensional algebra, then they are `∑_χ χ(z) A_χ` for a finite set of
finite functions `χ`, which depends only on the isomorphism class. The
center acts on the finitely generated admissible space `W(π; ψ)` through
such an algebra; this is the Z-finiteness used in that proof. Writing
`a = z a'` with `z` scalar and `a'_r = 1` gives
`W(a) = ∑_χ χ(z) (A_χ W)(a')`. Applying (2.2) to each `A_χ W` then yields the
displayed form with the finite functions `a ↦ χ(a_r) X_i(α(a))`. This
extension is internal derived content and has no separate locator in the
source.

## `GenericWhittakerAsymptoticStatement`

Statement: assume `ρ` is admissible and irreducible and has a nonzero
equivariant functional. JPSS (2.1), printed page 385, calls such a
representation generic. The conclusion is the same expansion as above, for
every equivariant `ℓ`. This is display (2.5)(2) of JPSS, printed page 388,
citing JPS (1979), Proposition (2.2), printed page 181. A generic irreducible
`π` has a central character `ω`, so `W(z a') = ω(z) W(a')`. The JPS
expansion on the elements with last entry 1 therefore becomes the expansion
on `A_r` with the finite functions `a ↦ ω(a_r) X_i(α(a))`. The functional is
unique up to scalars [G-K], so stating the conclusion for every equivariant
`ℓ` adds nothing.

## Omitted items

- The majorization (2.5)(3) and the remark after it are consequences that
  the source derives from (2), and they are not restated.
- The gauge lemma (2.6), printed page 389, is an estimate internal to the
  convergence proof, stated with block-matrix indexing. It is not a target
  here.
- JPS (1979), Proposition (2.3.6), the gauge bound after the twist
  `|det|^{-σ}` by the central exponent, is not restated separately. It is the
  generic case of `WhittakerGaugeStatement` applied to the twist.

## Family declaration

`WhittakerAsymptoticPrerequisitesStatement` is the conjunction of the three
targets at the same universes `uF` and `uV`. It adds no hypothesis or
conclusion.

## Sources

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin--Selberg
  Convolutions*, Amer. J. Math. 105 (1983), 367-464; registered source
  `jpss-1983-rankin-selberg`, SHA256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
  Printed pages 376, 377, 385 and 388-389 (PDF pages 11, 12, 20, 23 and 24)
  were read visually.
- H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
  GL(3) I*, Ann. of Math. 109 (1979), 169-212; registered source
  `jps-1979-gl3-i`, SHA256
  `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
  Printed pages 181-184 were read in the scan's text layer.

## Dependencies

Published project imports: `Langlands.Group.GL.Basic` (`GeneralLinear`,
`GeneralLinear.scalar`), `Langlands.HarmonicAnalysis.Basic`
(`SchwartzBruhat`), `Langlands.LocalField.Canonical` and
`Langlands.LocalField.Normalization.Definitions` (canonical topology, ring of
integers, normalized absolute value) and
`Langlands.Representation.Smooth.Definitions` (`IsAdmissible`). Everything
else comes from Mathlib.
