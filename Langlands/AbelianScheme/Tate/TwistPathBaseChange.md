# Base change and path transport on the actual Tate twist

Author: Worker 142.

This companion to `PathBaseChange` proves the base-change/path square for
actual root-of-unity kernel points and their Tate twists. On root coordinates
the vertical base-change comparisons are the identity. The result extends to
selected integral and rational limits, the section-ring twist used by the Weil
pairing, full and away finite-adelic scalar structures, and prime-adic twists.

## Sources and provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), printed p.18 / PDF p.26, supplies the full and away inverse-limit and
rationalization conventions. Section III.1, printed pp.90–92 / PDF pp.98–100,
uses the Tate twist in pairing-compatible invariant-orbit levels. The registered
source is `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft,
Chapter X section 3, (10.25)–(10.26), printed p.150 / PDF p.154, defines actual
finite-etale covers and their geometric-fibre functors. Items (10.29)–(10.30),
printed p.151 / PDF p.155, provide change-of-point and pullback conventions,
allowing different geometric endpoint fields. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The displayed squares are internal deductions from the imported actual
root-kernel pullback isomorphism, fibre-functor path pushforward and existing
twist transports. They are not separately quoted source theorems. The Lean
proof first proves the square on morphisms into the actual kernel of
multiplication on the multiplicative group, then passes to root coordinates,
inverse limits and scalar extension.

## Parameters and actual finite points

Fix `b : S' ⟶ S`, field-valued points `s : Spec Ω ⟶ S'` and
`t : Spec Ω' ⟶ S'`, and a path
`p : fiberFunctor s hs ≅ fiberFunctor t ht`. The fields are independent.
Finite-fibre witnesses at the two points and their composites with `b` are
explicit. Write `b_*p` for the actual `pathPushforward b hsb htb p`.

For a natural order `n`, `mu.pointsBaseChangeEquiv_pathAct` proves

```text
baseChange_t (pathAct p x) = pathAct (b_*p) (baseChange_s x).
```

Here `x` is a morphism from `Over.mk s` to the actual root kernel
`(mu S' n).X`, and each base-change map is `mu.pointsBaseChangeEquiv`.
Finiteness and etaleness of the root kernels on both bases are explicit
typeclass hypotheses. The finite statement itself imposes no additional
positivity or invertibility assumption on `n`.

The proof takes the actual scheme morphism from the root kernel on `S'`
to the root kernel on `S`: first the inverse canonical `mu.baseChangeIso`,
then the first pullback projection. Its compatibility with the structure
morphisms follows from the pullback equation and the isomorphism's equation
over `S'`. The characterization
`pathPushforward_apply_left_of_comp` then gives equality of transported
underlying scheme morphisms. `mu.pointsBaseChangeEquiv_left` identifies those
maps with the existing root-kernel comparison, and extensionality gives the
desired equality over the base.

## Root coordinates and selected limits

`levelTransport_baseChange` states that transport along `b_*p` on the actual
root coordinate `Level Ω n` equals transport along `p`. Although the endpoint
fields may differ from each other, base change retains each endpoint field.
The vertical comparison therefore preserves the root itself.

To prove this, `mu.levelEquiv` expresses a root as an actual kernel point.
`mu.levelEquiv_pointsBaseChangeEquiv` identifies its unchanged coordinate on
the original base. Rewriting the two transports by `levelTransport_kernel`
and using the finite point square proves the root equality. This argument
uses actual root-kernel points rather than an assumed comparison of actions.

For `P : ℕ → Prop`, the selected index `Index P` retains positive orders
satisfying `P`. Assume finite-etale root kernels at every such order on each
base. `integralTransport_baseChange` proves equality on
`Divisibility.Integral Ω P` by extensionality at every retained coordinate.
`rationalTransport_baseChange` proves the equality on
`Divisibility.Rational Ω P = ℚ ⊗[ℤ] Divisibility.Integral Ω P`.
Tensor induction reduces pure tensors to the integral result and handles
sums by additivity.

## Section-ring and adelic twists

`sectionRationalTransport_baseChange` gives the equality for the twist over
`Γ((Over.mk s).left, ⊤)` with target over `Γ((Over.mk t).left, ⊤)`.
The canonical `sectionRationalEquiv` is induced by `Scheme.ΓSpecIso`; it
depends only on the endpoint field and is the same for the point and its
composite with `b`. Conjugating the field-coordinate equality by these two
comparisons proves the section-ring equality. Thus the vertical comparisons
in this section-ring square are also the identity.

`sectionFiniteAdeleTransport_baseChange` states the same equality with one
`RationalProfiniteIntegerAdeleComparison` used throughout. The underlying maps
remain the section rational transports, so the proof is the preceding
equality. Taking `P := fun _ => True` gives the full twist.

`sectionPrimeToFiniteAdeleTransport_baseChange` uses one coupled
`PrimeToRationalProfiniteIntegerAdeleComparison` and the selection
`P := fun n => Nat.Coprime n m`. Only the retained positive orders require
finite-etale root kernels. The result again has exactly the section rational
maps on underlying elements. Prime `m = p` gives the prime-to-`p` system;
the Lean theorem permits any natural modulus.

## Prime-adic twists and scope

For a prime `ℓ`, assume finite-etale root kernels at all orders `ℓ ^ n` on
both bases. `primeTransport_baseChange` proves equality of transports on the
actual integral prime-adic twist by coordinate extensionality and the finite
root equality at each power. `rationalPrimeTransport_baseChange` first makes
this an equality of `ℤ_[ℓ]`-linear maps, then applies scalar extension
`LinearMap.baseChange ℚ_[ℓ]` and evaluates. It is the rational prime-adic
twist comparison with the existing scalar structure.

All results concern a supplied path. They neither produce paths nor require
connectedness, local noetherianity or algebraic closure for these conditional
equalities. No primitive root, basis of the twist, or trivialization is chosen.
The finite-etale root hypotheses remain assumptions; the module does not
derive them from characteristic or invertibility. The companion
`PathBaseChange` proves the corresponding actual abelian Tate-module square.
Restriction to Weil-compatible frames and invariant orbit levels additionally
uses the existing geometric pairing compatibility.
