# A compact convex set of trace-normalized kernels

Module `Langlands.Analysis.TraceNormalizedKernelCone` fixes a complex `*`-algebra `𝒜` with a norm
(`NormedRing`, `StarRing`, `Algebra ℂ`, `StarModule ℂ`), an index type `κ`, a complex Hilbert
space `W`, weights `c : κ → ℝ`, a Hilbert basis `e` of `W` and a set `Rel` of relations
`(k₁, b, k₂, A) ∈ κ × 𝒜 × κ × (W →L[ℂ] W)`. A function `F : κ × κ × 𝒜 × W × W → ℂ` is read as
`F (k, k', a, w, w') = ⟪w, B_k ρ(a) B_{k'}^* w'⟫` for a representation `ρ` of `𝒜` and maps `B_k`.

## Definitions

* `kernelOf F` is the kernel `((x, k, w), (y, k', w')) ↦ F (k, k', x^* y, w, w')` on `𝒜 × κ × W`.
* `IsConeElement Rel F` collects: additivity and complex homogeneity in `a`; conjugate linearity
  in `w` and linearity in `w'`; the Hermitian symmetry `conj (F (k', k, x^*, w', w)) = F (k, k', x, w, w')`;
  positivity of `kernelOf F` (`0 ≤ Re (kernelForm (kernelOf F) f f)`); the domination
  `Re (kernelForm (kernelOf F ∘ (a ·)) f f) ≤ ‖a‖² Re (kernelForm (kernelOf F) f f)` (that is,
  `ρ(a)^* ρ(a) ≤ ‖a‖²`); and the relations `F (k₁, k', b x, w, w') = F (k₂, k', x, A w, w')`.
* `IsBoundedForm F`: for all `k, k', a` there is a constant `M` with
  `|F (k, k', a, w, w')| ≤ M ‖w‖ ‖w'‖`. This is only a bound: sesquilinearity is part of
  `IsConeElement Rel F` (the function `‖w‖ ‖w'‖` satisfies the bound and is not sesquilinear).
* `traceSet c e`: every finite partial sum of `∑_{k,b} c_k Re F (k, k, 1, e_b, e_b)` is `≤ 1`.
* `boundSet c`: `|F (k, k', a, w, w')| ≤ ‖a‖ ‖w‖ ‖w'‖ / √(c_k c_{k'})`.
* `coneSet Rel c e` is the intersection of the cone elements, `traceSet c e` and `boundSet c`.

## Results

| Declaration | Content |
| --- | --- |
| `IsConeElement.zero`, `.add`, `.smul` | the cone elements form a convex cone |
| `isClosed_isConeElement`, `isClosed_traceSet`, `isClosed_boundSet` | each condition is closed in the product topology (it is a family of conditions on finitely many coordinates) |
| `isCompact_coneSet` | `coneSet` is compact: it is closed and contained in a product of closed balls (Tychonoff, `isCompact_univ_pi`) |
| `convex_coneSet` | `coneSet` is convex |
| `exists_extremePoint_ne_zero` | if `coneSet` contains a nonzero point, it has a nonzero extreme point |

The last result is the Krein–Milman theorem (`closure_convexHull_extremePoints` in Mathlib) for
the locally convex space `κ × κ × 𝒜 × W × W → ℂ`: if every extreme point were `0`, the set would
be the closure of the convex hull of `{0}`.

## Provenance

Internal. The set plays the role, for operator-valued kernels normalized by a weighted trace, of
the set `P₀` of functions of positive type in G. B. Folland, *A Course in Abstract Harmonic
Analysis*, 2nd ed., CRC Press 2015 (`folland-2015-abstract-harmonic-analysis-second`), §3.3,
printed pp.86–88: `P₀` is weak* compact and the closed convex hull of its extreme points, whose
nonzero elements give the irreducible representations (Theorem 3.25). The trace normalization
replaces the normalization at the identity and is what makes the argument produce the
Gelfand–Kostyuchenko maps of Bernstein's method (J. Bernstein, *On the support of Plancherel
measure*, 1988, §1.5).
