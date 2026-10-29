# Compact induction across a continuous split quotient: proof

Worker 777 proves `Langlands.Induction.compactInductionSplitQuotient`. Its type
is exactly the published proposition
`Langlands.Induction.CompactInductionSplitQuotient.{uG, uV}` from
`Langlands.Representation.Induction.SplitQuotientStatement`. The closing
theorem is unapplied and keeps both independent universes `uG` and `uV`. The
module's only direct import is that statement module, whose Lean/Markdown pair
and imported pairs are unchanged.

## Setting

The helpers work in a slightly more general setting than the target. `R` is an
arbitrary commutative ring, `V` an arbitrary `R`-module, and `G`, `L` are
groups in possibly different universes. `r : G →* L` and `s : L →* G` satisfy
`r (s l) = l`. `H` is a subgroup of `G` with `r.ker ≤ H`, and
`σ : Representation R H V`. Topologies, and topological-group structures where
the compact function space needs them, are added only for the continuity
lemmas and the constructions on `CompactFunctions`. Closedness of `H` is never
used: the closing theorem takes that hypothesis and ignores it.

Write `H_L = H.comap s` and `i = s.subgroupComap H : H_L →* H`, as in the
statement.

## Group-theoretic lemmas

- `splitQuotient_mul_inv_mem_ker`: `g * (s (r g))⁻¹ ∈ r.ker`, because
  `r (s (r g)) = r g`.
- `splitQuotient_section_mem`: if `g ∈ H` then `s (r g) ∈ H`. Indeed
  `g * (s (r g))⁻¹ ∈ r.ker ≤ H`, and multiplying its inverse by `g` gives
  `s (r g)`.
- `splitQuotientRetract` packages this as the element `r h` of `H_L` for
  `h ∈ H`.
- `splitQuotient_action_retract`: if `σ` is trivial on every `h ∈ H` with
  `r h = 1` (the published kernel-triviality condition), then
  `σ (i (r h)) = σ h` on every vector. The proof writes `h = p * (p⁻¹ * h)`
  with `p = s (r h)` and notes that `r (p⁻¹ * h) = 1`.

## Covariant functions

`splitQuotient_apply_eq` shows that every `H`-covariant `f : G → V` satisfies
`f g = σ ⟨g * (s (r g))⁻¹, _⟩ (f (s (r g)))`. This is covariance at the kernel
element `g * (s (r g))⁻¹ ∈ H` applied to `s (r g)`. With kernel-triviality,
`splitQuotient_apply_section` concludes `f (s (r g)) = f g`.

## Coset maps and supports

`splitQuotientRetractMap : H \ G → H_L \ L` is `Quotient.map' r`. It is well
defined because `y * x⁻¹ ∈ H` implies `s (r (y * x⁻¹)) ∈ H` by
`splitQuotient_section_mem`. `splitQuotientSectionMap : H_L \ L → H \ G` is
`Quotient.map' s`, well defined by the definition of `H.comap s`. Both are
continuous for the quotient topologies, by `Continuous.quotient_map'`
(`continuous_splitQuotientRetractMap`, `continuous_splitQuotientSectionMap`).

The support lemmas use the published `quotientSupport`, the image in the coset
space of the nonzero support.

- `quotientSupport_comp_section`: for `H`-covariant `f`, the projected support
  of `l ↦ f (s l)` equals the image of the projected support of `f` under
  `splitQuotientRetractMap`. One inclusion uses `r (s l) = l`. For the other,
  if `f g ≠ 0` then `f (s (r g)) ≠ 0`, by `splitQuotient_apply_eq` and
  linearity of `σ`. No kernel-triviality is needed here.
- `quotientSupport_comp_retract`: for any `k : L → V`, the projected support of
  `g ↦ k (r g)` equals the image of the projected support of `k` under
  `splitQuotientSectionMap`. One inclusion uses that `s (r g)` and `g` have the
  same `H`-coset, since `g * (s (r g))⁻¹ ∈ r.ker ≤ H`. The other uses
  `r (s l) = l`.

Hence compactness of projected supports is transported as the continuous image
of a compact set. No quotient homeomorphism, closedness or Hausdorff property
is used.

## The two maps on actual compact functions

Both maps are built with the published constructor `compactFunctionOf`, which
takes the function, its covariance, one open subgroup of uniform right
invariance, and compactness of its projected support.

- `splitQuotientRestrict` sends `f : CompactFunctions H σ` to `l ↦ f (s l)` in
  `CompactFunctions H_L (σ.comp i)`. Covariance under `p ∈ H_L` is covariance
  of `f` under `s p ∈ H`. The uniform stabilizer is the preimage
  `K.comap s hs` of the chosen open stabilizer `K` of `f`, which is open since
  `s` is continuous. Compactness comes from `quotientSupport_comp_section`.
- `splitQuotientExtend` sends `k : CompactFunctions H_L (σ.comp i)` to
  `g ↦ k (r g)` in `CompactFunctions H σ`, for kernel-trivial `σ`. Covariance
  under `h ∈ H` is covariance of `k` under `splitQuotientRetract h`, rewritten
  with `splitQuotient_action_retract`. The uniform stabilizer is
  `K.comap r hr`. Compactness comes from `quotientSupport_comp_retract`.

`splitQuotientEquiv` bundles these into an actual `Representation.Equiv` from
`(compactInduced H σ).comp s` to `compactInduced H_L (σ.comp i)`. Additivity
and scalar compatibility of the forward map hold pointwise by definition. The
right inverse law is `k (r (s l)) = k l`. The left inverse law is
`f (s (r g)) = f g`, from `splitQuotient_apply_section`. Equivariance compares
right translation by `s l` on `G` with right translation by `l` on `L`, using
`s (x * l) = s x * s l`.

## Closing theorem

`compactInductionSplitQuotient` introduces the statement's data and chooses
`e A hA = splitQuotientEquiv r hr s hs hrs H hker A.representation hA`. The
restriction formula and the inverse formula hold by `rfl`, since `eval` reads
the function and the maps are composition with `s` and `r`. Naturality for
`T : A ⟶ B` is checked pointwise: both sides evaluate at `l` to
`T (f (s l))`, because `compactInducedMap` and `restrictAlongMap` both act by
postcomposition with the same linear map.

No support-preservation premise, bijectivity premise, supplied inverse,
alternative function space or extra topological hypothesis is introduced. The
published support and uniform open-stabilizer conditions of `CompactFunctions`
are proved for both maps.

## Source and scope

This proves the internal derived step stated in the statement pair. It is the
complement-restriction part suggested by Bernstein and Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977), §5.16, Case IV₁,
printed pages 465–466 (PDF pages 26–27), with the setup of §5.1 on printed
page 459 (PDF page 20). These pages were reread for this proof. The source
argues with ℓ-sheaves, fibers and the transitive action of `N`. The Lean proof
instead constructs the maps directly on functions, which is an internal route.
The source does not print this comparison as a separate theorem.

The source is registered as `bernstein-zelevinsky-1977-induced-i`, retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
with SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The current Library has no `notes/errata` directory.

The proof is unnormalized and has no character. It does not prove
normalization, the actual parabolic specialization, the Case IV₂ quotient
integration of §5.17, or the full orbit comparison. The same-ambient
coinvariant step is the separate published theorem
`Langlands.Induction.compactInductionNormalCoinvariants`.

Development checks used environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
The closing theorem compiles without warnings and depends only on `propext`,
`Classical.choice` and `Quot.sound`. Compilation is development evidence;
independent semantic review and Library publication remain required.
