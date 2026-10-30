# Compact induction from locally constant covariant functions

This internal construction turns a locally constant covariant function with
compact actual projected nonzero support into an element of the published
compact-induction module. Worker 199 implemented the Lean proof and this
companion; Worker 76 supplied the compact-representative and inverse-neighborhood
proof route in the prerequisite task. Both are contributing authors.

The entry declaration is
`Langlands.Induction.compactFunctionOfLocallyConstant`, in
`Langlands.Representation.Induction.CompactLocallyConstant`. It takes:

- a commutative ring `R : Type uR`;
- a locally compact topological group `G : Type uG`;
- an actual subgroup `H : Subgroup G` and `hH : IsClosed (H : Set G)`;
- an `R`-module `V : Type uV` and any `σ : Representation R H V`;
- an actual function `f : G → V`;
- covariance `∀ (h : H) (x : G), f ((h : G) * x) = σ h (f x)`;
- `IsLocallyConstant f`;
- `IsCompact (quotientSupport H f)`.

It returns exactly `CompactFunctions H σ`. The ring, group and coefficient
universes remain independent; the returned carrier has universe `max uG uV`,
as in the existing definition. The coefficient module has no topology.
There is no Hausdorff hypothesis on `G`, and `H` need not be open or normal.
The representation `σ` need not be smooth, admissible or finite dimensional.
No open fixing subgroup is supplied by the caller.

The simp theorem `eval_compactFunctionOfLocallyConstant` gives, for every `x`,

```lean
eval H σ (compactFunctionOfLocallyConstant H hH σ f hcov hlc hc).1 x = f x
```

This equation is definitional. In particular the constructed vector retains
the original function and its actual projected nonzero support.

## Stabilizer and support

`rightFunctionStabilizer f` is the actual subgroup

```lean
{g : G | ∀ x, f (x * g) = f x}
```

Its subgroup laws are proved by associativity and applying the fixing equation
at `x * g⁻¹`. `mem_rightFunctionStabilizer` is its simp membership formula.
`mul_mem_support_iff_of_mem_rightFunctionStabilizer` proves that each of its
elements preserves the actual nonzero support.

`quotientMap_mem_quotientSupport_iff_of_covariant` proves directly for the raw
function that `quotientMap H x` lies in its projected support exactly when
`f x ≠ 0`. If a nonzero value at `y` projects to the same coset as `x`, then
`y * x⁻¹ ∈ H`; covariance would force `f y = 0` if `f x = 0`. The converse is
the defining image witness. This lemma needs only the algebraic hypotheses.
It does not presuppose the uniform stabilizer being constructed here.

## Implemented compactness argument

`exists_nhds_one_eq_on_isCompact` first handles any locally constant function
`f : G → V` and compact set `C : Set G`, without requiring covariance or a
module structure on `V`. Near `(1,c)`, local constancy and continuity of
`(g,y) ↦ y*g` give `f(y*g) = f(c)`, while local constancy along the second
projection gives `f(y) = f(c)`. Hence `f(y*g) = f(y)` on a neighborhood of
`(1,c)`. Mathlib's
`IsCompact.eventually_forall_of_forall_eventually` makes this uniform for
every `c ∈ C`: there is `U ∈ 𝓝 1` with
`f(c*g) = f(c)` for every `g ∈ U` and every `c ∈ C`. This step uses
compactness of `C`, rather than intersecting an unrestricted collection of
pointwise neighborhoods.

`isOpen_rightFunctionStabilizer_of_isCompact_quotientSupport` then applies
the published
`Langlands.QuotientIntegration.leftQuotient_exists_isCompact_image` to the
compact set `quotientSupport H f`. This gives a compact `C ⊆ G` whose image
is exactly that set. The quotient and projection are the existing left-coset
objects: `LeftQuotient H = Quotient (QuotientGroup.rightRel H)` and
`quotientMap H`. The quotient-support convention is unchanged.

For `f x ≠ 0`, choose `c ∈ C` with the same projected coset. Then
`h = x*c⁻¹ ∈ H` and `x = h*c`. For every `g ∈ U`, covariance gives

```text
f(x*g) = σ(h)(f(c*g)) = σ(h)(f(c)) = f(x).
```

This proves uniform invariance at all nonzero points. To treat a point with
`f x = 0`, use `g ∈ U ∩ U⁻¹`. If `f(x*g) = 0` the desired equality holds.
Otherwise the nonzero-point argument applies at `x*g` with `g⁻¹ ∈ U`,
giving `f x = f(x*g)`. Thus every `g ∈ U ∩ U⁻¹` fixes the whole function.
Inversion continuity makes this intersection an identity neighborhood.
Mathlib's `Subgroup.isOpen_of_mem_nhds` therefore proves that the actual
`rightFunctionStabilizer f` is open.

`locallyConstantCompactOpenStabilizer` bundles that same subgroup as an
`OpenSubgroup G`. The entry constructor passes it, its defining fixing
equation and the original compact-support proof to the existing
`compactFunctionOf`. The result belongs to the existing `CompactFunctions`,
with its single uniform open stabilizer established in Lean.

## Provenance and scope

This arbitrary-ring constructor and its compactness proof are internal derived
mathematics. No assertion is attributed verbatim to Bernstein–Zelevinsky or
another original source. The module imports the current published mathematics
by Lean name:

- Worker 15's
  [`Induction.Definitions`](Definitions.md) supplies the actual
  compact-induction carrier, covariance, support convention and
  `compactFunctionOf`.
- Worker 53's
  [`Induction.CompactQuotientProof`](CompactQuotientProof.md) supplies the
  existing public smooth-function support API and makes clear the distinction
  between local constancy and a uniform open stabilizer. Its forward
  local-constancy theorem is not used as a converse.
- Worker 113's
  [`Analysis.Local.QuotientTopology`](../../Analysis/Local/QuotientTopology.md)
  supplies compact lifting for this actual left quotient under exactly local
  compactness of `G` and closedness of `H`. The use here is of that published
  theorem, without a new claim about its original literature.
- Pinned Mathlib supplies the local-constancy, compactness, inversion and open
  subgroup lemmas used in the proof.

These imported Lean/Markdown pairs are preserved. Closedness and compact
projected support are hypotheses of this intermediate constructor and must be
established in each application. This unit proves no relative restriction
equivalence, induction in stages, orbit integration, measure comparison,
character cancellation or normalized Jacquet comparison.

The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
Development compilation and entry inspection succeeded with no errors or
warnings, independent `uR/uG/uV`, and only `propext`, `Classical.choice` and
`Quot.sound`. Independent semantic review and Library publication are separate
requirements.
