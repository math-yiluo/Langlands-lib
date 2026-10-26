# Surjectivity of compact induction from a closed subgroup

Worker 440 proves the published
`Langlands.Induction.CompactInductionSurjectivityStatement.{uG,uV,uW}` as
`Langlands.Induction.compactInductionSurjectivity`.
The implementation follows the smooth-lift and quotient-cutoff route specified
by Worker 182. The statement and every imported Lean/Markdown pair are unchanged.

## Exact target and conventions

The theorem has exactly the published proposition as its type:

```lean
theorem compactInductionSurjectivity :
    CompactInductionSurjectivityStatement.{uG,uV,uW}
```

The proposition quantifies internally over a Hausdorff topological group
`G : Type uG`, compact open subgroups cofinal among its open subgroups, a closed
subgroup `H`, arbitrary complex modules `V : Type uV` and `W : Type uW`,
smooth representations `sigma` and `tau` of `H`, and a surjective actual
intertwiner `T : sigma.IntertwiningMap tau`. It concludes surjectivity of
`compactInducedMap H T`. The three universes are independent.

The cofinality hypothesis is precisely
`∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
IsCompact (L : Set G) ∧ L.toSubgroup ≤ K.toSubgroup`.
It is used through the published smooth-surjectivity theorem. No compact open
neighborhood basis is inferred or added. The coefficient modules carry no
topology, norm, completeness, dimension, admissibility, or length assumption.
There is no compact-quotient or extra lifting assumption.

The carriers and maps are those of
[`Induction.Definitions`](Definitions.md). An element of
`CompactFunctions H sigma` is an actual function with covariance
`F(h*x) = sigma(h)(F(x))`, one uniform open right stabilizer, and compact
projected nonzero support
`quotientMap H '' Function.support F` in `LeftQuotient H`.
This left-coset space `H \ G` has the quotient topology. The action remains
right translation, `(g*F)(x) = F(x*g)`, and `compactInducedMap H T` remains
postcomposition by `T`.

## Implemented proof

The helper `isOpen_quotientSupport` applies to any commutative ring `R`,
topological group `G`, subgroup `H`, module `V`, representation `sigma`,
and `f : SmoothFunctions H sigma`. Its coefficient, group, and module
universes are independent. It requires neither closedness of `H` nor
compactness or a smoothness hypothesis on `sigma`.

The published `quotientMap_preimage_quotientSupport` identifies the preimage
of the projected support with the actual nonzero support, using covariance
to saturate the latter under `H`. The published `eval_isLocallyConstant`
implies that the zero fiber is closed, hence its complement is open.
Mathlib's quotient-map criterion transfers this openness to the quotient.
Together with the published `isClosed_quotientSupport`, the projected support
of a smooth induced function is therefore both open and closed.

Now fix `f : CompactFunctions H tau`. Apply
[`smoothInductionSurjectivity`](SurjectivityProof.md) to `f.val`, obtaining
`F : SmoothFunctions H sigma` with `smoothInducedMap H T F = f.val`.
Let

```text
C = quotientSupport H (eval H tau f.val).
```

Membership of `f` in `CompactFunctions` supplies compactness of `C`.
The helper supplies openness. Form the published
`F' = smoothQuotientCutoff H sigma C hc ho F`, so

```text
F'(x) = if quotientMap H x ∈ C then F(x) else 0.
```

This constructor preserves covariance because the quotient class is unchanged
under left multiplication by `H`. It also supplies a single open subgroup
fixing the whole cutoff on the right. Concretely, it intersects the chosen
uniform open right stabilizer of `F` with
`compactQuotientOpenStabilizer H C hc ho`, the proved open setwise stabilizer
of `C`. Every element of this intersection preserves both the condition in
the displayed formula and the value of `F`. Thus the construction provides
the required uniform stabilizer, beyond pointwise local constancy.
These facts are proved in the imported
[`CompactQuotientCutoff`](CompactQuotientCutoff.md) construction.

The published support formula gives

```text
quotientSupport H F' = C ∩ quotientSupport H F.
```

Consequently the projected support of `F'` is contained in compact `C`.
It is closed by `isClosed_quotientSupport`, applied to the actual smooth
function `F'`. A closed subset of a compact set is compact, so Lean bundles
`F'` as an element of `CompactFunctions H sigma`. This argument concerns
the actual projected nonzero support.

Finally, equality under `compactInducedMap H T` reduces by subtype and
function extensionality to `T(F'(x)) = f(x)`. If `quotientMap H x ∈ C`, the
cutoff keeps `F(x)`, and evaluation of the smooth lifting identity gives
the equality. Otherwise `F'(x) = 0`. If `f(x)` were nonzero, its own quotient
class would belong to its projected support `C`; hence `f(x) = 0`.
Linearity gives `T(0) = 0`, finishing the equality outside `C` as well.

## Provenance and dependencies

This is an internal derived proof from the published modules
`Induction.CompactSurjectivityStatement`, `Induction.SurjectivityProof`, and
`Induction.CompactQuotientCutoff`, with the support and local-constancy lemmas
from their imported `Induction.CompactQuotientProof`. The lemma on openness
uses pinned Mathlib's quotient topology and locally constant function API.
The proof introduces no new construction assumptions or axioms.

The target's original source is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4)
10 (1977), 441–472, source ID `bernstein-zelevinsky-1977-induced-i`,
SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
Sections 1.1 and 1.2 (printed pp.442–443 / PDF pp.3–4) and 1.8(a),
the trivial-`U` remark, and 1.9(a) (printed pp.444–445 / PDF pp.5–6)
were read; the last two pages were also checked visually. No source-specific
project errata note was present.

Section 1.8(a) defines covariance, a common open right stabilizer, right
translation, and compact support modulo `MU`. Set `U = {e}`, its character
trivial, and `M = H`; the normalization factor becomes one. Proposition
1.9(a) states exactness of induction and compact induction. The source's
`l`-group condition implies the target's open-subgroup cofinality; the target
uses this weaker condition as an internal generalization. The implemented
smooth-lift/cutoff argument proves compact surjectivity under that condition.
The proof referred to in the source's reference [1], chapter I, was not used.

## Development checks

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`), the module
compiled with zero errors and warnings. A Lake-build declaration inspection
reported a theorem with exactly the three universe parameters `uG`, `uV`,
`uW`, and only `propext`, `Classical.choice`, and `Quot.sound` as axioms.
These are development checks; independent semantic review, official
exact-target validation, and Library publication are separate requirements.
