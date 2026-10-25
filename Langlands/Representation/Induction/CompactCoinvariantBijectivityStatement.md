# Bijectivity of the compact-induction quotient integral

Worker 86 states
`Langlands.Induction.CompactCoinvariantIntegralBijective.{uG,uV}`.
It is a closed, universally quantified `Prop` definition. This module proves
no bijectivity result and constructs no new integral.

For the data specified below, the assertion is

```lean
Function.Bijective
  (Langlands.Induction.compactCoinvariantDesc H σ ν hν.right_invariant)
```

The map is the existing complex linear map

\[
 \overline I_\nu:
   \bigl(\operatorname{cInd}_H^G(\sigma)\bigr)_G \longrightarrow V_H,
 \qquad
 \overline I_\nu([f])=\int_{H\backslash G}[f(g)]\,d\nu(Hg).
\]

Both spaces are actual `Representation.Coinvariants`. The source carrier is
in `Type (max uG uV)` and the target in `Type uV`; `G : Type uG` and
`V : Type uV` have independent universes.

## Exact hypotheses and conventions

The ambient group is Hausdorff and locally compact, with
`IsTopologicalGroup G` and a supplied Borel measurable structure. The
compact-open neighborhood basis is the literal hypothesis used in
`Langlands.Induction.StructuralStatement`:

```lean
∀ O : Set G, IsOpen O → (1 : G) ∈ O →
  ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O
```

The subgroup `H` is closed. It carries its subtype topology and a supplied
Borel measurable structure. The supplied measures `μG : Measure G` and
`μH : Measure H` each satisfy exactly `IsHaarMeasure`, `Regular`, and
`IsMulRightInvariant`, as in
`Langlands.QuotientIntegration.CompatibleMeasureExistsForClosedSubgroups`.
These are regular two-sided Haar hypotheses. They are inputs to this
assertion, not a claim that arbitrary groups and closed subgroups admit
two-sided Haar measures.

The quotient is the existing `QuotientIntegration.LeftQuotient H`,
definitionally `Quotient (QuotientGroup.rightRel H)`, with points `H * g`,
its quotient topology, and a supplied Borel measurable structure.
The statement quantifies a supplied measure `ν` with
`IsFiniteMeasureOnCompacts ν` and the actual property
`hν : QuotientIntegration.IsCompatible H μG μH ν`. This property includes
nonzeroness, regularity, preservation by every actual right translation,
integrability of subgroup averages of continuous compactly supported complex
functions, and their Weil integral formula for `μG` and `μH`. The descent
map receives precisely the field `hν.right_invariant`.

The coefficient carrier has only `AddCommGroup V` and `Module ℂ V`.
The representation `σ : Representation ℂ H V` is required to satisfy
`Langlands.IsSmooth σ`, so every vector has an open stabilizer. Smoothness
and a supplied compatible measure are essential choices in the scope of this
target. The construction module allowed arbitrary inducing representations
and zero measure; this bijectivity statement retains smoothness and excludes
zero measure through `hν.nonzero`. In particular, a zero integral cannot be
included as a general bijectivity assertion.

There is no topology, norm, completeness, finite dimension, admissibility,
or finite length assumption on the coefficient carrier. There is no section,
surjectivity, kernel identity, exactness, or isomorphism assumption. The
existing covariance is `f(h * g) = σ h (f g)` and the ambient action is
right translation `f(x) ↦ f(x * g)`. No character or modulus twist is added.

## Existing laws and separate obligations

The imported `CompactCoinvariantIntegral` module already proves
`compactCoinvariantDesc_mk_integral`, which identifies the representative
formula with the finite-fiber algebraic integral of
`quotientCoinvariantSimple H σ f`. It also proves
`compactCoinvariantDesc_natural` for every algebraic inducing intertwiner,
using the actual `Coinvariants.map` and `compactInducedMap`. Neither law is
replaced by a hypothesis or a new family of maps here.

The separate `Langlands.Analysis.Local.QuotientMeasureExistence` module
proves `Langlands.QuotientIntegration.compatibleMeasureExists` under the
specified regular two-sided Haar hypotheses. Scalar measure existence does
not prove this vector-valued bijectivity target. The present statement
quantifies the compatible quotient measure rather than choosing one.
Its bijectivity proof and any normalizer-equivariance or normalized orbit
comparison remain separate obligations.

## Original source and provenance

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. ENS (4) **10** (1977), 441–472, §5.17,
printed pp.466–467 (PDF pages 27–28). Registered source:
`bernstein-zelevinsky-1977-induced-i`, retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Both cited original pages were read and visually checked.

On p.466 the source integrates the projection of an induced function over
`V' \ V`, including a factor from the inverse character in the twisted
setting, and descends the resulting map to twisted coinvariants. For the
bijectivity argument it reduces to `N = {e}`, `M = V'`, and trivial
character. Rename its ambient group `V` to `G`, its subgroup `V'` to `H`,
and its coefficient space `L` to our `V`. The projected integral then has
exactly the untwisted formula displayed above. With `N` trivial this
specialization makes no assertion about a nontrivial normalizer action.

On p.467 the source treats the regular representation first: its relevant
coinvariant spaces are one-dimensional and the integral is nonzero.
It then passes to direct sums of regular representations, uses free
resolutions, and invokes exactness of its functors. That is the source's
proof route, not an implemented proof in this statement module. None of
those intermediate conclusions or exactness claims is assumed here.

The fully quantified topological-group formulation with an explicitly
supplied compatible measure is an internal formulation of this untwisted
target. The regular two-sided Haar setting deliberately specializes measure
data to the established existence interface used by the unipotent
application. This is not an assertion that BZ77 states this exact Lean
telescope or proves the theorem for arbitrary groups without these inputs.
The imported integral, quotient, and induction pairs are unchanged.
