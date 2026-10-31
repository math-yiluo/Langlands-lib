# Compact induction restricted to a split kernel

This pair constructs `Langlands.Induction.splitKernelCompactEquiv`. It is an
internal prerequisite for the parabolic-orbit comparison, written for task
`0f8b0a2a-b717-4f85-9163-c47e4dd86127` by Worker 76 (the shared draft with the
construction, covariance, support, local-constancy and naturality arguments)
and Worker 835 (the separately named compactness, stabilizer, coordinate-formula,
inverse-law and equivariance lemmas, and this description). It does not
construct an orbit integral or prove the normalized Jacquet comparison.

## Inputs and actual representations

Let `R` be a commutative ring, `G` a locally compact topological group, `L` a
group with a topological space, and

```text
r : G →* L,   s : L →* G,   r (s l) = l.
```

Both maps are continuous. Let `H` be a closed subgroup of `G` containing every
`s l`, and let `σ` be a smooth `R`-linear representation of `H` on an arbitrary
module `V`. The Lean universes of `R`, `G`, `L`, and `V` are independent.
No compatibility between the topology and group operations of `L` is needed:
all continuity arguments use the supplied maps and the topological group
operations of `G`. The declarations therefore apply verbatim to every
topological group `L`. No topology on `V` is used.

Put `N = r.ker` and `I = H.comap r.ker.subtype`, with their actual subgroup
topologies. The homomorphism `j = r.ker.subtype.subgroupComap H : I →* H`
is induced by inclusion. The constructed equivalence is

```text
((compactInduced H σ).comp r.ker.subtype) ≃
    compactInduced I (σ.comp j),
```

as a `Representation.Equiv` of `N`-representations. Both carriers are the
published `CompactFunctions` subtypes: covariant functions with a uniform open
right stabilizer and compact actual projected nonzero support. Actions are
ordinary right translation.

No Hausdorffness, openness or normality of `H`, compact-open subgroup basis,
admissibility, or dimension assumption is imposed. Local compactness of `N` is
not needed for the construction.

## Formulas and inverse laws

The existing `splitKernelCoordinate r s hrs g` is the actual element

```text
n(g) = s(r(g))⁻¹ * g ∈ N.
```

The helper `splitKernelSection s H hsH` lifts `s` to a homomorphism `L →* H`.
The forward map restricts a function:

```text
(E f)(n) = f(n).
```

The inverse uses the actual coefficient action:

```text
(E⁻¹ k)(g) = σ(s(r(g))) (k(n(g))).
```

The `s(r(g))` in this formula is lifted into `H` by `splitKernelSection`.
The two displayed identities are the lemmas `splitKernelCompactEquiv_eval`
and `splitKernelCompactEquiv_symm_eval`. The lemma
`splitKernelCompactEquiv_symm_eval_coordinates` restates the inverse formula
with both lifts written out: the coefficient element is the subtype element
`⟨s (r g), hsH (r g)⟩ : H`, and `k` is evaluated at the kernel element
`⟨(s (r g))⁻¹ * g, _⟩ : r.ker`, whose membership proof is
`map_splitKernelCoordinate`. All three hold by `rfl`.

Covariance recovers `f(g)` from `f(n(g))`, since
`g = s(r(g)) * n(g)`. This is `splitKernel_apply_eq` and proves the
left inverse. On `n ∈ N`, `r(n) = 1`, so `s(r(n)) = 1` and `n(n) = n`.
The lemma `splitKernelExtendFunction_coe` therefore proves the right inverse.
Linearity of restriction is pointwise; these laws bundle it as a linear
equivalence. Its intertwining field compares evaluation at the same product
`x * n` in `N` and in `G`, proving actual kernel equivariance.

The bundled laws are also stated as named theorems:
`splitKernelCompactEquiv_symm_apply_apply` (`E⁻¹ (E f) = f`) and
`splitKernelCompactEquiv_apply_symm_apply` (`E (E⁻¹ k) = k`) are instances
of Mathlib's `Representation.Equiv.symm_apply_apply` and
`Representation.Equiv.apply_symm_apply`. Kernel equivariance is
`splitKernelCompactEquiv_translate`:

```text
E (compactInduced H σ (n : G) f) = compactInduced I (σ.comp j) n (E f)
```

for every `n ∈ N`, obtained from the intertwining field via
`Representation.IntertwiningMap.isIntertwining`.

## Covariance, support and smoothness

Write `a = s(r(hg))`, `b = s(r(g))`, and `p = a⁻¹ * h * b` for `h ∈ H`,
with all three elements lifted into `H`. Then `r(p) = 1`, and

```text
n(hg) = p * n(g),       a * p = h * b.
```

Covariance of `k` under the actual element `p ∈ I` proves full `H`-covariance
of its extension. This is the implemented proof of
`splitKernelExtendFunction_covariant`; no action of `I` is assumed trivial.

Let `q` denote `splitKernelLeftQuotientHomeomorph`, the independently
constructed homeomorphism

```text
q : I \ N ≃ₜ H \ G.
```

Its forward map is induced by inclusion and its inverse by `n(g)`. The two
support lemmas in this module give exact identities for the published
`quotientSupport`, the image of the nonzero support:

```text
quotientSupport I (f restricted to N) = q⁻¹ '' quotientSupport H f,
quotientSupport H (extended k)        = q    '' quotientSupport I k.
```

The first identity uses covariance to show that a nonzero value at `g`
forces a nonzero value at `n(g)`. For the second, every `σ(h)` is invertible,
so multiplying a coefficient value by `σ(s(r(g)))` preserves whether it is
zero. Compactness follows by continuous image in each direction: the
lemmas `isCompact_quotientSupport_splitKernel_restrict` and
`isCompact_quotientSupport_splitKernelExtendFunction` push the compact
support of the given compact-induced function through `q⁻¹` and `q`,
respectively. These are statements about the actual quotient support,
without a replacement support model or an assumed compactness property of
the desired maps.

For restriction, `exists_openSubgroup_splitKernel_restrict` pulls the
uniform open right stabilizer `K` of the smooth function back along the
continuous kernel inclusion, giving the open subgroup `K.comap r.ker.subtype`
of `N`. It uses only the group and the subgroup topology on `N`, not the
topology of `L`. The definition `splitKernelCompactRestrict` passes this
stabilizer and the compactness lemma to the published constructor
`compactFunctionOf`.

For extension, `k` is locally constant by the existing smooth-function
evaluation lemma. The kernel coordinate and the lifted section coordinate
are continuous. Smoothness of `σ` makes each orbit map
`h ↦ σ(h)(v)` locally constant: the proof uses a right translate of the open
subgroup fixing `v`. Near a given `g`, first fix the value `k(n(g))` by local
constancy of `k`, then fix its image under the section coefficient action.
The intersection of these neighborhoods proves local constancy of the
extension. The published constructor `compactFunctionOfLocallyConstant`
upgrades its proved covariance, local constancy and compact quotient support
to a uniform open right stabilizer, namely the right stabilizer
`locallyConstantCompactOpenStabilizer` of the extended function. The lemma
`exists_openSubgroup_splitKernelExtendFunction` exhibits that same open
subgroup of `G` and its fixing property, so the uniform stabilizer of the
extension is a named result. This is where local compactness of `G` and
closedness of `H` enter. Pointwise local constancy alone is not substituted
for a smooth-induced vector.

## Naturality and provenance

For any smooth `τ` on another `R`-module `W` in an independent universe,
`splitKernelInducingMap r H T` restricts any intertwiner `T : σ → τ` along
`j`. The theorem `splitKernelCompactEquiv_natural` states

```text
E_τ (compactInducedMap H T f)
  = compactInducedMap I (splitKernelInducingMap r H T) (E_σ f).
```

Both sides evaluate to `T(f(n))`; the proof is subtype extensionality and
pointwise definitional equality. This is naturality for every coefficient
intertwiner, rather than only an isomorphism for a selected representation.

The arbitrary-ring interface and its proof are internal derived constructions
from the published compact-induction definitions, the split-kernel quotient
homeomorphism, and the compact locally constant constructor. They are not
asserted verbatim from external literature, in particular not from
Bernstein-Zelevinsky. No Haar measure, coinvariant comparison, normalizer
action, or normalization-character cancellation is provided here.

The two focused prerequisites are imported from their published Library pairs,
`Langlands/Analysis/Local/SplitKernelQuotient` (for `splitKernelCoordinate`
and `splitKernelLeftQuotientHomeomorph`) and
`Langlands/Representation/Induction/CompactLocallyConstant` (for
`compactFunctionOfLocallyConstant` and `locallyConstantCompactOpenStabilizer`).
They are not copied into this pair. The construction uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.
