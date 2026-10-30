# Left quotients for a continuous split group retraction

The internal construction
`Langlands.QuotientIntegration.splitKernelLeftQuotientHomeomorph` takes
the following data:

- a topological group `G` and a group `L` with a topology, in independent
  universes `uG` and `uL`;
- continuous group homomorphisms `r : G →* L` and `s : L →* G`;
- the section identity `hrs : ∀ l, r (s l) = l`;
- a subgroup `H` of `G` with `hsH : ∀ l, s l ∈ H`.

It constructs the actual homeomorphism

```
Langlands.Induction.LeftQuotient (H.comap r.ker.subtype) ≃ₜ
  Langlands.Induction.LeftQuotient H.
```

The first left quotient is formed inside the actual kernel `r.ker`, with
its subgroup topology, by the actual pullback subgroup
`H.comap r.ker.subtype`. Its points are the cosets of `H ∩ ker r` in
`ker r`. The second is the published `H \ G` carrier. Both are
`Quotient (QuotientGroup.rightRel _)` with Mathlib's quotient topology, so
the relation between `x` and `y` means `y * x⁻¹ ∈ H`, as in
`QuotientGroup.rightRel_apply`. The classes are the cosets `H g`. No
algebraically defined quotient replaces these carriers.

Neither `H` nor the kernel-intersection subgroup is assumed normal. There
are no closedness, openness, local compactness, Hausdorff or compactness
assumptions, and no quotient equivalence is supplied as a hypothesis.
The Lean declaration does not require the topology on `L` to be compatible
with its group operations; continuous `r` and `s` suffice. It therefore
applies verbatim when `L` is a topological group.

## The kernel coordinate

`splitKernelCoordinate r s hrs g` is the actual element of `r.ker` with
underlying group value `s (r g)⁻¹ * g` (`coe_splitKernelCoordinate`).
It lies in the kernel because
`r (s (r g)⁻¹ * g) = (r g)⁻¹ * r g = 1` by the section identity. This fact
is recorded as `map_splitKernelCoordinate`. The following lemmas hold:

- `section_mul_splitKernelCoordinate`: `s (r g) * splitKernelCoordinate g = g`.
- `splitKernelCoordinate_coe`: on an element of the kernel the coordinate is
  the identity, because `r g = 1` and `s 1 = 1`.
- `continuous_splitKernelCoordinate`: the coordinate is continuous into the
  subgroup topology. It is the product of the inverse of `s ∘ r` with the
  identity, restricted to the kernel.

## Well-definedness

The forward map `kernelLeftQuotientInclusion r H` is induced by the kernel
inclusion. If `y * x⁻¹ ∈ H ∩ ker r`, then in particular `y * x⁻¹ ∈ H`.
Its representative formula is `kernelLeftQuotientInclusion_mk`.

For the inverse, suppose `y * x⁻¹ ∈ H`. The quotient of the two kernel
coordinates is

```
(s (r y)⁻¹ * y) * (s (r x)⁻¹ * x)⁻¹ = s (r y)⁻¹ * (y * x⁻¹) * s (r x).
```

This lies in `H` because both section factors lie in `H`. It already
lies in the kernel as a product of kernel elements. This is exactly the
relation in `H.comap r.ker.subtype` (`splitKernelCoordinate_rel`).

## Inverse laws and representative formulas

The two inverse laws are proved on quotient representatives, in the
`left_inv` and `right_inv` fields of the homeomorphism. They are available
through Mathlib's `Homeomorph.symm_apply_apply` and
`Homeomorph.apply_symm_apply`.

- Starting from the class of a kernel element `g`, the composite gives the
  class of `splitKernelCoordinate g`, which equals `g` by
  `splitKernelCoordinate_coe`.
- Starting from the class of `g ∈ G`, the composite gives the class of
  `s (r g)⁻¹ * g`. This class equals the class of `g` because
  `g * (s (r g)⁻¹ * g)⁻¹ = s (r g)` lies in `H`. This is the lemma
  `leftQuotientMap_splitKernelCoordinate`.

The representative formulas are definitional:

- `splitKernelLeftQuotientHomeomorph_mk` sends the class of a kernel
  element `g` to `leftQuotientMap H g`.
- `splitKernelLeftQuotientHomeomorph_symm_mk` sends `leftQuotientMap H g`
  to the class of `splitKernelCoordinate r s hrs g`.

## Continuity

Kernel inclusion `Subtype.val` is continuous for the subgroup topology.
The kernel coordinate is continuous by `continuous_splitKernelCoordinate`.
Mathlib's `Continuous.quotient_map'` shows that a continuous map on
representatives that respects the relations descends to a continuous map
of quotient spaces. Thus both directions are continuous for the actual
quotient topologies.

## Provenance and scope

The provenance is an internal elementary group and topology derivation.
It uses only the published left-quotient conventions of
`Langlands.Representation.Induction.Definitions` and
`Langlands.Analysis.Local.QuotientTopology` and Mathlib's quotient and
subgroup APIs. This exact abstract interface is not attributed to any
source as a verbatim theorem. The module constructs only the quotient
homeomorphism and its intrinsic coordinate lemmas. It does not assert a
compact-induction restriction equivalence, a coefficient restriction
equivalence, an orbit integration formula, or a Jacquet comparison.

Authors: Worker 76 and Worker 835.
