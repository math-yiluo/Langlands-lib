# The right-annihilator uniformity of an idempotented ring

This module constructs the uniform space in David Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, I.1.3, printed
page 8 / PDF page 14. The original nonunital conventions and finite local-unit
definition on printed pages 6–7 / PDF pages 12–13 also govern the construction.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
These original pages were read and the formulas on PDF14 visually checked.
No source-specific project errata entry was present when this unit was prepared.

The construction is by Worker 6; Worker 345 checked the original source, expanded
the documentation and prepared the focused submission. All declarations are in
`Langlands.Algebra`, with the subgroup and entourage API in `Idempotent`
and the common-refinement/directedness laws in `IsIdempotented`. The given `A : Type u` has only
`NonUnitalRing A`; the construction uses its actual multiplication and the
published `Idempotent A` and corner order from
`Langlands.Algebra.IdempotentedRing`. There is no ambient topology, unit,
nontriviality, commutativity, countability or finiteness assumption. Zero rings
are included.

## The actual subgroups

`rightAnnihilator e : AddSubgroup A` has carrier `{a | a * e = 0}`.
Addition and negation preserve this equation by distributivity.
`mem_rightAnnihilator` exposes the defining equation.
`mem_rightAnnihilator_iff_residual` proves

```text
a ∈ rightAnnihilator e ↔ ∃ b : A, a = b - b * e.
```

For the forward implication use `b = a`; for the reverse implication use
`e * e = e`. This is Renard's `A(1-e)` without introducing an ambient unit.
`mul_mem_rightAnnihilator` proves stability under every left multiplication
using associativity. The name refers to the kernel of **right multiplication**;
as a one-sided ideal it is stable on the left.

`rightAnnihilator_antitone` uses the published implication `e ≤ f → f * e = e`:
an element killed by `f` is also killed by `e`. For `hA : IsIdempotented A`,
`rightAnnihilator_common_refinement hA e f` produces an actual `g` with
`e ≤ g`, `f ≤ g`, and
`rightAnnihilator g ≤ rightAnnihilator e ⊓ rightAnnihilator f`.
It applies the published finite-upper-bound theorem to `{e,f}`, then antitonicity.

## The constructed uniform space

`rightCoordinateEntourage e` is the actual subset

```text
{p : A × A | p.1 * e = p.2 * e}.
```

`mem_rightCoordinateEntourage` exposes the coordinate equality;
`rightCoordinateEntourage_eq_annihilator` identifies the whole set with
`{p | p.1 - p.2 ∈ e.rightAnnihilator}`. `rightCoordinateEntourage_antitone` multiplies a coordinate equality on the
right by the smaller idempotent and uses absorption. Thus a common upper bound of idempotents refines their entourages.

`idempotentedRingUniformSpace A : UniformSpace A` is defined for **every**
nonunital ring as

```text
⨅ e : Idempotent A, UniformSpace.comap (fun a : A => a * e) ⊥.
```

Here bottom is Mathlib's discrete uniform space on the original carrier `A`.
The complete lattice of uniform spaces and its actual `comap` construction
supply the uniform-space axioms. No topology or neighborhood basis is assumed.
This discrete-coordinate infimum is an internal realization of Renard's
uniformity: the neighborhood basis proved below is precisely the one in I.1.3.
Renard does not present the construction as a lattice infimum.

`idempotentedRing_uniformity` proves its exact filter formula:

```text
𝓤[idempotentedRingUniformSpace A] =
  ⨅ e : Idempotent A, 𝓟 (rightCoordinateEntourage e).
```

The proof computes the uniformity of the infimum, pulls back the discrete
principal equality filter, and identifies its preimage with coordinate equality.

The definition introduces no global uniform-space or topology instance.
Consumers install it explicitly, for example with
`letI := idempotentedRingUniformSpace A`. Neighborhood statements use this local
instance in their types; coordinate uniform continuity names both uniform
structures explicitly. An independently given topology on `A` is no input.

## Entourage and neighborhood bases

For every `hA : IsIdempotented A`,
`idempotentedRing_uniformity_hasBasis hA` proves the exact assertion

```text
(𝓤[idempotentedRingUniformSpace A]).HasBasis
  (fun _ : Idempotent A => True) rightCoordinateEntourage.
```

The proof uses the actual zero idempotent for nonemptiness and
`IsIdempotented.rightCoordinateEntourage_directed` for directedness under reverse
inclusion, then applies Mathlib's
principal-infimum basis theorem. Consequently single idempotents suffice;
the index is not replaced by finite families or by an assumed basis.

With the constructed uniform space locally installed,
`idempotentedRing_nhds_hasBasis hA b` proves

```text
(𝓝 b).HasBasis (fun _ : Idempotent A => True)
  (fun e => {a : A | (a-b)*e = 0}).
```

The uniform-space neighborhood-basis theorem evaluates the entourage at `(a,b)`,
then distributivity identifies the fiber with this displayed set. These sets
are the translates `b + rightAnnihilator e` in the sense of their membership
equation. At zero, `idempotentedRing_nhds_zero_hasBasis hA` specializes
to the actual carriers `(rightAnnihilator e : Set A)`. These are exactly the
source's translated right-annihilator neighborhoods.

Finally, `idempotentedRing_uniformContinuous_rightCoordinate e` proves
uniform continuity of the original map `a ↦ a * e` to the discrete uniformity
on `A`. The infimum is below its `e`-indexed comap; the comap characterization
of uniform continuity gives the conclusion. This law does not need
idempotentedness.

The additive direct-sum decomposition, zero/one pseudometrics and their
comparison, topological group laws, separation, inverse limits, density,
completeness, completed multiplication, and module action extension remain
separate obligations. This module constructs neither a completion nor the
distinct left-module completion of I.1.4.

The final anonymous `example` declarations check the complete unapplied
construction, entourage basis, both neighborhood bases and discrete-coordinate
uniform-continuity interfaces in the arbitrary ring universe `u`.
