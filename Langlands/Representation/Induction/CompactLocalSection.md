# Compact covariant sections with a prescribed value

This module constructs `Langlands.Induction.compactLocalSection`, an actual
member of the existing `CompactFunctions P σ`. It takes a smooth representation
`σ`, a point `x : G`, a vector `v : V`, an open set `U : Set (LeftQuotient P)`,
and a proof that `quotientMap P x ∈ U`. Its value at `x` is `v`, and its actual
projected nonzero support is contained in `U`.

## Interface and scope

The coefficient ring `R : Type uR` is any commutative ring; `G : Type uG` is a
group with a topology, `NonarchimedeanGroup G` and
`WeaklyLocallyCompactSpace G`; `V : Type uV` is an additive commutative group
and an `R`-module. All three universes are independent. The subgroup `P` is
arbitrary and `σ : Representation R P V` satisfies `Langlands.IsSmooth σ`.
There is no topology on `V`, and neither finite dimensionality nor
admissibility is assumed. `NonarchimedeanGroup G` supplies the topological
group instance.

The requested case of a locally compact Hausdorff group, a closed subgroup,
and a smooth complex representation is obtained by setting `R = ℂ`;
Mathlib infers weak local compactness from local compactness. Closedness of
`P` and the Hausdorff assumption are unnecessary for this construction.

The explicit argument order is:

```lean
compactLocalSection (P : Subgroup G) (σ : Representation R P V)
  (hσ : IsSmooth σ) (x : G) (v : V) (U : Set (LeftQuotient P))
  (hU : IsOpen U) (hx : quotientMap P x ∈ U) : CompactFunctions P σ
```

For `s := compactLocalSection P σ hσ x v U hU hx`, the intrinsic laws are:

- `compactLocalSection_apply`: `eval P σ s.val x = v`.
- `compactLocalSection_support_subset`:
  `quotientSupport P (eval P σ s.val) ⊆ U`.

Here `LeftQuotient P` is the actual quotient by `QuotientGroup.rightRel P`,
whose cosets are `P * g`. The support is the image under `quotientMap P` of
the set where the function is nonzero. It is not a chosen support bound or
a closure substituted for that set. The return type carries covariance,
a single open right stabilizer for the entire function, and compactness
of this actual projected support. The constructor uses classical choice;
no claim of linear dependence on `v` is made for its choice of subgroup.

## Double-coset construction

The public auxiliary operation `compactDoubleCosetSection` requires only a
topological group, a compact open subgroup `K`, a point `x`, a vector `v`,
and the hypothesis

```lean
v ∈ fixedVectors σ (conjOpenSubgroup P K x).toSubgroup
```

It does not require global smoothness of `σ` or local compactness of `G`.
It returns the section whose value at `p * x * k` is `σ p v` and whose value
outside `P * x * K` is zero. Internally, `inDoubleCoset` is a Prop-valued
definition expressing the existence of `p : P` and `k : K` with that
factorization. `doubleCosetValue` chooses a factorization when one exists.

To prove that this choice has the required value, suppose
`p * x * k = q * x * l`. Then
`x⁻¹ * (p⁻¹ * q) * x = k * l⁻¹ ∈ K`, so `p⁻¹ * q` belongs to
`conjOpenSubgroup P K x` and fixes `v`. Applying `σ p` gives
`σ q v = σ p v`. This proves representative independence in the private
`doubleCosetValue_eq` lemma. Multiplication on the left by `P` and on the
right by `K` preserves the double coset, proving covariance and uniform
right invariance, including the zero values outside it.

These properties build a `SmoothFunctions P σ` via `smoothFunctionOf`.
Its projected support lies in the image of `K` under
`k ↦ quotientMap P (x * k)`, which is compact by continuity. The published
`isClosed_quotientSupport` makes the actual projected support closed, so
it is compact as a closed subset of that compact image. This step uses
no Hausdorff condition on the quotient.

The auxiliary operation has three public laws:

- `compactDoubleCosetSection_apply` evaluates at every `p * x * k`.
- `compactDoubleCosetSection_support_subset` bounds the projected support
  by the image of `x * K` in `P \ G`.
- `compactDoubleCosetSection_mul` states right invariance under every `k : K`
  at every point of `G`.

## Choosing a sufficiently small subgroup

Smoothness supplies an open subgroup `H` of `P` fixing `v`. By the subspace
topology, choose an open set `O` of `G` whose preimage in `P` is `H`;
`1 ∈ O`. The set of `k : G` satisfying both

```text
x * k * x⁻¹ ∈ O,     quotientMap P (x * k) ∈ U
```

is an open identity neighborhood. The published
`Langlands.compactOpenSubgroupBasis` supplies a compact open subgroup `K`
inside it. If `p ∈ conjOpenSubgroup P K x`, then
`x⁻¹ * p * x ∈ K`, hence `p ∈ O` and therefore `p ∈ H`. Consequently this
conjugate intersection fixes `v`. The second inclusion ensures that the
projected image of `x * K` lies in `U`.

The private `exists_localSectionSubgroup` proves these properties. The
constructor chooses such a subgroup and applies `compactDoubleCosetSection`.
The value law follows by evaluating at `p = 1` and `k = 1`; the support law
is the composition of the two support inclusions.

## Provenance and dependencies

This is an internal derived construction, authored by Worker 53. Its
mathematical inputs are the published definitions and theorems in:

- [`Definitions`](Definitions.md): actual covariant, smooth and compactly
  induced functions, evaluation, and projected support.
- [`CompactQuotientProof`](CompactQuotientProof.md): `conjOpenSubgroup`, its
  membership condition, and closedness of projected support.
- [`NeighborhoodBasis`](../../Topology/CompactOpen/NeighborhoodBasis.md):
  the compact open subgroup basis under weak local compactness and the
  nonarchimedean condition.

These are imported by Lean module name. No external literature theorem or
assumed local section is used. This construction supplies a local ingredient
for a later closed-orbit extension argument; it does not assert or prove
that extension theorem, a sheaf comparison, or global surjectivity of a
restriction map.

The module is checked in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`). The constructor's checked
universe parameters are `uR`, `uG`, `uV`, and its only axioms are `propext`,
`Classical.choice`, and `Quot.sound`. Independent semantic review and
publication are separate from these development checks.
