# Vanishing of a one-cell open restriction: statement

Authors: Worker 634 (transport design) and Worker 1005 (statement packaging
and documentation).

`Langlands.Whittaker.BruhatCellRestrictionVanishingStatement.{u}` is a
`Prop`-valued definition. It states a conditional transport result for
distributions on the actual matrix group and its actual upper Bruhat cells.
This pair defines the proposition; it supplies no proof of that proposition
or of global Shalika invariance.

## Quantifiers and spaces

For every natural number `n` and every `K : Type u` in an arbitrary universe,
assume `[Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]`.
Assume also local compactness and total disconnectedness of the actual group
`G = Langlands.GeneralLinear (n + 1) K`. These last two instances are on `G`,
with its published topology on matrix units. The statement adds no separate
local compactness or total disconnectedness hypothesis on `K`.
The rank is `n + 1`, so it includes rank one at `n = 0`.

Quantify over every `w : Equiv.Perm (Fin (n + 1))` and every bundled
`ψ : UnitaryAdditiveCharacter K`. This bundle is a continuous, nontrivial
additive character with values in the complex unit circle. Write

```text
ℓ(w) = permutationInversionCount (n + 1) w,
C_w  = upperBruhatCell (n + 1) K w,
L    = upperBruhatLayerLE (n + 1) K ℓ(w),
O    = upperBruhatCellNeighborhood (n + 1) K w.
```

Here `L` is the union of all actual cells with inversion count at most `ℓ(w)`,
and `O` is `C_w` together with all actual cells of strictly larger inversion
count. The imported geometry proves `L` closed, `O` open, and
`O ∩ L = C_w`. The cell type is the published subtype
`UpperBruhatCell (n + 1) K w`, with its inherited topology.

For any of these spaces `X`, `SchwartzBruhat X` is the complex vector space
of locally constant, compactly supported functions on `X`, and
`Distribution X` is its full complex algebraic dual. There is no continuity
condition on a distribution. The next quantifier is exactly
`D : supportedOn L`. Its ambient coercion is a distribution on `G` that
annihilates every test function vanishing pointwise on `L`:

```text
∀ f : SchwartzBruhat G, (∀ g ∈ L, f g = 0) → D f = 0.
```

This is the published pointwise-annihilator support convention.

## Premises and conclusion

The first premise is global `IsBiEquivariantDistribution ψ n D`.
With `χ = standardCharacter ψ n`, it says that for every pair of actual
upper-unipotent elements `u₁, u₂` and every ambient test function `f`,

```text
D (g ↦ f (u₁ * g * u₂)) = (χ(u₁) * χ(u₂)) * D f.
```

The notation on the left abbreviates the published test-function pullback;
both character values on the right are coerced to `ℂ`. Both character
factors are positive, with the same convention in the global and cell
predicates.

The second premise is the actual equation `pushforward τ D = -D`, where
`τ = weylTransposeHomeomorph n K`. It is the involution
`g ↦ J * transpose(g) * J`, with `J = weylLong (n + 1) K`.
Distribution pushforward satisfies `(pushforward τ D) f = D (f ∘ τ)`.

The third premise is the following disjunction:

1. Every `E : Distribution (UpperBruhatCell (n + 1) K w)` satisfying
   `IsBiEquivariantBruhatCellDistribution n K w ψ E` is zero.
2. There exists a proof
   `hτ : Set.MapsTo τ C_w C_w` such that every distribution `E` on that
   same actual cell satisfying the same positive bi-equivariance predicate
   is `IsWeylTransposeInvariantBruhatCellDistribution n K w hτ E`.
   This last predicate means that pushforward by the actual restricted
   homeomorphism `bruhatCellWeylTranspose n K w hτ` fixes `E`.

Each branch quantifies over all cell distributions `E`; neither is a premise
only about a selected descent of `D`. The existential stability proof `hτ`
belongs only to the second branch. The first branch requires no cell
stability, and the proposition does not assert stability of every cell.
There is no compatible-torus hypothesis.

Under these three premises, the conclusion is exactly

```text
restrictOpen (isOpen_upperBruhatCellNeighborhood w)
  (D : Distribution G) = 0.
```

This is equality in `Distribution O`. The restriction is the published dual
of extension by zero: its value on `f : SchwartzBruhat O` is
`D (SchwartzBruhat.extendZero (isOpen_upperBruhatCellNeighborhood w) f)`.
Thus the conclusion concerns the actual neighborhood restriction.

## Intended transport and provenance

This is an internal derived interface assembled from the published Bruhat
geometry, `Whittaker.Distribution`, `Whittaker.BruhatCellDistribution`, and
`Distribution.SupportedRestriction`. It adapts Worker 634's private
`RelativeCellTransportCore.restriction_zero_of_cellwise` design in the
shared preparation for the global invariance argument. That preparation is
unreviewed proof material, not an assumption or public proof of this
proposition. No external literature proposition is transcribed here.

The intended proof uses the actual relatively closed piece
`P = (Subtype.val : O → G) ⁻¹' L`. Closedness of `L` makes `P` closed in
the open space `O`. The identity `O ∩ L = C_w` gives a concrete
homeomorphism from this nested subtype to the actual cell by forgetting the
two subtype proofs. One can therefore apply the published `descendInOpen`
to `D` and push the result along that homeomorphism. This produces a
distribution on the actual cell with its actual translations.

A separate proof must transfer positive bi-equivariance to this descent.
The first branch then makes it zero. In the second branch, the same-cell
stability proof permits transport of global anti-invariance to the
restricted transpose. The assumed cellwise invariance makes this descended
distribution equal to its negative, hence zero over `ℂ`. Injectivity of
homeomorphism pushforward and the published
`closedPushforward_descendInOpen` identity then yield the claimed zero open
restriction.

These paragraphs describe the intended proof route; this file introduces
no public relative-cell constructions or covariance theorems. The cellwise
alternative remains an explicit premise. Proving it for the relevant cells,
proving this transport proposition, assembling the finite-layer removal
argument, and proving global Shalika invariance or Whittaker multiplicity
one are separate obligations.
