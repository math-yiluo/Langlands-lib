# Mackey's formula on continuous exact virtual groups

Worker 1828 derives this auxiliary unit for proof task
`cfea3159-7908-43b1-a677-75834c3859bd` (the local restriction formula
`Langlands.ClassField.Global.RelativeWeilGroup.LocalInducedRestrictionStatement`).
It is general group theory and does not mention Weil groups.

## Source

Mackey's formula: Jean-Pierre Serre, *Linear Representations of Finite Groups*,
GTM 42 (1977), §7.3, Proposition 22, p.58 (registered
`serre-1977-linear-representations`). Serre states it for finite groups,
characteristic zero and one subgroup in a double-coset system. The version here
is derived from it. It holds over any field for the algebraic equivalence, for
arbitrary groups `G` and `L`, for a finite-index subgroup `H ≤ G` and a
homomorphism `ι : L → G` in place of a second subgroup, and in the exact
Grothendieck group of continuous complex representations for the class identity.
Representations need not be semisimple: the class identity uses an explicit
filtration, not a decomposition into irreducibles.

## Setting

- `G` and `L` are groups in the same universe, `H ≤ G` has finite index, and
  `ι : L →* G` is a homomorphism.
- `U` is a finite index type with elements `x u : G`.
- `S u ≤ L` are finite-index subgroups and `κ u : S u →* H` satisfy
  `κ u s = x u * ι s * (x u)⁻¹` (`hκ`).
- `hS`: if `x u * ι ℓ * (x u)⁻¹ ∈ H`, then `ℓ ∈ S u`. With `hκ` this says that
  `S u` is exactly `ι⁻¹((x u)⁻¹ H x u)`.
- `hcover`: every `g : G` is `h * (x u * ι ℓ)` with `h ∈ H`.
- `hdisj`: if `h * (x u * ι ℓ) = h' * (x u' * ι ℓ')` with `h, h' ∈ H`, then `u = u'`.

So the double cosets `H x u ι(L)` are pairwise distinct and cover `G`. Induction
is the Library's `FiniteRepresentation.induce`, Mathlib's coinduction
`Representation.coind` on `H`-equivariant functions `f : G → A` with
`f (h * g) = ρ h (f g)`, where `G` acts by right translation.

## Declarations and proofs

`ofRepresentation_eq_sum_of_equiv_pi` (namespace
`Langlands.VirtualRepresentation.ExactGrothendieckGroup`). Let `V` and `W u`
(`u` in a finite type) be continuous complex representations of a topological
group `L` with carriers in one universe. Let `e : V ≃ₗ[ℂ] ((u : U) → W u)` be a
linear equivalence with `e (ℓ • v) u = ℓ • e v u`. Then in the exact Grothendieck
group of continuous representations the class of `V` is `∑ u, [W u]`.
Proof: for a finite set `s ⊆ U`, the vectors whose coordinates outside `s`
vanish form an invariant subspace `V_s`, continuous by
`isContinuous_subrepresentation`. `V_∅` is zero, so its class is zero; this uses
the short exact sequence `0 → 0 → 0 → 0` as in the Library's filtration lemmas.
For `a ∉ s`, the inclusion `V_s → V_{insert a s}` followed by the coordinate
`v ↦ e v a` onto `W a` is an actual short exact sequence. Surjectivity uses
`e.symm (Pi.single a w)`. Induction on `s` gives `[V_s] = ∑_{u ∈ s} [W u]`, and
`V_univ` is `V` itself.

`FiniteRepresentation.mackeyMap` sends an `H`-equivariant function `f` on `G` to
the family `u ↦ (ℓ ↦ f (x u * ι ℓ))`. Each component is `S u`-equivariant for
the restriction of `A` along `κ u`, because
`x u * ι (s * ℓ) = κ u s * (x u * ι ℓ)`.
`mackeyMap_intertwines` shows that it intertwines the action of `L` on the
restriction along `ι` of the induced representation with the product of the
induced actions: both are right translation.

`mackeyMap_bijective` proves bijectivity from `hS`, `hcover` and `hdisj`.
- Injective: `f (h * (x u * ι ℓ)) = ρ h (f (x u * ι ℓ))`, and these elements
  exhaust `G`.
- Surjective: given a family `F`, choose for each `g` a decomposition
  `g = h * (x u * ι ℓ)` and put `f g = ρ h (F u ℓ)`. Any two decompositions of
  `g` have the same `u` by `hdisj`. Their `L`-parts differ by
  `s = ℓ * ℓ'⁻¹ ∈ S u` (by `hS`), with `κ u s = h⁻¹ * h'` (by `hκ`). The
  `S u`-equivariance of `F u` then shows that the value does not depend on the
  decomposition. This makes `f` `H`-equivariant and sends it to `F`.

`mackeyEquiv` is the resulting linear equivalence (`LinearEquiv.ofBijective`),
and `mackeyEquiv_apply` unfolds it.

`continuousRestrict_continuousInduce`: for topological groups, open `H` and open
`S u`, continuous `ι` and continuous `κ u`, and every continuous exact virtual
representation `y` of `H`,

`continuousRestrict ι (continuousInduce H hH y) = ∑ u, continuousInduce (S u) (hSo u) (continuousRestrict (κ u) y)`.

Both sides are integer-linear in `y`, so by `hom_ext` it suffices to compare them
on actual representation classes. There `restrict_ofRepresentation` and
`induce_ofRepresentation` reduce the identity to
`ofRepresentation_eq_sum_of_equiv_pi`, applied to `mackeyEquiv` and
`mackeyMap_intertwines`. Carriers on both sides lie in universe `max uG uV`.

## Public theorems used

`ExactGrothendieckGroup.hom_ext`, `ofRepresentation_shortExact`,
`ofRepresentation_eq_of_equiv`, `restrict_ofRepresentation`,
`induce_ofRepresentation`, `continuousInduce`, `continuousRestrict`,
`FiniteRepresentation.continuousSubrepresentation` and
`isContinuous_subrepresentation`, and Mathlib's `Representation.coindV`,
`Subrepresentation` and `LinearEquiv.ofBijective`.
