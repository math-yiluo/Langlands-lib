# Wall contraction from a lattice model of the Cartan elements

Module `Langlands.Representation.Aubert.General.CartanLatticeContraction`.

This module proves the wall contraction dichotomy
`Langlands.Aubert.General.HasWallContraction` (module
`Langlands.Representation.Aubert.General.JacquetCartanAssembly`) from an abstract
description of the Cartan elements of the standard Levi subgroups. It contains
no facts about actual reductive groups. The model is the dominant Cartan
representatives `C̃⁺ = C₀ F₀ ∩ Z_dom` of D. Renard, *Représentations des groupes
réductifs p-adiques* (French version dated 9 July 2026, source id
`renard-2026-representations-groupes-reductifs-padiques`), V.5.1 and notation
V.3.23, written as `ϖ^x f` with `x` in the cocharacter lattice of a maximal split
torus. The argument replaces the proof step of Renard VI.2.1 `a) ⇒ b)` (printed
pp. 138–139) that leads to (VI.2.1.1). It is derived here, not taken from the
literature; the contraction input is Renard V.5.2 (iii) (printed p. 123).

## `Langlands.Aubert.General.IsCartanLatticeModel`

The parameters are a group `G` with a topology, subgroup families
`levi unipotent : Finset Δ → Subgroup G` (`M_I` and `N_I`), sets
`cartanSet : Finset Δ → Set G`, an additive commutative group `X`, a monoid
homomorphism `e : Multiplicative X →* G` (in the model, `x ↦ ϖ^x`), additive maps
`pair β : X →+ ℤ` for `β ∈ Δ` (in the model, `x ↦ ⟨β, x⟩`), and a set `F₀ ⊆ G`.
Write `e x` for `e (ofAdd x)`. `IsCartanLatticeModel levi unipotent cartanSet e
pair F₀` is the conjunction of the following fields.

- `finite_F₀`: `F₀` is finite.
- `exists_rep`: for every `I` there is an integer `B` such that every
  `t ∈ cartanSet I` is `e x * f` with `f ∈ F₀` and `-B ≤ ⟨β, x⟩` for all `β ∈ I`.
  In the model this is the dominance of `t` for `M_I`.
- `e_mem_levi`: `e x ∈ M_I` for all `I` and `x`.
- `F₀_subset_levi`: `F₀ ⊆ M_I` for all `I`.
- `levi_le_normalizer`: `M_I` normalizes `N_I`.
- `commute_of_pair_eq_zero`: if `⟨β, x⟩ = 0` for all `β ∈ I`, then `e x`
  commutes with every element of `M_I`.
- `exists_standard`: every `I` has some `ζ ∈ X` with `⟨β, ζ⟩ = 0` for `β ∈ I` and
  `⟨β, ζ⟩ > 0` for `β ∉ I` (a standard cocharacter of `I`).
- `contracts`: for every `J`, `u ∈ N_J` and neighbourhood `O` of `1`, there is an
  integer `L` such that `e y * u * (e y)⁻¹ ∈ O` for every `y` with `⟨β, y⟩ = 0`
  for `β ∈ J` and `⟨β, y⟩ ≥ L` for `β ∉ J`. This is the form of Renard V.5.2
  (iii) for the strictly `J`-positive part of the lattice.

## Declarations

- `exists_finite_pairing_reps pair J lo hi`: there is a finite set `R ⊆ X` such
  that every `x` with `lo ≤ ⟨β, x⟩ ≤ hi` for all `β ∈ J` has some `r ∈ R` with
  `⟨β, x - r⟩ = 0` for all `β ∈ J`.
- `IsCartanLatticeModel.conj_add_of_pair_eq_zero`: if `z` is orthogonal to `I`
  and `u ∈ M_I`, then `e (y + z) * u * (e (y + z))⁻¹ = e y * u * (e y)⁻¹`.
- `IsCartanLatticeModel.eventually_wall_contraction` (the step lemma, for a
  topological group `G` and a finite type `Δ`): fix `I`, a neighbourhood `O`
  of `1`, finite sets `S J ⊆ N_J ∩ M_I` for `J ⊊ I`, and integers `B` and `T`.
  Then for all sufficiently large `T'` the following holds. Let `J ⊊ I`, let
  `x ∈ X` with `-B ≤ ⟨β, x⟩ ≤ T` for `β ∈ J` and `⟨β, x⟩ ≥ T'` for
  `β ∈ I \ J`, let `f ∈ F₀`, and let `u ∈ S J`. Then
  `(e x * f) * u * (e x * f)⁻¹ ∈ O`.
- `IsCartanLatticeModel.hasWallContraction` (for a topological group `G` and a
  finite type `Δ`): a lattice model satisfies `HasWallContraction levi unipotent
  cartanSet I` for every `I`.

## Proofs

`exists_finite_pairing_reps`: the map `x ↦ (⟨β, x⟩)_{β ∈ J}` sends the given set
of lattice elements into the finite box `[lo, hi]^J` (`Set.Finite.pi`). Choosing
one preimage of each point of the image (`Function.invFunOn`) gives the finite
set `R`; `x` and the chosen preimage of its image have the same pairings with
`J`.

`conj_add_of_pair_eq_zero`: `e (y + z) = e y * e z`, and `e z` commutes with `u`
by `commute_of_pair_eq_zero`.

`eventually_wall_contraction`: the finitely many walls `J` are treated
separately (`Filter.eventually_all`). For a wall `J`:

1. Take the finite set `R` of `exists_finite_pairing_reps` for `J` and the box
   `[-B, T]`.
2. `O' = ⋂_{r ∈ R} {g | e r * g * (e r)⁻¹ ∈ O}` is a neighbourhood of `1`, a
   finite intersection of preimages of `O` under continuous maps fixing `1`.
3. The set `U` of the elements `f * u * f⁻¹` with `f ∈ F₀`, `u ∈ S J` is finite and
   lies in `N_J ∩ M_I`, since `f ∈ M_J` normalizes `N_J` and `f ∈ M_I`.
4. `contracts` for each element of `U` and `O'` gives one integer `L` that works
   for all of `U`.
5. Every `T'` with `T' ≥ L + ⟨β, r⟩` for all `r ∈ R` and `β ∈ Δ` works. Given `x`,
   `f`, `u` as in the statement, pick `r ∈ R` with `y = x - r` orthogonal to `J`.
   Let `ζ` be a standard cocharacter of `I` and
   `m = Σ_{β ∈ Δ} max(L - ⟨β, y⟩, 0)`. Then `y + m ζ` is orthogonal to `J` and has
   pairing at least `L` with every `β ∉ J`. For `β ∈ I \ J` this pairing is
   `⟨β, x⟩ - ⟨β, r⟩ ≥ T' - ⟨β, r⟩ ≥ L`. For `β ∉ I` it is
   `⟨β, y⟩ + m ⟨β, ζ⟩ ≥ ⟨β, y⟩ + m ≥ L`. So `e (y + m ζ)` conjugates `f * u * f⁻¹`
   into `O'`. Since `m ζ` is orthogonal to `I` and `f * u * f⁻¹ ∈ M_I`,
   `e y` also does (`conj_add_of_pair_eq_zero`). Finally `e x = e r * e y` and the
   definition of `O'` give
   `(e x * f) * u * (e x * f)⁻¹ = e r * (e y * (f * u * f⁻¹) * (e y)⁻¹) * (e r)⁻¹ ∈ O`.

`hasWallContraction`: let `O` and `S` be given, and let `B` be the bound of
`exists_rep` for `I`. The step lemma gives a function `next` with `T < next T`
such that `T' = next T` satisfies the conclusion of the step lemma for `T`.
Put `T k = next^[k] (-B)`; this sequence is monotone. Let `R` be the finite set
of `exists_finite_pairing_reps` for `I` and the box `[-B, T |I|]`. The compact set
is the finite set `D = {e r * f | r ∈ R, f ∈ F₀}`.

Let `t = e x * f ∈ cartanSet I` as in `exists_rep`, and put
`J k = {β ∈ I | ⟨β, x⟩ < T k}`. These sets increase with `k` and have at most
`|I|` elements. Hence `J (k + 1) ⊆ J k` for some `k ≤ |I|`: otherwise the
cardinalities would increase strictly, and `J (|I| + 1)` would have more than
`|I|` elements. Fix such a `k`.

- If `J k = I`, every `β ∈ I` has `-B ≤ ⟨β, x⟩ < T k ≤ T |I|`. Pick `r ∈ R` with
  `x - r` orthogonal to `I`. Then `t = (e r * f) * e (x - r)` with `e r * f ∈ D`,
  because `e (x - r)` commutes with `f ∈ M_I`. Also `e (x - r) ∈ M_I` and it
  commutes with every element of `M_I`.
- Otherwise `J k ⊊ I` is the wall. For `β ∈ J k`, `-B ≤ ⟨β, x⟩ < T k`. For
  `β ∈ I \ J k`, `β ∉ J (k + 1)`, so `⟨β, x⟩ ≥ T (k + 1) = next (T k)`. The step
  lemma for `T k` then gives `t * u * t⁻¹ ∈ O` for every `u ∈ S (J k)`.

## Use

For the rational points of a connected reductive group, the intended model takes
`Δ` the simple relative roots, `X` the cocharacter lattice of a maximal split
torus `S`, `e` the uniformizer section `x ↦ ϖ^x`, `pair` the lattice pairing, and
`cartanSet I` the dominant Cartan representatives of `M_I`. Verifying the fields
there is not part of this module.
