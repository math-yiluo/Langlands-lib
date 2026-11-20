# Counting Galois conjugates of a finite place

Worker 5130 wrote this module for Task 7784. It counts how often Galois conjugates of a
finite place lie above a given place of an intermediate field. This is the multiplicity
count in the base change of an induced representation.

Let `L/K` be a Galois extension of number fields (one universe), `G = Gal(L/K)`. An element
`σ` acts on finite places of `L` through the published `finitePlaceEquiv σ`, which pulls a
prime back along `σ`.

## The action

- `finitePlaceEquiv_algEquiv_mul`, `_one`, `_inv_apply`, `_apply_inv`: action laws, with
  `finitePlaceEquiv (σ τ) w = finitePlaceEquiv τ (finitePlaceEquiv σ w)`.
- `asIdeal_finitePlaceEquiv_algEquiv`: the prime of `finitePlaceEquiv σ w` is the
  translate `σ⁻¹ • w` for Mathlib's pointwise action of `G` on ideals of `𝓞 L`.
- `smulCommClass_ringOfIntegers`: this action commutes with the `𝓞 K`-module structure.
  The instance is needed for Mathlib's invariance lemmas.
- `ramificationIdx_finitePlaceEquiv_algEquiv` and `inertiaDeg_finitePlaceEquiv_algEquiv`:
  ramification index and inertia degree over `K` are invariant (`Ideal.ramificationIdx_smul`,
  `Ideal.inertiaDeg_smul`).

## Counts

- `placesAbove L v`: the finite set of places of `L` above `v`. `card_mul_eq_finrank_of_forall`
  says that if all of them have the same `e f = c`, then their number times `c` is `[L : K]`
  (from the published `finitePlacesAbove_sum_ramification_inertia`).
  `nonempty_finitePlacesAbove`: some place lies above every place.
- `card_filter_finitePlaceEquiv_mem`: for `u` above `v` and a finite set `S` of places above
  `v`, the number of `σ` with `finitePlaceEquiv σ u ∈ S` is `|S|` times the number of `σ`
  fixing `u`. The fibre over `u' ∈ S` is the stabilizer translated by any `τ` with
  `finitePlaceEquiv τ u = u'` (the published transitivity
  `ClassField.Global.exists_finitePlaceEquiv_eq`).
- `card_stabilizer_finitePlaceEquiv`: the stabilizer of `u` has `e(u|v) f(u|v)` elements.
  Apply the previous count to all places above `v`, and compare with `[L : K] = |G|`.
- `card_filter_finitePlaceEquiv_liesOver`: for an intermediate field `M` (scalar tower
  `K → M → L`) and a place `w` of `M` above `v`, exactly `[L : M] e(w|v) f(w|v)` elements
  `σ` move `u` above `w`. This uses towers of `e` and `f` (`Ideal.ramificationIdx_tower`,
  `Ideal.inertiaDeg_tower`), and the count `|places above w| · e f = [L : M]` for the
  Galois extension `L/M`.
- `IsRightCosetFamily M ρ`: `ρ : ι → G` meets every right coset of `Gal(L/M)` (embedded by
  `AlgEquiv.restrictScalarsHom`) exactly once, that is, for every `σ` there is exactly one
  `i` with `σ (ρ i)⁻¹ ∈ Gal(L/M)`.
- `exists_isRightCosetFamily`: for every `n = [M : K]` (with `M` a number field) there is
  such a family indexed by `Fin n`. With `H` the image of `Gal(L/M)`, `[G : H] |H| = |G|`,
  `|H| = [L : M]`, `|G| = [L : K] = [M : K] [L : M]` give `|G ⧸ H| = n`. For an
  enumeration `e : Fin n ≃ G ⧸ H` of the left cosets, `ρ i` is the inverse of a
  representative of `e i`. Then `σ (ρ i)⁻¹ ∈ H` holds exactly when `σ⁻¹ H = e i`.
- `card_filter_rightCosetFamily_liesOver`: for such `ρ`, the number of `i` with
  `finitePlaceEquiv (ρ i)⁻¹ u` above `w` is `e(w|v) f(w|v)`. Whether `σ⁻¹ u` lies above
  `w` depends only on the coset `Gal(L/M) σ`. Then `G ≅ ι × Gal(L/M)` and `|Gal(L/M)| = [L : M]`
  reduce this to the previous count.

## Provenance

Hilbert's ramification theory for Galois extensions of Dedekind domains (Neukirch, Algebraic
Number Theory, I.9), stated for the Library's `finitePlaceEquiv` action. Internal to the
project.
