# Step 1 of Murre's induction: the descent problem in general

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseGeneral`, a supporting module of
`murreArtinianBase` (module `MurreArtinianBase`). Namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase`. Notation as in `ArtinianBaseTools`.

The main result is `descend_general`. Let `C ⊆ A` be local artinian rings, `π : C → ℓ` the
residue map, and `v ∈ F(Spec A)` over `η ∈ F(Spec ℓ)`. Then `η` lifts to `F(Spec C)`. Here `A`
need not be finite over `C`; its residue field can be transcendental over `ℓ`. This case is
needed because infinitesimal étaleness quantifies over all local artinian test rings. It is
reduced to `descend_finite` with (F2), a Krull intersection argument and the Nullstellensatz.
The module is internal to the proof.

## Lemmas

* `exists_fg`: (F2) in the form needed here. For a `C`-algebra `A`, every `v ∈ F(Spec A)` comes
  from `F(Spec C[s])` for a finitely generated `C`-subalgebra `C[s] ⊆ A`. The proof uses the
  Library's `ChartGluing.isColimitAdjoinCocone` (`A` as filtered colimit of its finitely
  generated subalgebras), `ChartGluing.exists_of_isColimit`, and `BaseChange.good_all`
  (FilteredColimits over `Spec C`, from (F1a) and (F2)).
* `exists_pow_injective`: let `C` be artinian, `A₀` a noetherian `C`-algebra, and `𝔮` an ideal
  such that for all `y ∈ 𝔮` and `c ∈ C`, `(1 - y)·c = 0` in `A₀` forces `c = 0` (hypothesis
  `hreg`; in particular `C → A₀` is injective). Then `C` injects into
  `A₀/𝔮^M` for some `M`. The kernels of `C → A₀/𝔮^M` decrease and stabilize, since `C` is
  artinian. An element in all of them lies in `⋂ 𝔮^M`, so by the Krull intersection theorem it
  is killed by some `1 - y`, `y ∈ 𝔮`.
* `isIntegral_of_residue`: a local artinian `C`-algebra with residue field integral over `C` is
  integral over `C`.
* `isIntegral_of_nil_ker`: a `C`-algebra with a nil-kernel map to an integral `C`-algebra is
  integral.
* `isField_of_injective_finite`: a domain `Q`, between a field `ℓ` and a field `κ` finite over
  `ℓ`, is a field.
* `mem_maximalIdeal_of_isNilpotent`: nilpotent elements of a local ring lie in its maximal
  ideal.
* `descend_closed_point`: the closed point step. Let `x ∈ F(Spec A₀)`, with `A₀` noetherian and
  of finite type over `C`. Suppose `x` agrees with `η` at a maximal ideal `𝔮` whose residue
  field is integral over `C`, and for `y ∈ 𝔮` and `c ∈ C`, `(1 - y)·c = 0` in `A₀` forces
  `c = 0`. Then `η` lifts to `C`.
  - With `M` from `exists_pow_injective`, `A₃ = A₀/𝔮^M` is local artinian, contains `C`, and
    is finite over `C` (integral and of finite type).
  - The restriction of `x` to `A₃` lies over `η`, and `descend_finite` applies.
* `closed_point_of_generic`: from the generic point to a closed point. Let `p` be a prime of
  `A₀` (of finite type over `C`), with `ℓ → A₀/p`, and suppose `x` agrees with `η` at the
  fraction field of `D = A₀/p`. Then there is a maximal ideal `𝔮 ⊇ p` of `A₀` such that
  `A₀/𝔮` is integral over `C` and `x` agrees with `η` at `A₀/𝔮`.
  - The Library lemma `Charts.exists_away_eq_of_eq` ((F1a) and (F2)) spreads the agreement
    to some `D[1/a]`, `a ≠ 0`.
  - `D[1/a]` is of finite type over `ℓ`. By the Nullstellensatz
    (`finite_of_finite_type_of_isJacobsonRing`), a residue field `κ` of `D[1/a]` is finite
    over `ℓ`.
  - `𝔮` is the kernel of `A₀ → κ`. `A₀/𝔮` is a field by `isField_of_injective_finite`.
  - `A₀/𝔮` embeds in `κ`. `κ` is finite over `ℓ`, and `ℓ` is finite over `C` (a quotient), so
    `κ` and hence `A₀/𝔮` are integral over `C`.
  - The spread agreement gives agreement of `x` and `η` at `κ`. Restriction along the field
    embedding `A₀/𝔮 ↪ κ` is injective by (F1b) (`fieldInj`), so `x` agrees with `η` at
    `A₀/𝔮`.

## `descend_general`

1. By `exists_fg`, `v` comes from `x ∈ F(Spec A₀)` for a finitely generated `C`-subalgebra
   `A₀ ⊆ A`.
2. `p = m_A ∩ A₀` is prime, and `D = A₀/p` embeds in the residue field of `A`. Since `v` lies
   over `η`, `x` and `η` agree at the fraction field of `D`.
3. `closed_point_of_generic` gives a maximal ideal `𝔮 ⊇ p`.
4. For `y ∈ 𝔮`, `1 - y ∉ p`, so `1 - y` is a unit of `A`. Hence `(1 - y) c = 0` forces `c = 0`
   for `c ∈ C`.
5. `descend_closed_point` concludes.
