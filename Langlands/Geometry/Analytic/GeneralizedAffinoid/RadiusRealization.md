# Realizing finitely many positive radii in one complete extension field

Author: Worker 1010.

This helper module supplies the ground-field extension used in the
arbitrary-radius spectral power proof.

## The structure

For a normed field `K` and real numbers `t : Fin N → ℝ`,
`RadiusRealization K t` consists of the following data:

- a type `L` in the universe of `K`, with a `NormedField` structure that is
  ultrametric and complete;
- a ring map `ι : K →+* L` with `‖ι a‖ = ‖a‖` (`norm_ι`);
- elements `c i : L` with `‖c i‖ = t i` (`norm_c`);
- an additive map `π : L →+ K`;
- a positive real `bound` with `‖π x‖ ≤ bound * ‖x‖` (`norm_π_le`).

The map `π` satisfies `π (ι a * x) = a * π x` (`π_ι_mul`) and `π 1 = 1`
(`π_one`). Thus `π` is a bounded `K`-linear retraction of `ι`. The structure
is data. The theorems below only assert that it is nonempty, and nothing in
it is an assumption of the final theorem.

## Constructions

- `cons` combines a realization `R` of `t` over `K` with a realization `S` of
  the single radius `τ` over `R.L`. The result realizes `Fin.cons τ t` over
  `K` with these data:
  - the field `S.L`;
  - the embedding `S.ι ∘ R.ι`;
  - the elements `S.c 0` and `S.ι (R.c i)`;
  - the retraction `R.π ∘ S.π`, with bound `R.bound * S.bound`.

  The linearity and normalization identities follow from those of `R` and
  `S`.
- `empty` realizes the empty family by `K` itself, with identity maps.
- `one` realizes the radius one by `1 : K`.
- `laurent` realizes a radius `t` satisfying
  `H : ∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ t ^ n`. It uses the completed
  Gauss-normed Laurent field from `LaurentGaussField`: the element is the
  variable `X`, and the retraction is the constant term, with bound one.
- `nonempty_root` handles a nontrivially normed complete ultrametric `K`,
  with `a : K`, `n > 0` and `‖a‖ = t ^ n`.
  - The field `L` is Mathlib's splitting field of `X ^ n - C a`, with the
    spectral norm (`spectralNorm.normedField`). This norm extends the norm of
    `K` (`spectralNorm_extends`) and is nonarchimedean. `L` is complete
    because it is finite-dimensional over the complete field `K`.
  - The polynomial has positive degree and splits in `L`, so it has a root
    `α`. From `α ^ n = a` one gets `‖α‖ ^ n = t ^ n`, hence `‖α‖ = t`.
  - The retraction is a `K`-linear functional `f` with `f 1 = 1`, which exists
    because `L` is a vector space and `1 ≠ 0`. It is continuous because `L` is
    finite-dimensional over the complete field `K`. The bound is its operator
    norm plus one.

## Theorems

`nonempty_single` proves that every radius `t > 0` is realized over every
complete ultrametric normed field `K`. There are three cases.

1. If `t = 1`, use `one`.
2. Suppose `‖a‖ = t ^ n` for some `a : K` and nonzero integer `n`. Replace
   `a` by `a⁻¹` if `n < 0`. This gives `b` and `m > 0` with `‖b‖ = t ^ m`.
   Since `t ≠ 1`, `‖b‖ ≠ 1`, so `b` or `b⁻¹` has norm greater than one. This
   makes `K` nontrivially normed, and `nonempty_root` applies.
3. Otherwise `H` holds, and `laurent` applies.

The trivially valued case therefore needs no separate treatment. Every radius
other than one falls into the third case.

`nonempty` proves by induction on `N` that every family `t : Fin N → ℝ` of
positive reals is realized over every complete ultrametric `K`. It realizes
the tail of the family over `K`, then the first radius over the resulting
field, and combines the two with `cons`.

## Provenance

This is an internal construction. It is not a formalization of a numbered
result of the cited lecture notes. It reduces positive-polyradius affinoid
questions to radius-one (strict) ones by extending the ground field. This is
the classical role of the radius condition in Berkovich, *Non-Archimedean
analytic spaces* (Trieste lectures, 2009), Fact 2.1.3(ii) on page 7. The Lean
proofs above are the ones implemented.
