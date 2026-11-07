# Linear extension of bounded configurations compatible modulo a large integer

Author: Worker 1421.

This module proves a uniform elementary fact about finite subsets of `ℤ^r`,
written `r → ℤ` for an arbitrary finite index type `r` (with decidable
equality), so that the lattice can live in any universe. It is used to show that tori with bounded weights are determined
by their `m`-torsion for large `m` (`Langlands.Algebra.HopfPointRigidity`), in
the chart construction of task `45ac6e52-a4d8-4414-91f1-03c3be35223e`. It is
an internal lemma with no literature counterpart.

## Definitions

- `red r m : ℤ^r →+ (ℤ/m)^r`: coordinatewise reduction (`red_apply`). It is
  surjective (`red_surjective`).
- `combination S φ : (S → ℤ) →+ ℤ^r`, for a finite set `S` and a map `φ`:
  `c ↦ ∑_{χ ∈ S} c χ • φ χ` (`combination_apply`).
- `box r n`: the finite set of vectors whose coordinates all have absolute
  value at most `n`; `mem_box`.

## Results

- `exists_hom_of_relations`: if `S` generates `ℤ^r` as a group and `φ` kills
  every relation of `S`, meaning `combination S id c = 0` implies
  `combination S φ c = 0`, then some group homomorphism `T` agrees with `φ` on
  `S`. The proof applies `AddMonoidHom.liftOfRightInverse` to the surjection
  `combination S id`.
- `eq_zero_of_red_eq_zero`: a vector that reduces to `0` modulo `m`, with
  the sum of the absolute values of its coordinates less than `m`, is zero.
- `exists_bound r n`: there is `m₀` with the following property. Let
  `m ≥ m₀`, let `S ⊆ box r n` generate `ℤ^r`, and let `φ` map `S` into
  `box r n`. Suppose `red m (φ χ) = γ (red m χ)` on `S` for some group
  endomorphism `γ` of `(ℤ/m)^r`. Then some group homomorphism of `ℤ^r` agrees
  with `φ` on `S`.

Proof of `exists_bound`. There are finitely many configurations: subsets of
the box together with self-maps of the box. For each configuration that is
"bad", i.e. some relation of `S` is not preserved by `φ`, choose a witness
relation `c`. Let `m₀` exceed the coordinate sizes of every resulting vector
`combination S φ c`. If the conclusion failed for some `m ≥ m₀`, the
configuration of `(S, φ)` would be bad. Its chosen witness `c` would satisfy
`red m (combination S φ c) = γ (red m (combination S id c)) = 0`, and this
vector is smaller than `m`, so it vanishes by `eq_zero_of_red_eq_zero`. That
contradicts the choice of the witness.

## Reduction of lattice maps

- `exists_red_comp`: every group endomorphism `T` of `ℤ^r` induces an
  endomorphism `Tb` of `(ℤ/m)^r` with `Tb ∘ red = red ∘ T`. The kernel of `red`
  consists of the vectors `m • y`, and `T` maps it into the kernel, so
  `AddMonoidHom.liftOfRightInverse` factors `red ∘ T` through `red`.
- `exists_red_equiv`: every automorphism `T` of `ℤ^r` induces an automorphism
  `Tb` of `(ℤ/m)^r` with `Tb (red x) = red (T x)`. Apply `exists_red_comp` to
  `T` and `T⁻¹`. The two induced maps are mutually inverse because `red` is
  surjective.
