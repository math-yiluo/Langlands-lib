# Roots with equal finite orbit sums lie in one orbit

This file proves a purely combinatorial fact about finite root data. It is the
root-theoretic input for the statement that, in a quasi-split group, every
relative-root restriction fiber is a single Galois orbit.

Let `P : RootDatum J M N` be a root datum (a Mathlib root pairing over `ℤ`).
Let `Γ` be a finite group and `ρ : Γ →* P.Aut` an action by root-datum
automorphisms. The definition `rootOrbitSum P ρ i` is the sum
`∑ g : Γ, P.root (ρ g • i)` of the roots along the orbit of the index `i`,
counted with multiplicity along `Γ`. The lemma `rootOrbitSum_eq_sum_smul`
rewrites it as the sum `∑ g, ρ g • P.root i` of transported weights.

Supporting lemmas:

- `rootOrbitSum_smul`: the orbit sum is constant along orbits, by
  reindexing with right multiplication.
- `rootOrbitSum_eq_sub_of_root_eq_sub`: if `root m = root a - root b`,
  then the orbit sum of `m` is the orbit sum of `a` minus that of `b`.
- `pairing_smul_smul`: automorphisms preserve the pairing. This is Mathlib's
  `RootPairing.Hom.pairing`.
- `sum_pairing_smul_right`: the sum of `pairing i (ρ g • j)` over `g` equals
  the evaluation of the orbit sum of `i` on the coroot of `j`. The proof uses
  invariance under `ρ g⁻¹` and reindexing by inversion.
- `toLinearMap_rootOrbitSum_coroot_smul`: the orbit sum of `j` takes the same
  value on every coroot in the orbit of `j`.

## Main theorem

`exists_smul_eq_of_rootOrbitSum_eq` assumes that `J` is finite and that no
root has orbit sum zero. Under these hypotheses, `rootOrbitSum P ρ i = rootOrbitSum P ρ j`
implies `∃ g, ρ g • j = i`.

The proof does not use the classification of root systems. Suppose, for a
contradiction, that `i` is not in the orbit of `j`.

1. For every `g`, `pairing i (ρ g • j) ≤ 0`. Suppose instead that it is
   positive. Since `i ≠ ρ g • j`, Mathlib's
   `RootPairing.root_sub_root_mem_of_pairingIn_pos` gives a root `m` with
   `root m = root i - root (ρ g • j)`. Then the orbit sum of `m` is
   `N(i) - N(j) = 0`, where `N` denotes the orbit sum. This contradicts the
   hypothesis.
2. Summing over `g`, the value `c` of `N(j) = N(i)` on the coroot of `j` is
   at most `0`.
3. Let `B` be the canonical form `P.RootForm`. Mathlib's
   `rootForm_self_smul_coroot` and `toLinearMap_apply_apply_Polarization` give
   `2 B(α, x) = B(α, α) ⟨x, α^∨⟩` for each root `α` and weight `x`. Apply this
   with `x = N(j)` and `α` running over the orbit of `j`. Each such coroot
   value equals `c`, so `2 B(x, x) = c · ∑ B(α, α)`. The orbit sum `x` is a
   nonzero element of the root span, so `B(x, x) > 0` by
   `rootForm_pos_of_ne_zero`. Every `B(α, α)` is nonnegative by
   `zero_le_rootForm`. Therefore `c > 0`, which contradicts step 2.

The provenance is internal. Kaletha–Prasad, *Bruhat–Tits theory: a new
approach* (2023), §2.6(b) (printed page 96), state without proof that the
fibers of absolute-to-relative root restriction are Galois orbits in the
quasi-split case. The argument here proves the combinatorial core of that
statement for an arbitrary finite group of automorphisms. It assumes nothing
about reducedness, irreducibility or the Dynkin type. The geometric hypotheses
(equality of orbit sums from equal restrictions to the maximal split torus, and
nonvanishing of orbit sums) are not established in this file.
