# Epimorphic Hopf maps into diagonal Hopf algebras are surjective

This module is a helper for the proof of
`Langlands.GroupScheme.MultiplicativeTypeMonoClosedImmersionStatement`
([`GroupScheme/Torus/MultiplicativeTypeMonoClosedImmersionProof`](../GroupScheme/Torus/MultiplicativeTypeMonoClosedImmersionProof.md)).
It proves an algebraic fact about bialgebra maps into the group algebra `R[M]` of an abelian
group `M` over a commutative ring `R`.

## Provenance

The module is internal: its definition and theorems were written for this proof and are not
translated from a source. The idea is the classical one that a closed subgroup of a
diagonalizable group is cut out by characters. Conrad's proof of Lemma B.1.3 uses this over a
field. Here it is used over an arbitrary commutative ring `R`, through coefficient ideals.

## Contents

All declarations are in the namespace `Langlands.CommutativeAlgebra.DiagonalHopfEpi`.

- `coefficientIdeal B m : Ideal R`, for a subalgebra `B` of `R[M]` and `m : M`: the ideal of
  the `r : R` for which the monomial `single m r` lies in `B`. It is the preimage of `B`
  under the linear map `r ↦ single m r`.
- `mem_coefficientIdeal`: `r ∈ coefficientIdeal B m ↔ single m r ∈ B`, by definition.
- `mem_of_coefficientIdeal_eq_top`: if every coefficient ideal of `B` is the unit ideal,
  then `B` contains every monomial, hence every element of `R[M]` (each element is the finite
  sum of its monomials).
- `surjective_of_epi φ hS hφ`: the main result, below.

## The main result

Let `B` be a commutative `R`-bialgebra and `φ : B →ₐc[R] R[M]` a bialgebra homomorphism into
the group algebra with its standard Hopf structure. Assume

- `hS`: the range of `φ` is stable under the antipode of `R[M]`;
- `hφ`: `φ` is an epimorphism of commutative rings, stated for target rings in the same
  universe: for every commutative ring `D` and ring maps `f g : R[M] →+* D`,
  `f ∘ φ = g ∘ φ` implies `f = g`.

Then `φ` is surjective.

The antipode hypothesis is needed: the inclusion `R[x] → R[x, x⁻¹]` is an epimorphic
bialgebra map that is not surjective.

## Proof

Write `Bφ` for the range of `φ`, a subalgebra of `R[M]`. Suppose `φ` is not surjective.

1. By `mem_of_coefficientIdeal_eq_top`, some coefficient ideal `J_l = coefficientIdeal Bφ l`
   is a proper ideal. Choose a maximal ideal `𝔪 ⊇ J_l` (`Ideal.exists_le_maximal`).
2. Let `N` be the set of `m : M` with `J_m ⊄ 𝔪`. It is an additive subgroup of `M`:
   - `0 ∈ N`, because `single 0 1 = 1 ∈ Bφ`, so `1 ∈ J_0`, and `1 ∉ 𝔪`;
   - if `r ∈ J_a \ 𝔪` and `s ∈ J_b \ 𝔪`, then `rs ∈ J_{a+b}` because
     `single a r * single b s = single (a + b) (r s)`, and `rs ∉ 𝔪` because `𝔪` is prime;
   - if `r ∈ J_a \ 𝔪`, then applying the antipode (`hS`) to `single a r` gives
     `single (-a) r ∈ Bφ` (Mathlib's `AddMonoidAlgebra.antipode_single`), so `r ∈ J_{-a}`.

   By the choice of `𝔪`, `l ∉ N`.
3. Let `k = R/𝔪` and `D = k[M/N]`. Define two `R`-algebra maps `R[M] → D` by their values on
   the basis: `f(single m r) = r̄ · 1` (the augmentation) and
   `g(single m r) = r̄ · [m]`, where `r̄` is the image of `r` in `k` and `[m]` is the basis
   element of the class of `m` in `M/N` (`AddMonoidAlgebra.lift` applied to the trivial
   character and to the composite character `M → M/N → D`).
4. `f ∘ φ = g ∘ φ`. Take `b : B` and expand `φ b = Σ_m single m c_m`. By the Library's
   `DiagonalCoalgebraImage.single_coefficient_mem_range`, each `single m c_m` lies in `Bφ`,
   that is `c_m ∈ J_m`. Compare the two maps term by term:
   - if `m ∈ N`, then `[m] = 0` in `M/N`, so `f` and `g` agree on `single m c_m`;
   - if `m ∉ N`, then `J_m ⊆ 𝔪`, so `c_m ∈ 𝔪`, `c̄_m = 0`, and both maps send
     `single m c_m` to `0`.
5. By `hφ`, `f = g`. Evaluating on `single l 1` gives `1 = [l]` in `k[M/N]`, that is
   `single 0 1 = single [l] 1`. Since `1 ≠ 0` in the field `k`, `[l] = 0`, so `l ∈ N`. This
   contradicts step 2.
