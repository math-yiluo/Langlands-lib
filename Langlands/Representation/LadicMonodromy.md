# Finite image of inertia from a tame Frobenius structure

The module `Langlands.Representation.LadicMonodromy` proves
`Langlands.LadicMonodromy.finite_image_of_tameFrobenius`. This is an abstract form of
Grothendieck's ℓ-adic monodromy argument, applied to an irreducible representation, with no
reference to local fields. The arithmetic input for the Galois group of a local field is
`Langlands.LocalGalois.SepClosed.exists_tameFrobenius` in
`Langlands.Galois.Local.TameFrobenius`. The application to ℓ-adic Galois representations is
`Langlands.Henniart.ladicFiniteInertia` in
`Langlands.Correspondence.HenniartLadicFiniteInertiaProof`.

## The main theorem

`finite_image_of_tameFrobenius` assumes the following data and hypotheses:

- a group `G` with a topology, a normal subgroup `I` and an element `φ : G`;
- `hN`: every neighbourhood of `1` contains a normal subgroup of finite index;
- `hTame`: for every neighbourhood `U` of `1` there is a set `P ⊆ G` such that every
  `x ∈ P` has some power `x ^ p ^ a` in `U`, `P` contains every commutator
  `x * y * x⁻¹ * y⁻¹` with `x, y ∈ I`, and `P` contains every `φ * x * φ⁻¹ * (x ^ q)⁻¹`
  with `x ∈ I`;
- `E` is an algebraically closed nontrivially normed field with an ultrametric norm, `V` is a
  finite-dimensional `E`-vector space, `ℓ` is a prime with `(ℓ : E) ≠ 0` and `‖(ℓ : E)‖ < 1`,
  `ℓ` is coprime to `p`, and `q ≥ 2`;
- `ρ : G →* Module.End E V` is continuous for the module topology on `Module.End E V`;
- irreducibility, written as: every `ρ(G)`-stable submodule of `V` is `⊥` or `⊤`.

The conclusion is that `ρ '' I` is finite.

For the Galois group of a local field, `P` is the set of elements of inertia that lie in the
kernel of the tame character at one finite Galois level. The first condition says that
wild inertia is pro-`p`. The second and third conditions say that the tame quotient is
abelian and that Frobenius acts on it by the `q`-th power (Tate 1979, (4.2), p. 21).

## Entrywise congruences

Fix a basis `b` of `V`. `EntriesLE b r f` says that every entry of the matrix
`LinearMap.toMatrixAlgEquiv b f` has norm at most `r`. Because the norm is ultrametric, this
condition is preserved by sums (`EntriesLE.add`, `EntriesLE.sub`, `EntriesLE.neg`). It
multiplies under products (`EntriesLE.mul`, with bound `r * s`) and under scalars
(`EntriesLE.smul`, `EntriesLE.of_smul`, `EntriesLE.nsmul`). Further facts:

- `entriesLE_one_add_pow_sub`: if `X` has entries of norm at most `r ≤ 1`, then
  `(1 + X) ^ n - 1 - n • X` has entries of norm at most `r * r`. The proof is by induction
  on `n` from the identity
  `(1 + X) ^ (n + 1) - 1 - (n + 1) • X = ((1 + X) ^ n - 1 - n • X) * (1 + X) + n • (X * X)`.
- `eq_zero_of_forall_entriesLE`: an endomorphism whose entries have norm at most `lam ^ j`
  for all `j`, with `0 ≤ lam < 1`, is zero.
- `entriesLE_sub_one_mem_nhds`: for `r > 0`, the set of `f` with `EntriesLE b r (f - 1)` is a
  neighbourhood of `1` in the module topology. Each matrix entry is a linear functional,
  hence continuous for the module topology (`IsModuleTopology.continuous_of_linearMap`).

`congruenceSet b ρ lam j` is the set of `g` with `EntriesLE b (lam ^ j) (ρ g - 1)`. It
contains `1` and is closed under multiplication when `0 ≤ lam ≤ 1`, because
`ρ (g * h) - 1 = (ρ g - 1) * (ρ h - 1) + (ρ g - 1) + (ρ h - 1)`. It is a neighbourhood of
`1` when `ρ` is continuous and `lam > 0` (`congruenceSet_mem_nhds`).
`inv_mem_of_normal_finiteIndex_subset` handles inverses. A set that contains `1`, is closed
under multiplication and contains a normal subgroup `N` of finite index is closed under
inverses, because `g⁻¹ = g ^ m * (g ^ (m + 1))⁻¹` with `m + 1` the index of `N` and
`g ^ (m + 1) ∈ N` (`Subgroup.pow_index_mem`). Under `hN` this gives the subgroups
`congruenceSubgroup b ρ hlam0 hlam1 hρ hN j`.

With `lam = ‖(ℓ : E)‖`, write `H j` for the level-`j` congruence subgroup.

- `pow_mem_congruenceSet_succ`: if `g ∈ H j` with `j ≥ 1`, then `g ^ ℓ ∈ H (j + 1)`. Write
  `ρ g = 1 + X`. Then `ρ (g ^ ℓ) - 1 = ((1 + X) ^ ℓ - 1 - ℓ • X) + (ℓ : E) • X`. The first
  term has entries of norm at most `lam ^ (2 j) ≤ lam ^ (j + 1)`, and the second at most
  `lam ^ (j + 1)`.
- `mem_congruenceSet_succ_of_pow_eq_one`: if `g ∈ H j` with `j ≥ 2` and `ρ g ^ ℓ = 1`, then
  `g ∈ H (j + 1)`. Here `(ℓ : E) • X = -((1 + X) ^ ℓ - 1 - ℓ • X)` has entries of norm at
  most `lam ^ (2 j) = ‖ℓ‖ * lam ^ (2 j - 1)`. Dividing by `ℓ` gives the bound
  `lam ^ (2 j - 1) ≤ lam ^ (j + 1)` for `X`.
- `eq_one_of_pow_eq_one`: if `g ∈ H 2` and `ρ g ^ ℓ = 1`, then `ρ g = 1`. Iterating the
  previous lemma puts `g` in every `H j`. So the congruence subgroup of level `2` has no
  `ℓ`-torsion in its image; the level `2` also covers `ℓ = 2`.
- `mem_of_coprime_pow_mem`: this is stated for any decreasing sequence of subgroups `H j` in
  which `ℓ`-th powers raise the level from `j ≥ 1` to `j + 1`. If `g ∈ H 2`, `ℓ` is coprime
  to `m`, and `g ^ m ∈ H j`, then `g ∈ H j`. Indeed `g ^ ℓ ^ j ∈ H (2 + j) ≤ H j`, and a
  Bézout relation `1 = ℓ ^ j * A + m * B` (`Nat.gcd_eq_gcd_ab`) writes `g` as
  `(g ^ ℓ ^ j) ^ A * (g ^ m) ^ B`. So whether an element of `H 2` lies in `H j` can be
  tested on any of its powers with exponent prime to `ℓ`. The proof of the main theorem
  uses exactly this membership property, for every level `j`; no quotient group `H 2 / H j`
  is formed.

## Spectral lemmas

- `hasEigenvalue_of_conj`: if `P * Q = Q * P = 1`, every eigenvalue of `P * f * Q` is an
  eigenvalue of `f`.
- `exists_pow_eigenvalue_eq_one`: let `T` be invertible, `q ≥ 2`, and `P * T * Q = T ^ q`
  with `P` and `Q` mutually inverse. Then for some `m > 0` every eigenvalue of `T ^ m` equals
  `1`. Let `S` be the finite spectrum of `T` (`Module.End.finite_spectrum`). It does
  not contain `0`, and `s ↦ s ^ q` maps `S` into itself: `s ^ q` lies in the spectrum of
  `T ^ q` (`spectrum.pow_mem_pow`), which consists of eigenvalues of the conjugate of `T`.
  The maps `s ↦ s ^ (q ^ k)` of the finite set `S` into itself cannot all be distinct. Hence
  `s ^ (q ^ i) = s ^ (q ^ j)` on `S` for some `i < j`, so every `s ∈ S` satisfies
  `s ^ m = 1` with `m = q ^ j - q ^ i > 0`. Over an algebraically closed field the spectrum
  of `T ^ m` is the image of `S` under `s ↦ s ^ m` (`spectrum.map_pow_of_pos`), which is
  contained in `{1}`. The conclusion is only this containment: when `V` is zero the
  spectrum of `T ^ m` is empty.
- `exists_common_fixed`: let `V` be nonzero and `S` a set of pairwise commuting
  endomorphisms all of whose eigenvalues equal `1`. Then they have a common nonzero fixed
  vector. Take a minimal element `W₀` among the nonzero submodules stable under all of `S`
  (submodules of a finite-dimensional space are well-founded). For `f ∈ S`, the restriction
  of `f` to `W₀` has an eigenvector (`Module.End.exists_eigenvalue`), whose eigenvalue is
  `1`. So `W₀ ⊓ ker (f - 1)` is nonzero. It is stable under `S` because the elements of `S`
  commute with `f`. By minimality it equals `W₀`. Hence every `f ∈ S` fixes `W₀`
  pointwise.

## Proof of the main theorem

If `V` is zero, every endomorphism is `1`, so the image is finite. Otherwise fix a basis `b`
and the subgroups `H j` above. By `hN` choose a normal subgroup `N` of finite index inside
`H 2`, and set `I' = I ⊓ N`, a normal subgroup. Apply `hTame` to each `H j`, which gives sets
`P j`.

1. *Wild part.* If `x ∈ N` lies in every `P j`, then `ρ x = 1`. For each `j`, `x ^ p ^ a`
   lies in `H j` for some `a`. Since `ℓ` is coprime to `p ^ a` and `x ∈ H 2`,
   `mem_of_coprime_pow_mem` gives `x ∈ H j`. Then `eq_one_of_forall_mem_congruenceSet`
   applies.
2. *Commutativity.* For `x, y ∈ I'` the commutator lies in `N` and in every `P j`. So
   `ρ (x * y * x⁻¹ * y⁻¹) = 1`, and `ρ x` and `ρ y` commute.
3. *Frobenius.* For `x ∈ I'` the element `φ * x * φ⁻¹ * (x ^ q)⁻¹` lies in `N` and in every
   `P j`. So `ρ φ * ρ x * ρ φ⁻¹ = ρ x ^ q`.
4. *Quasi-unipotence.* By `exists_pow_eigenvalue_eq_one`, for every `x ∈ I'` there is
   `m > 0` such that every eigenvalue of `ρ x ^ m` equals `1`.
5. *Irreducibility.* Let `S` be the set of powers `ρ x ^ m` (`x ∈ I'`, `m : ℕ`) all of whose
   eigenvalues equal `1`, and let `W` be the subspace of vectors fixed by all of `S`. The
   elements of `S` commute by step 2, so `W` is nonzero by `exists_common_fixed`. `W` is
   `ρ(G)`-stable: for `g : G`, `ρ g⁻¹ * ρ x ^ m * ρ g = ρ (g⁻¹ * x * g) ^ m`, and
   `g⁻¹ * x * g ∈ I'`. Its eigenvalues are eigenvalues of `ρ x ^ m`
   (`hasEigenvalue_of_conj`), so `S` is stable under this conjugation.
   Irreducibility gives `W = ⊤`. Hence every `x ∈ I'` has `ρ x ^ m = 1` for some `m > 0`.
   In Tate's account the kernel of the monodromy operator is stable under the Weil group,
   so an irreducible representation has zero monodromy (Tate 1979, (4.1.5), p. 20). Step 5
   is this argument, with the unipotent elements `ρ x ^ m` in place of the logarithm `N`.
6. *Torsion-freeness.* Let `x ∈ I'` with `ρ x ^ m = 1`, and write `m = ℓ ^ a * m'` with `ℓ`
   not dividing `m'` (`Nat.exists_eq_pow_mul_and_not_dvd`). The element `y = x ^ ℓ ^ a` lies
   in `H 2`, and `y ^ m'` acts trivially. By `mem_of_coprime_pow_mem`, `y` lies in every
   `H j`, so `ρ x ^ ℓ ^ a = 1`. Then `ρ x = 1` by induction on `a`. Suppose `z ∈ N` and
   `ρ z ^ ℓ ^ (a + 1) = 1`. The induction hypothesis, applied to `z ^ ℓ ∈ N`, gives
   `ρ z ^ ℓ = 1`. Then `eq_one_of_pow_eq_one` gives `ρ z = 1`, since `N ≤ H 2`.
7. *Finiteness.* Elements of `I` in the same coset of `N` have the same image, since their
   quotient lies in `I'`. The map sending each element of `ρ '' I` to the coset of a chosen
   preimage is therefore an injection into the finite group `G ⧸ N`.

## Sources and provenance

This module is an internal formalization of the argument behind Tate's account of
Grothendieck's ℓ-adic monodromy theorem. Tate states that the wild inertia group is
pro-`p`, that inertia modulo wild inertia is `∏_{ℓ' ≠ p} ℤ_ℓ'`, and that conjugation by `w`
induces raising to the `‖w‖` power on it. He also states that the kernel of the monodromy
operator is stable, so that an irreducible representation has zero monodromy (Tate 1979,
(4.1.5), p. 20, and (4.2)–(4.2.1), p. 21). The implemented route differs from the source
in the following ways:

- it uses entrywise congruences in an arbitrary basis instead of a stable lattice;
- it uses the eigenvalue argument and the common fixed vector of commuting quasi-unipotent
  operators instead of the ℓ-adic logarithm `N`;
- it uses the finite-level tame character instead of the structure of the profinite tame
  quotient.

- J. Tate, *Number theoretic background* (1979), `tate-1979-number-theoretic-background`,
  (4.1.5), p. 20, and (4.2)–(4.2.1), p. 21. Retained Corvallis Part II PDF SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
