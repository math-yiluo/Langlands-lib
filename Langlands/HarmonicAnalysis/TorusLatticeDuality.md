# Annihilators of finite-index sublattices in a finite product of circles

Lean module: `Langlands.HarmonicAnalysis.TorusLatticeDuality`, namespace
`Langlands.HarmonicAnalysis.TorusFourier`. It imports the published
`Langlands.HarmonicAnalysis.TorusFourierInversion` (`torusCharacter_mul`, `torusCharacter_inv`,
`IsTrivialOn`, `hasSum_torusFourierCoeff_mul_conj_isTrivialOn`) and, through it,
`TorusFourierDecay` (`torusCharacter`, `torusFourierCoeff`). From Mathlib it uses
`AddChar.exists_apply_ne_zero` (characters of a finite abelian group separate points,
`Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality`), `AddSubgroup.nsmul_index_mem`,
`card_nsmul_eq_zero`, `Complex.norm_eq_one_of_pow_eq_one` and `Polynomial.mem_nthRoots`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082.

- Proof of Proposition VII.2.1, case `M = G`, printed pp. 317–318 (PDF pp. 83–84):
  `ϕ(g) = ∫_{A_G} χ_{ω'}(a^{-1}) ∫_𝒪 (E^G_G ψ_ω)(g) χ_ω(a) dω da`, followed by "on peut
  appliquer la formule d'inversion de Fourier. Compte tenu des définitions de nos mesures, on
  obtient `ϕ(g) = ∑_{ω ∈ 𝒪; χ_ω = χ_{ω'}} (E^G_G ψ_ω)(g)`."
- I.1, printed p. 239 (PDF p. 5): "L'application de restriction `Im X(G) → Im X(A_G)` est
  surjective de noyau fini."

The integral over `A_G` in this step is a sum over the image of `A_G` in the lattice of `G`,
a subgroup of finite index. The sum over the `ω` with `χ_ω = χ_{ω'}` is the image of a coset of
the finite kernel of the restriction under the twist map `Im X(G) → 𝒪`, `χ ↦ ω ⊗ χ`; by III.7
(printed p. 273) this map identifies `𝒪` with `Im X(G)/S` for the finite twist stabilizer `S`,
so it is `|S|`-to-one on the coset, and the factor `|S|` is compensated by the orbit measure of
VI.3 (printed p. 302); see `TorusFourierInversion.md`. Relating the two needs the duality
between a finite-index
sublattice `Λ ⊆ ℤ^J` and its annihilator `Λ^⊥` in the torus, which this module proves in
coordinates, together with the resulting partial Fourier series formula. The identification of
Waldspurger's lattice, image of `A_G` and kernel of the restriction with `ℤ^J`, `Λ` and `Λ^⊥` is
not made here. The proofs are standard and derived for this purpose.

## Scope and hypotheses

`J` is a finite type and the torus is `J → Circle`; `Λ` is an additive subgroup of `J → ℤ`.

Hypotheses of the results:

- `mem_latticeAnnihilator`, `isTrivialOn_latticeAnnihilator_of_mem`: none.
- `finite_latticeAnnihilator`, `mem_of_isTrivialOn_latticeAnnihilator`,
  `isTrivialOn_latticeAnnihilator_iff`: `Λ` has finite index (`Λ.FiniteIndex`).
- `hasSum_torusFourierCoeff_mul_conj_mem`: `μ` a finite left-invariant measure on the torus,
  `Λ.FiniteIndex`, a `Fintype` instance on `latticeAnnihilator Λ` (one exists by
  `finite_latticeAnnihilator`), decidability of membership in `Λ`, `hf : Continuous f`, and
  `hs : Summable fun n => ‖torusFourierCoeff μ f n‖`.

## Definitions

- `latticeAnnihilator Λ : Subgroup (J → Circle)`, the annihilator
  `Λ^⊥ = {z | χ_m(z) = 1 for all m ∈ Λ}`, where `χ_m = torusCharacter m`.

## Results

- `mem_latticeAnnihilator`: the membership condition.
- `finite_latticeAnnihilator`: `Λ^⊥` is finite when `Λ` has finite index.
- `isTrivialOn_latticeAnnihilator_of_mem`: `χ_m` is trivial on `Λ^⊥` for `m ∈ Λ`.
- `mem_of_isTrivialOn_latticeAnnihilator`, `isTrivialOn_latticeAnnihilator_iff`
  (**double annihilator**): for `Λ` of finite index, `χ_m` is trivial on `Λ^⊥` if and only if
  `m ∈ Λ`.
- `hasSum_torusFourierCoeff_mul_conj_mem` (**partial Fourier series over a sublattice**): the
  sum of `f̂(n) conj(χ_n(z))` over `n ∈ Λ` (the other terms are `0`) is
  `μ(T) |Λ^⊥|⁻¹ ∑_{w ∈ Λ^⊥} f(z w)`.

## Proof notes

1. `latticeAnnihilator` is a subgroup because `χ_m` is multiplicative and
   `χ_m(z⁻¹) = conj(χ_m(z))`.
2. Finiteness: with `N` the index, `N e_j ∈ Λ` (`nsmul_index_mem`), so `z_j^N = 1` for every
   coordinate of `z ∈ Λ^⊥`; the coordinates lie in the finite set of `N`-th roots of unity in `ℂ`
   (`Polynomial.nthRoots`), and a product of finite sets is finite.
3. Double annihilator: if `m ∉ Λ`, its class in the finite group `Q = ℤ^J / Λ` is nonzero, so
   some character `ψ : Q → ℂ` has `ψ(m̄) ≠ 1` (`AddChar.exists_apply_ne_zero`). Its values have
   norm `1` (they are `|Q|`-th roots of unity). Put `z_j = ψ(ē_j)`. Writing `k = ∑_j k_j e_j`
   gives `χ_k(z) = ψ(k̄)`, so `z ∈ Λ^⊥` and `χ_m(z) = ψ(m̄) ≠ 1`.
4. The partial sum is `hasSum_torusFourierCoeff_mul_conj_isTrivialOn` for the finite subgroup
   `Λ^⊥`, with the condition `IsTrivialOn Λ^⊥ n` replaced by `n ∈ Λ` (step 3).

## Relation to the Library

`TorusFourierInversion` proves inversion along any finite subgroup `K` with the condition
"`χ_n` trivial on `K`"; this module identifies that condition with membership in a finite-index
sublattice. `DiscreteFourierUniqueness` decomposes finitely generated abelian groups as
`ℤ^d × T` with `T` finite and proves uniqueness of character sums; it has no annihilators in the
torus. `RationalRestrictionKernel` (Worker 200) proves finiteness of the actual restriction
kernel `Im X(G) → Im X(A_G)` under a finite-index premise on the central valuation image; its
comparison with `latticeAnnihilator` in the circle coordinates of `Im X(G)` is not made here.

## Open obligations

For Proposition VII.2.1: identify the image of `A_G` in the valuation lattice of `G`, in the
coordinates of `RationalUnramifiedCharacterCoordinates`, with a finite-index `Λ`, and the kernel
of `Im X(G) → Im X(A_G)` with `latticeAnnihilator Λ`; write the integral over `A_G` as a sum over
`A_G / (A_G ∩ G¹)`; pass from `Im X(G)` to the orbit `𝒪 = Im X(G)/S` with the factor `|S|`;
and carry out the remaining steps of the proof.
