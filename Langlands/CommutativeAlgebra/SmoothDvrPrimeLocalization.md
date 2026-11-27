# Localizations of smooth algebras over a DVR at generic points of the special fibre

The module `Langlands.CommutativeAlgebra.SmoothDvrPrimeLocalization` proves that the
localization of a smooth algebra over a discrete valuation ring at a prime minimal over
the maximal ideal of the base is an extension of ramification index one, in the sense
of `Langlands.AlgebraicGeometry.IsRamificationIndexOne`.

## Source

Siegfried Bosch, Werner Lütkebohmert and Michel Raynaud, *Néron Models* (Springer,
1990; literature ID `bosch-lutkebohmert-raynaud-1990-neron-models`), §3.6, remark after
Definition 1, printed p. 78 (PDF p. 85): a local ring of a smooth `R`-scheme at a generic
point of the special fibre has ramification index 1 over `R`. The module proves the
algebraic content of this remark for an affine chart; BLR give no proof, and the proof
below is internal to the Library.

## Setting

Throughout, `V` is a discrete valuation ring, `A` a `V`-algebra, `p` a prime ideal of
`A`, and `O` a local ring with compatible algebra structures `V → A → O`
(`IsScalarTower V A O`) such that `O` is the localization of `A` at `p`
(`IsLocalization.AtPrime O p`). Write `𝔪_V` for the maximal ideal of `V`. The two
hypotheses used below are

- `hp : 𝔪_V A ≤ p`: the prime lies over the closed point of `Spec V`;
- `hmin`: every prime `q` of `A` with `𝔪_V A ≤ q ≤ p` equals `p`, so `p` is minimal over
  `𝔪_V A`. Geometrically, `p` is a generic point of the special fibre of `Spec A`.

## Results

- `isLocalHom_algebraMap hp`: the structure map `V → O` is a local homomorphism.
- `maximalIdeal_map_eq hp hmin` (for `A` smooth over `V`): `𝔪_V O` is the maximal ideal
  of `O`.
- `isGeometricallyReduced_residueField hp hmin` (for `A` smooth over `V`, with the
  structure map local): the residue field of `O` is geometrically reduced over the
  residue field `k` of `V`.
- `isRamificationIndexOne hp hmin`: the conjunction of the last two, that is,
  `IsRamificationIndexOne V O`.

## Proofs as implemented

`isLocalHom_algebraMap`: a non-unit `x` of `V` lies in `𝔪_V`, so its image in `A` lies
in `p` and its image in `O` lies in the maximal ideal of `O`; hence a non-unit maps to a
non-unit.

`maximalIdeal_map_eq`: choose a uniformizer `π` of `V`, so that `𝔪_V O = (π)`. The
inclusion `𝔪_V O ≤ 𝔪_O` comes from `hp`. Conversely, every prime `P` of `O` containing
`π` has contraction `q` to `A` with `𝔪_V A ≤ q ≤ p`, so `q = p` by `hmin` and `P` is the
maximal ideal. Thus every `y ∈ 𝔪_O` lies in the radical of `(π)`: `y^n = z π` in `O`.
Writing `y = a/s` and `z = b/t` and clearing denominators gives `c t a^n = c s^n π b`
in `A` for some `c ∉ p`. The element `c t a` therefore lies in every prime of `A`
containing `π`, and the Library lemma
`Langlands.CommutativeAlgebra.SmoothDVRUniformizerDivision.dvd_of_forall_mem_prime`
(the special fibre of a smooth `V`-algebra is reduced) gives `π ∣ c t a` in `A`. Since
`c t s` is a unit in `O`, `y = a/s` is a multiple of `π` in `O`.

`isGeometricallyReduced_residueField`: let `B = k ⊗_V A` and `θ : A → B` the surjection
`a ↦ 1 ⊗ a`, whose kernel is contained in `𝔪_V A` (Mathlib's
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor`). Then `B` is smooth over `k`, hence
geometrically reduced over `k`
(`Langlands.AlgebraicGeometry.PointTopology.isGeometricallyReduced_of_smooth`) and
reduced. The image `p_B = θ(p)` is a prime of `B` whose contraction is `p`, and it is a
minimal prime of `B` by `hmin`. The localization `L = B_{p_B}` is therefore a reduced ring
of Krull dimension zero, hence a field, and it is geometrically reduced over `k`
(`Langlands.CommutativeAlgebra.SeparablyClosedRationalPointProof.isGeometricallyReduced_localization`).
The `k`-algebra map `B → κ(O)` induced by `A → O → κ(O)` sends elements outside `p_B` to
units, so it factors through a `k`-algebra map `ψ : L → κ(O)`. The map `ψ` is injective
because `L` is a field, and surjective because every element of `κ(O)` is the residue of
some `a/s` with `s ∉ p`, which is `ψ(θ(a)/θ(s))`. So `κ(O) ≅ L` over `k`, and
geometric reducedness transfers along the inverse isomorphism.
