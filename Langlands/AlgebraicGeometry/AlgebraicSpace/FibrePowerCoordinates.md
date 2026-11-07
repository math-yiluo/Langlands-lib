# Coordinates of points of fibre powers

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.FibrePowerCoordinates`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`. It extends the published
`ChartFibrePower` (finite fibre powers `V ×_X ⋯ ×_X V` of a map `a : h_V ⟶ X`).

## Definitions

- `ChartFibrePower.coord P p i : Spec κ(p) ⟶ V`: the `i`-th coordinate of a point `p` of the
  fibre power. It is the canonical morphism `Spec κ(p) ⟶ P` followed by the `i`-th
  projection.
- `ChartFibrePower.IsDistinct P p`: the coordinates of `p` are pairwise different, i.e.
  `coord p` is injective.
- `ChartFibrePower.mapIndex P Q e : P.obj ⟶ Q.obj`, for `e : κ → ι`: the morphism of fibre
  powers lifting the family `k ↦ P.pr (e k)`. `mapIndex_pr` is its defining property.
- `ChartFibrePower.perm P σ`: the action of a permutation `σ` of the index type by
  `mapIndex`. `perm_pr`, `perm_one` and `perm_mul` give
  `perm σ ≫ pr i = pr (σ i)`, `perm 1 = 𝟙` and `perm σ ≫ perm τ = perm (σ * τ)`.
- `ChartFibrePower.pointTest P p` and `pointHom P p`: `Spec κ(p)` as a scheme over `S`, with
  its canonical morphism to the fibre power.

## Results

- `Spec_map_field_cancel`. For a homomorphism of fields `φ`, `Spec φ ≫ g = Spec φ ≫ h`
  implies `g = h`. Proof: Mathlib's `Scheme.SpecToEquivOfField`, together with injectivity of
  `φ` and `Spec.map`.
- `coord_mapIndex` and `coord_mapIndex_eq_iff`. The coordinates of the image of `p` under
  `mapIndex` are those of `p` composed with the residue-field map. Hence
  `coord (ρ p) k = coord (ρ p) l ↔ coord p (e k) = coord p (e l)`, using the previous lemma.
- `mem_range_mapIndex`. If the coordinates of `q` satisfy `coord q (f (e k)) = coord q k` for
  all `k`, then `q` lies in the range of `mapIndex f ≫ mapIndex e`. This is used to
  recognize points on graphs of permutations.
- `exists_perm_of_not_injective_snoc` (pigeonhole). Let `x, y : Fin n → T` be injective. If
  no extension `Fin.snoc x (y b)` is injective, then `y = x ∘ π` for some permutation `π`.

Provenance: internal helpers for the orbit construction of the Noetherian case of
`NoetherianQuasiAffineSourceAFStatement`: tuples of pairwise distinct points of a finite
cover, with symmetric groups acting. No source proof is transcribed.
