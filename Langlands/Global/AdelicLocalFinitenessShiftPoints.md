# The translations of `Ξ_main` as shifts of the chamber coordinates

Module `Langlands.Global.AdelicLocalFinitenessShiftPoints`. It verifies, for the translations of
the system `Ξ_main` (module `AdelicLocalFinitenessStatement`), the two properties of the shifts used
by the strict-embedding estimate (`exists_chamberEmbedding`, `exists_residualOperators`): they move
the chamber coordinates by fixed vectors, and they commute with the Levi and normalize the unipotent
radical of the relevant standard parabolics.

## Definition

`IsCoordinateShift c b v`: the point `b` moves the coordinate map `c` by the vector `v`, i.e.
`c(b g) = c(g) + v` for all `g`.

## Results

- `AdelicSiegelFactors.isCoordinateShift_torus`: for an Iwasawa subgroup `K` of the standard minimal
  parabolic `P₀`, a real linear map `e` on the real character dual of `P₀` and a torus point `q`,
  `i(q)` moves `g ↦ e(H₀(g))` by `e(log_{P₀}(q))`, where `q` is viewed in `P₀` through
  `torusToStandardParabolic`. Proof: `i(q)` is the image of a point of `P₀(𝔸)`, so
  `H₀(i(q) g) = log_{P₀}(q) + H₀(g)` (`IsIwasawaCompact.height_map_mul`). With the coordinates of
  `adelicLocalFinitenessChamberCoordinates`, which send `log_{P₀}(t_α)` and `log_{P₀}(z_j)` to the
  unit vectors, this gives the unit shifts of the chamber coordinates by `a_α = i(t_α)` and
  `z_j = i(z_j)`.
- `StandardParabolicFamily.commute_positiveSplitComponent_standardLevi`: the image of a point of the
  positive split component of `P` commutes with every adelic point of the standard Levi `L_J` of an
  index `J ⊆ P`: `L_J ≤ L_P` (`standardParabolicOrder`), `L_P` is the image of the Levi of `P`
  (`levi_eq`), and the split component is central in that Levi
  (`commute_positiveSplitComponent_levi`).
- `StandardParabolicFamily.isLeviNormalizingPoint_torus`: the image of a torus point lies in every
  standard parabolic (the torus lies in its centralizer, hence in every standard Levi), so it and
  its inverse normalize `U_J(𝔸)` (`conj_mem_standardUnipotent`); if it commutes with `L_J(𝔸)`, it is
  a Levi-normalizing point for `J` (`IsLeviNormalizingPoint`, module
  `AdelicLocalFinitenessComponentShifts`).
- `StandardParabolicFamily.isLeviNormalizingPoint_of_groupData`: assume
  `PositiveTorusSplitComponentStatement` (as a hypothesis). For group data of `Ξ_main`
  (`IsLocalFinitenessGroupData`), `i(t_β)` is a Levi-normalizing point for every `J ⊆ Δ` with
  `β ∉ J`, and `i(z_j)` for every `J ⊆ Δ`. Proof: `t_β` is a positive torus point on which every
  simple root other than `β` is `1`, so by the hypothesis `i(t_β)` is the image of a point of the
  positive split component of the standard parabolic with index `Δ ∖ {β}`, which contains `J`;
  likewise `i(z_j)` for the index `Δ` (the split center of `G`).

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), 187–234, §7.2, pp. 211–212 (the translations `a_α ∈ A_{P_α}` and `z_j ∈ A_G` of
`Ξ_main`), §7.5, p. 219 (the transformation `σ_α`, left translation by `a_α ∈ A_P`, shifts the
coordinate `h = H₀ − T₀` by `e_α = H₀(a_α)`) and §7.7, pp. 220–221 (the shifts `z_i^{±1}`)
(literature id `bernstein-lapid-2024-meromorphic-continuation-eisenstein`). The identification of
the translations with points of split components is the statement
`PositiveTorusSplitComponentStatement`, taken as a hypothesis here.
