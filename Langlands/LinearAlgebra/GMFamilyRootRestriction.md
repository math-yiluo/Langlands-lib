# Restricting a root arrangement along an isometric embedding

This module compares the Euclidean model of [GMFamilies](GMFamilies.md) for a finite set of
vectors `R₀` in a Euclidean space `E₀` with the model for its restriction to a subspace. The
subspace is given as a linear isometric embedding `φ : E →ₗᵢ[ℝ] E₀`. Restriction of vectors is
the adjoint `res φ : E₀ → E` (`inner_res : ⟪res φ γ, x⟫ = ⟪γ, φ x⟫`), and
`restrictRoots φ R₀` is the set of nonzero restrictions of the elements of `R₀`. In Arthur's
setting `E₀` is the real cocharacter space of a maximal split torus, `R₀` its roots, `E` the
space `𝔞_{M₁}` of a Levi subgroup, and `restrictRoots φ R₀` the roots of `(G, A_{M₁})`
(J. Arthur, *The invariant trace formula. I. Local theory* (1988), §7,
`arthur-1988-invariant-trace-formula-I`).

All results are transport statements: a subspace `V ⊆ E` corresponds to `mapSub V = φ(V)`.

## Contents

- **Chambers.** `posSet_restrictRoots`, `up_posSet` and `res_image_posSet`: the positive roots for
  a regular point `h ∈ E` are the restrictions of the positive roots of `R₀` for `φ h`.
  `isRegular_mapSub_iff`, `coe_restrictedRoot_mapSub` and `restrictedRoot_mapSub_eq_zero_iff`
  compare regularity and restricted roots on `V` and `φ(V)`.
- **Parabolic sets.** `up φ R₀ S` collects the elements of `R₀` restricting into `S` and
  `down S₀` is the image of `S₀` under `res φ`. `mem_parabolics_mapSub_iff`,
  `up_mem_parabolics`, `down_mem_parabolics`, `up_down` and `down_up` show that they are mutually
  inverse bijections between `parabolics (restrictRoots φ R₀) V` and `parabolics R₀ (φ V)`.
  `parabolics_subset_restrictRoots` and `sum_parabolics_mapSub` reindex sums.
- **Simple roots and `θ`.** `mapEquiv`, `mapIsometry` identify `V` with `φ(V)`;
  `restrictedRoots_up`, `simpleRoots_up`, `simpleEquiv` and `mem_simpleRoots_up_iff` compare the
  restricted simple roots; `gramVolume_map` and `theta_up` show that the `θ`-functions agree
  after transporting parameters with `pullParam`, `pushParam` and the continuous linear
  equivalence `pullEquiv`.
- **Families.** `pushFam V c` transports a family on `V` to `φ(V)`. `cM_pushFam` compares the
  functions `cM`, and `isAdjacentAlong_up_iff`, `isFamily_pushFam_iff` show that `pushFam`
  preserves and reflects the `(G, M)`-family property.
- **Faces and Levi flats.** For root sets closed under negation, `mem_faces_mapSub_iff`,
  `up_mem_faces`, `down_mem_faces`, `up_down_of_faces`, `down_up_of_faces` and `faces_mapSub`
  compare faces; `restrictRoots_leviRoots`, `faceSpace_up`, `leviSpaces_mapSub` and
  `sum_leviSpaces_mapSub` compare Levi roots, face spaces and Levi flats (using
  `mem_iInf_orthogonal_iff`, `map_mem_iInf_orthogonal_iff`, `mapSub_inf_iInf`); `cQM_pushFam`
  compares the functions `cQM`.
- **Descent data.** `mem_orthogonal_mapSub_iff` and `mapSub_inf_orthogonal` compute orthogonal
  complements inside `φ(E)`. `gramVolume_sum_swap`, `gramVolume_join_indep`,
  `measureFactor_mapSub` and `dDescent_mapSub` show that the descent coefficients are unchanged,
  and `extendParam_pushParam` and `descentSection_mapSub` transport the extension of parameters
  and the descent sections.

The proofs are direct: each object of [GMFamilies](GMFamilies.md) is defined through inner
products with roots, which `φ` preserves.
