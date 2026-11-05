# The Lie algebra of the dynamic unipotent subgroup

Module `Langlands.GroupScheme.SplitExistence.UnipotentLie`, namespace
`Langlands.GroupScheme.SplitExistence.ChevalleyData`. Internal helper of the proof of the split
reductive Existence Theorem (task 2132924b). This is the upper bound
`Lie U_G(λ) ⊆ ⊕_{γ > 0} k e_γ` used to compute the roots. The classical argument uses that
`U⁺ = ∏_{γ>0} U_γ` is an affine space with polynomial coordinates (Steinberg, *Lectures on
Chevalley Groups*, Lemma 17). The formal route through the dynamic subgroup `U_G(λ)` and a
retraction morphism is derived content.

## Ordered products over arbitrary rings

- `opmGL l c`: the ordered product `∏_{j ∈ l} x_j(c j)` in `GL_n(R)`. `coe_opmGL` identifies
  its matrix with `opm l c` (module `Retraction`). `opmGL_map` is compatibility with ring
  homomorphisms, and `opm_congr` says `opm l c` depends only on the values of `c` on `l`.

## Recovery on geometric points

`opm_retr_of_blockUnipotent` (`P` reduced): let `K` be a field with a `k`-algebra structure,
and `g ∈ Γ(K)` an element whose entries `(c, d)` with `ℓ(wt c) ≤ ℓ(wt d)` are those of the
identity matrix. Then `opm posList (retr k g) = g`. Such a `g` is block triangular, so it
lies in `B(K) = T(K) U⁺(K)` (`chevSub_inf_btSub`). Write `g = τ v`. Comparing diagonal
entries, and using that the nonzero diagonal entries of the `ℓ`-unitriangular `v` equal `1`,
gives `τ = 1`. So `g ∈ U⁺(K)`, and the ordered product decomposition
(`exists_orderedProd_of_mem_posSub`) together with `retr_opm` finishes the proof.

## The retraction morphism

- `coordAlg k`, `univMatrix k`: the coordinate algebra of `GL_n` over `k`, and the universal
  matrix, which is the identity point in affine coordinates. `GL_n` is literally the affine
  test object of its coordinate algebra.
- `retrMor k : GL_n ⟶ GL_n`: the morphism of schemes over `k` whose universal value is
  `∏_{γ > 0} x_γ(r_γ(g_univ))`. Here `r = retr k` is the polynomial retraction of
  `Retraction`, which uses `k`-linear coefficients.
- `affinePointsEquiv_retrMor`: on points with values in any `k`-algebra `S`, `retrMor` sends
  the matrix `g` to `∏_{γ > 0} x_γ(r_γ(g))`. The proof writes the point as the spectrum of
  the classifying map `f`, then applies naturality of the Library's `affinePointsEquiv`,
  `opmGL_map` and `retr_map` (the retraction commutes with `k`-algebra maps).
- `affSecEquiv`, `pointsEquiv_eq_glMap`, `mem_chevPoints_iff_affine`,
  `pointsEquiv_apply_eq_affine`: comparisons between global-section coordinates
  (`GeneralLinear.pointsEquiv`) and affine coordinates (`GeneralLinear.affinePointsEquiv`)
  on affine test schemes. They go through the Library's
  `GeneralLinear.pointsEquiv_eq_affinePointsEquiv` and `Corepresented.affineSectionsIso`.

## Main results

- `ChevGroup.unipotent_retr` (`P` reduced, `G` affine): restricted to the closed
  representative `u` of `U_G(λ)` (Library `Dynamic.Affine.unipotentHom`), the composite with
  `retrMor` is the identity:
  `u ≫ i ≫ retrMor = u ≫ i`. The representative is smooth (`dynamicSmooth`), hence reduced,
  so by `ext_of_extPoints` (module `ExtPoints`) it suffices to compare `K`-valued points for
  an algebraic closure `K`. Such a point lies in `U_{GL_n}` of the diagonal cocharacter
  (`unipotent_eq_comap_of_isClosedSubgroup`, `cochar_comp_i`), which is the block unipotent
  subgroup (`GeneralLinear.dynamicStatement`). It also lies in `Γ(K)`, because `G` is a stage.
  Recovery on geometric points concludes.
- `ChevGroup.coefficients_mem_span_of_unipotent` (`P` reduced, `G` affine): let `x` be an
  element of the Library's Lie algebra `lieKernel G k` (a `k[ε]`-point reducing to `1`) that
  lies in `U_G(λ)`. Then the epsilon-coefficient matrix of its image in `GL_n` is a `k`-linear
  combination of the root operators `e_γ = e γ 1` for positive `γ`. `x` factors through `u`,
  so its matrix `a` satisfies `∏_{γ>0} x_γ(r_γ(a)) = a`. Reduction to `1` gives
  `a = 1 + εN`. The first-order lemma `mem_span_of_opm_retr` (module `Retraction`) concludes.
