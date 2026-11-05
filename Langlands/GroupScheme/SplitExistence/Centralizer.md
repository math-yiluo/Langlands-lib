# The centralizer of the regular cocharacter is the torus

Module `Langlands.GroupScheme.SplitExistence.Centralizer`, namespace
`Langlands.GroupScheme.SplitExistence.ChevalleyData`. Internal helper of the proof of the split
reductive Existence Theorem (task 2132924b). This is the step "`Z_G(λ) = T`" of the classical
argument, with the identity `Z_G(λ)(K) = T(K)` coming from the Tits system (Steinberg,
*Lectures on Chevalley Groups*, §3). The scheme-theoretic deduction is derived content. It
uses the Library's dynamic subgroup theory (Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
§2.1).

## Declarations

- `mem_torusSub_of_blockLevi` (field `K`, `J` finite, `P` reduced): an element `g` of `Γ(K)`
  whose entries `(c, d)` vanish whenever `ℓ(wt c) ≠ ℓ(wt d)` lies in `T(K)`. Such a `g` is
  block triangular, so `g ∈ Γ ∩ P_ℓ = B` (`chevSub_inf_btSub`), and `g = τ v` with
  `τ ∈ T(K)` and `v ∈ U⁺(K)`. The matrix `v = τ⁻¹ g` is still block diagonal and is
  `ℓ`-unitriangular (`posSub_le_utSub`). Hence every nonzero entry of `v` is a diagonal entry
  equal to `1`. Every column of the invertible `v` has a nonzero entry, so `v = 1`.
- `ChevGroup k`: a `Stage` (module `Generation`) together with homomorphisms
  `t : D(X) ⟶ G` and `u j : 𝔾ₐ ⟶ G` whose composites with the inclusion `i : G ⟶ GL_n` are
  `torusToGL` and `rootToGL j`.
- `nonempty_chevGroup k` (`J` finite, `X` finitely generated): such a group exists. Take the
  stage of `exists_chevalley_stage` and factor the torus and root homomorphisms through it
  (`exists_hom_factor`).
- `ChevGroup.mono_i`, `ChevGroup.t_closed`: the inclusion into `GL_n` is a monomorphism, and
  `t` is a closed subgroup (`IsClosedSubgroup.of_comp`, `isClosedSubgroup_torusToGL`).
- `ChevGroup.cochar`: the regular cocharacter `λ = cochar k ≫ t` of `G`.
  `ChevGroup.cochar_comp_i`: its image in `GL_n` is the diagonal cocharacter of `ellWeights`.
- `ChevGroup.glExt_apply`: entries of `glExt` are the images of the entries of
  `GeneralLinear.pointsEquiv` under `specRingEquiv`.
- `ChevGroup.centralizer_le` (`J` finite, `P` reduced, `X` finitely generated): the dynamic
  centralizer `Z_G(λ)` lies in the range of `t`, as subgroup functors on every test scheme.

## Proof of `centralizer_le`

Take the Library's closed representative `z` of `Z_G(λ)` (`Dynamic.Affine.centralizerHom`).
It is smooth (`dynamicSmooth`), hence reduced and locally of finite type. By
`range_le_of_extPoints` (module `ExtPoints`) it suffices to treat a `K`-valued point `x` of the
representative, for `K` an algebraic closure of `k`. Its image `y` lies in `Z_G(λ)`. By
`Dynamic.centralizer_eq_comap_of_isClosedSubgroup`, `y` composed with `i` lies in `Z_{GL_n}` of
the diagonal cocharacter. The Library's `GeneralLinear.dynamicStatement` identifies that
centralizer with the block Levi subgroup `blockLevi` for the weights `ℓ(wt c)`. The matrix of
`y` also lies in `Γ(K)`, because `G` is a stage. So `mem_torusSub_of_blockLevi` gives
`y = diag(χ(wt c))` for a character `χ` with values in `Kˣ`. The `K`-valued point of `D(X)`
with character `χ`, mapped by `t`, has the same image in `GL_n`, by `pointsEquiv_torusToGL` and
`torusHom_map`. Cancelling the monomorphism `i` finishes the proof.
