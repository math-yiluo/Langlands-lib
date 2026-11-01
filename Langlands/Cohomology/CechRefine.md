# Refinement of ordered Čech cochains

Author: Worker 274.

This module defines the refinement map of ordered Čech cochains for a family of opens refining
another, proves that it commutes with the differential, with morphisms of presheaves and with
composition, and proves degree-one refinement injectivity for sheaves of abelian groups. It is
a helper for the proof of `Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundStatement`.
It contains no `sorry` and no new axioms.

## Provenance

The refinement map `γ(ξ)_{i₀…i_p} = ξ_{c(i₀)…c(i_p)}|_{U_{i₀…i_p}}` is the one of The Stacks
Project, Cohomology of Sheaves, section "Refinements and Čech cohomology" (tag 09UY), `cohomology.tex` lines 2439–2458 of
the registered source `stacks-flasque-affine-vanishing-kunneth-a04446e5`, for the ordered
complex of the Library module `Langlands.Cohomology.CechCochains`. Degree-one refinement
injectivity is the standard fact that `Ȟ¹(𝒰, ℱ) → Ȟ¹(𝒱, ℱ)` is injective for a sheaf `ℱ` and a
covering `𝒱` refining `𝒰` (it follows from Stacks, Cohomology of Sheaves, Lemma `lemma-cech-h1`, tag 0B8R, which embeds
`Ȟ¹(𝒰, ℱ)` into `H¹(X, ℱ)`); the proof here glues primitives directly. Names and form are a project choice.

## Definitions

All declarations are in namespace `Langlands.Cohomology.Cech`. Throughout,
`P : TopCat.Presheaf AddCommGrpCat T`, `U : ι → Opens T`, `U' : ι' → Opens T`, `β : ι' → ι`
and `hβ : ∀ j, U' j ≤ U (β j)`.

- `refine P U U' β hβ p : C P U p →+ C P U' p` sends `c` to
  `σ ↦ res (c (β ∘ σ))`, restricted from `inter U (β ∘ σ)` to `inter U' σ`.

## Results

- `inter_le_inter_comp hβ σ`: `inter U' σ ≤ inter U (β ∘ σ)`.
- `refine_apply`, `face_refine`: computation rules.
- `d_refine`: `d (refine c) = refine (d c)`.
- `refine_comp`: refining along `β` and then along `γ` is refining along `β ∘ γ`.
- `map_refine`: refinement commutes with `map U φ` for a morphism of presheaves `φ`.
- `refine_prod`: for a presheaf of rings, refinement commutes with the products `prod n z` of
  `Langlands.Cohomology.CechCup`.
- `inter_const_one a`: `inter U (fun _ : Fin 1 => a) = U a`.
- `res_d_zero_pair`: the differential of a `0`-cochain on the pair `(a, b)`, restricted to a
  smaller open, is the difference of the restrictions of its two values.
- `eq_of_locally`, `exists_gluing`: wrappers around the sheaf condition for a family of opens
  covering an open `V`.
- `le_iSup_inf_of_top_le`: if `U'` covers the space, `V ≤ ⨆ j, V ⊓ U' j`.
- `exists_d_eq_of_refine_eq_d`: for a sheaf `F` of abelian groups and a family `U'` with
  `⊤ ≤ iSup U'`, a `1`-cocycle `z` of `F` on `U` whose refinement to `U'` is a coboundary
  `d c` is a coboundary `d y` on `U`. The primitive `y (a)` is glued on `U a` from the
  sections `c j - z (a, β j)` on `U a ⊓ U' j`.
