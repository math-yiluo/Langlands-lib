# Refinement of ordered Čech covers and cover independence of the cup product

Module `Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqRefine`, namespace
`Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq`.

## Purpose

`AllSeq.cohomologyIso` identifies the cohomology of the ordered Čech cochain complex of a finite
affine cover with actual cohomology. `AllSeq.cupCanonical` uses it to define the cup product
`H¹(X, 𝒪_X) × H¹(X, 𝒪_X) ⟶ H²(X, 𝒪_X)`, and that definition depends on the cover. This module
shows that refining the cover does not change these identifications. In particular,
`cupCanonical` gives the same product on a cover and on any refinement.

Throughout, `U : I → X.Opens` and `V : J → X.Opens` are families of opens with finite index
types. The map `β : J → I` satisfies `hβ : ∀ j, V j ≤ U (β j)`, so `V` refines `U` along `β`.

## Sheaf level (section `Sheaf`)

For `M : X.Modules`:

- `inter_le_refine β hβ τ`: `inter V τ ≤ inter U (β ∘ τ)` for every tuple `τ : Fin n → J`.
- `refineTerm β hβ M p : term U M p ⟶ term V M p`. Its `τ`-component, for
  `τ : Fin (p + 1) → J`, is the `(β ∘ τ)`-component followed by restriction along
  `inter_le_refine` (`refineTerm_π`).
- `refineTerm_d`: these maps commute with the ordered Čech differentials `d`.
- `refineComplex β hβ M : complex U M ⟶ complex V M` is the resulting map of sheafified ordered
  Čech complexes (`refineComplex_f`).
- `augmentation_refineTerm` and `aug_refineComplex`: the map is compatible with the augmentations
  `M ⟶ complex U M` and `M ⟶ complex V M`, that is,
  `aug U M ≫ refineComplex β hβ M = single₀.map (𝟙 M) ≫ aug V M`.

## Cochain level (section `Cochain`)

For `π : X ⟶ Spec R`:

- `refineCochain π U V β hβ M : cochainComplex π U M ⟶ cochainComplex π V M` is the image of
  `refineComplex` under relative global sections, conjugated by `sectionsComplexIso`.
- `refineCochain_f_apply`: on a cochain `c` and a tuple `τ`, the refined cochain is
  `M.presheaf.map (homOfLE (inter_le_refine β hβ τ)).op (c (β ∘ τ))`.
- `cohomologyIso_refine` (**independence of the cover**): assume `π` is separated, `M` is
  quasi-coherent, both families cover `X` (`hU`, `hV`) and consist of affine opens (`hUa`,
  `hVa`). Then
  `homologyMap (refineCochain π U V β hβ M) n ≫ (cohomologyIso π V M hV hVa n).hom =
  (cohomologyIso π U M hU hUa n).hom`.
  The proof applies `AcyclicResolution.resolutionComparison_naturality` to the two augmented
  resolutions and the map `refineComplex` over `𝟙 M`.

## Structure sheaf (section `Unit`)

For `M = unitModule X`:

- `refineCochain_unit_eq`: `refineCochain` is the Library's `Langlands.Cohomology.Cech.refine`
  on `Cech.C (ab X.presheaf)`.
- `refine_mem_ker`: the refinement of a cocycle is a cocycle.
- `canonicalClass_refine`: the actual class of a cocycle `z` on `U` equals the actual class of
  its refinement on `V`. This follows from `cohomologyIso_refine` and `homologyMap_classMap`.
- `refineCochain_cup`: refinement commutes with the ordered cup product `cup` of `1`-cochains.
  The proof uses `Cech.refine_prod`.
- `cupCanonical_refine` (**cover independence of the cup product**): with the hypotheses of
  `cohomologyIso_refine` for `M = unitModule X`, for all `x y : H¹(X, 𝒪_X)`,
  `cupCanonical π V hV hVa x y = cupCanonical π U hU hUa x y`.

## Provenance

This is an internal derivation. `refineCochain` is the standard refinement map of Čech complexes
`γ : (ξ_{j₀…j_p}) ↦ (ξ_{c(i₀)…c(i_p)}|_{U_{i₀…i_p}})` of Stacks Project, Section 20.15
(tag 09UY), with `c = β` and the roles of the two covers named `V`, `U` here. The comparison with
actual cohomology uses the Library's naturality of `resolutionComparison` for maps of acyclic
resolutions, and the identification on cochains uses `Langlands.Cohomology.Cech.refine` and
`Cech.refine_prod` from `Langlands.Cohomology.CechRefine`.
