# Čech exactness for flasque sheaves

Author: Worker 727.

This module proves that the ordered Čech complex (module `Langlands.Cohomology.CechCochains`) of
a flasque sheaf of abelian groups for a finite family of opens is exact in every positive
degree. It is a helper for the proof of
`Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingStatement`,
where it shows that injective `𝒪_X`-modules have vanishing higher Čech cohomology. It contains
no `sorry` and no new axioms.

## Main result

`Langlands.Cohomology.Cech.exactAt_of_isFlasque`:

```lean
theorem exactAt_of_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    [TopCat.Presheaf.IsFlasque F.1] {ι : Type w} [Finite ι]
    (U : ι → Opens T) (p : ℕ) : ExactAt F.1 U p
```

Here `T : TopCat.{u}` and `TopCat.Presheaf.IsFlasque` is Mathlib's class: every restriction map
is surjective (an epimorphism of abelian groups). The family `U` need not cover anything: the
Čech complex of the family is exact in degrees `p + 1 ≥ 1`. The index type must be finite.

## Provenance

This is the case of finite families of Stacks Lemma 09SZ (`lemma-flasque-acyclic-cech`,
`cohomology.tex` lines 1963-1978 of the registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`, Stacks commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`): for a flasque sheaf `F` and an open covering `𝒰`,
`Ȟ^p(𝒰, F) = 0` for `p > 0`. A family `U` is an open covering of its union `⋃ U_i`, and the
two have the same Čech complex. Stacks deduces it from the Čech-to-cohomology
spectral sequence and the acyclicity of flasque sheaves. That route is not available here, so
the Lean proof is an elementary induction instead (see below). The project needs it for
injective modules, the case of Stacks Lemma 01EP (`lemma-injective-trivial-cech`); injective
modules are flasque by the Library's
`Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclic.isFlasque_of_injective`.

## Proof

Let `z` be a `(p + 1)`-cocycle. By induction over finite sets `S ⊆ ι`, find a `p`-cochain `y`
such that every component of `z - d y` vanishes on `(⨆ j ∈ S, U j) ⊓ inter U τ`.

- For `S = ∅` this open is `⊥`, and any two sections over an open contained in `⊥` agree
  (`eq_of_le_bot`).
- For `insert i S`, let `z' = z - d y`, again a cocycle that vanishes on
  `(⨆ j ∈ S, U j) ⊓ inter U τ`. For each `p`-index `σ`, the section `z' (i, σ)` on
  `U i ⊓ inter U σ` and the section `0` on `(⨆ j ∈ S, U j) ⊓ inter U σ` agree on the overlap.
  They glue over the union of the two opens (`exists_glue₂`), and flasqueness extends the
  glued section to a section `w σ` on `inter U σ` (`surjective_res`). Then `y + w` works for
  `insert i S`. On `U i ⊓ inter U τ`, the cocycle condition at `(i, τ)`
  (`res_eq_sum_of_d_eq_zero`) shows that `z' τ` equals `d w τ`. On the part over `S`, both
  `z' τ` and `d w τ` vanish. Two sections that agree on two opens agree on their union
  (`eq_of_res_eq₂`).

For `S = univ` the open `(⨆ j, U j) ⊓ inter U τ` is `inter U τ`, so `z = d y`.

## Auxiliary results

In namespace `Langlands.Cohomology.Cech`, for a sheaf `F : TopCat.Sheaf AddCommGrpCat.{u} T`:

- `eq_of_le_bot hO s t`: sections over an open `O ≤ ⊥` are equal.
- `eq_of_res_eq₂ h₁ h₂ hV s t e₁ e₂`: if `V ≤ O₁ ⊔ O₂`, with `O₁, O₂ ≤ V`, then sections over
  `V` with equal restrictions to `O₁` and `O₂` are equal (Mathlib's `eq_of_locally_eq₂`).
- `exists_glue₂ a b h`: sections over `A` and `B` agreeing on `A ⊓ B` glue to a section over
  `A ⊔ B` (Mathlib's `existsUnique_gluing'` for a family indexed by `Fin 2`).
- `surjective_res h`: the restriction maps of a flasque sheaf are surjective.
