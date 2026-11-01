# Global sections of the bi-Čech terms

Author: Worker 1147.

Lean module: `Langlands.AlgebraicGeometry.Modules.BiCech.GlobalSections`.
It is a helper for the proof of
`Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement`.

Let `𝒲 : BiCover P` and `F : P.Modules`.

## Components

- `ofSheafOn` and `toSheafOn` identify global sections of `sheafOn F W` with `F(W)`. They
  are mutually inverse restrictions along the equality `W ∩ ⊤ = W`.
- `compF z p q h s t ∈ F(biOpen s t)` is the `(s, t)`-component of a global section `z`
  of the degree-`n` bi-Čech term. `compF_eq_iff` states that a section is determined by
  its components.
- `compF_add`, `compF_zero`, `compF_sum` and `compF_zsmul` give additivity.
- `compF_smul`: a global function acts on components through restriction.
- `structureRingHom_comp_biOpen` identifies the restriction of the structure map
  `R → Γ(P, ⊤)` with the structure map to `Γ(P, W)`. It is the analogue, for an arbitrary
  open, of the Library's `CechResolution.structureRingHom_comp`.

## Concentrated sections

For `h : p + q = n` and a family `c s t ∈ F(biOpen s t)` of bidegree `(p, q)`,
`insT h c` is the sum over `s` and `t` of the biproduct inclusions of the `c s t`.

- `compF_insT_self`: the components of `insT h c` in bidegree `(p, q)` are `c`.
- `compF_insT_ne`: its components in every other bidegree vanish.

These follow from `biproduct.ι_π_self` and `biproduct.ι_π_ne`.

## Differential

- `horF` and `verF` are the two Čech differentials on families over the opens
  `biOpen s t`.
- `compF_D_zero_succ`, `compF_D_succ_zero` and `compF_D_succ_succ` express the components
  of `D z` through these, using `toT_D` and `DT` from `BiCech.Complex` and
  `BiCech.Sections`.
- `D_insT`: `D (insT h c) = insT (horF c) + (-1)^p • insT (verF c)`. The proof compares
  components bidegree by bidegree.

Provenance: internal bookkeeping.
