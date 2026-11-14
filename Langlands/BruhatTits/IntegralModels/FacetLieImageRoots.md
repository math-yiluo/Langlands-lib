# Lie-image weights of a torus-containing subgroup are its roots

Module `Langlands.BruhatTits.IntegralModels.FacetLieImageRoots`.

## Content

Let `k` be a field, `S` a commutative group scheme over `k`, and `H`, `Q`
affine group schemes over `k`. Let `t : S ⟶ H` be a homomorphism and
`j : H ⟶ Q` a homomorphism whose underlying morphism of schemes is a
monomorphism (for example a closed immersion).

- `weightSpace_comp_inf_range_eq_map`: for every character `χ` of `S`, the
  intersection of the ambient weight space `Lie(Q)_χ` (for the torus
  `t ≫ j`) with the differential image `dj(Lie(H))` equals
  `dj(Lie(H)_χ)`, the image of the weight space of `S` on `Lie(H)`.
- `nonzeroLieImageWeights_comp_eq_roots`: consequently
  `nonzeroLieImageWeights (t ≫ j) j = roots t`. The nonzero characters
  whose ambient weight space meets the differential image are exactly the
  roots of `S` on `Lie(H)`.

For a KP model morphism `φ : source ⟶ target` with special-fibre quotient
data `Q` and an integral torus `T` of the source model:

- `RelativeComponentModelHom.reductiveImageTorusMap φ Q T` is the
  special-fibre torus `T_s` mapped into the actual reductive image
  `℘_F(F') = image(φ_s ≫ π)`. It is the special-fibre inclusion of `T`
  followed by the schematic-image projection of `φ_s ≫ π`.
- `reductiveImageTorusMap_comp_inclusion`: composing it with the closed
  inclusion `℘_F(F') ⟶ Q.quotient` gives `φ.quotientTorusInclusion Q T`.
  This follows from `SchematicImage.projection_inclusion`.
- `nonzeroLieImageWeights_quotientTorusInclusion`: the left side of the KP
  facet sign formula `HasLieWeightSignFormula` (KP Axiom 4.1.22(3), second
  paragraph) equals `roots (φ.reductiveImageTorusMap Q T)`, the roots of
  `T_s` in `℘_F(F')`.

No splitness, smoothness or reductivity hypothesis is needed.

## Proofs

For `weightSpace_comp_inf_range_eq_map`: an element of the intersection is
`dj x` with `dj x ∈ Lie(Q)_χ`. The Library lemma
`lieKernelHomLinear_mem_weightSpace_iff` uses that `j` is a monomorphism to
give `x ∈ Lie(H)_χ`. Conversely `lieKernelHomLinear_mem_weightSpace` sends
`Lie(H)_χ` into `Lie(Q)_χ`.

For `nonzeroLieImageWeights_comp_eq_roots`: by the previous lemma the
condition reads `map dj (Lie(H)_χ) ≠ ⊥`. Since `dj` is injective
(`Lie.targetMapLinear_injective`), `Submodule.map` along it is injective, so
the condition is `Lie(H)_χ ≠ ⊥`.

The last theorem rewrites `quotientTorusInclusion` by the factorization and
applies the general lemma to the schematic-image inclusion, which is a
monomorphism (`SchematicImage.instSchematicImage2`).

## Provenance

Internal infrastructure for the proof of
`UnramifiedFacetCommonTorusStatement` (KP 4.1.22(3), Kaletha–Prasad,
*Bruhat–Tits theory: a new approach*, Axiom 4.1.22). It is the standard
fact that, for a closed subgroup `H ⊆ Q` containing a torus, the roots of
`Lie(H)` are the torus weights on `Lie(Q)` that occur in `Lie(H)`. It turns
the Lie-image weight set of the facet sign formula into a root set, so that
the Library's base-change and restriction lemmas for `roots` apply.
