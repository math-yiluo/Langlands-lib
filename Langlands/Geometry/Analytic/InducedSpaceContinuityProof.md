# Proof: induced spaces of `H`-spaces are `G`-spaces

This module proves the Library statement
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace.ContinuityStatement`
(module `InducedSpaceContinuityStatement`; Berkovich, *Étale equivariant sheaves
on p-adic analytic spaces*, §1.1.2, printed p.2). The theorem is

`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace.continuityStatement :
ContinuityStatement.{u, v, z}`.

Let `H` be an open subgroup of a topological group `G` and `X` an `H`-space
(`gSpaceProperty K H X`). Then the induced space `inducedAction H X` satisfies
`gSpaceProperty K G`: its underlying space is Hausdorff and its action of `G`
is continuous for Berkovich's test triples. The disjoint-union lemmas come
from the helper module `LocalizedSigmaNearness`.

## Hausdorff

The underlying space of `X_{G/H}` is by definition the topological sigma type
`(c : G ⧸ H) × (space of X)`. The space of `X` is Hausdorff by the first half
of `gSpaceProperty K H X`, and a sigma type of Hausdorff spaces is Hausdorff
(Mathlib instance).

## Continuity

Fix a test triple `τ` on `X_{G/H}`. We must show that the set of `g` with
`IsNear τ (actionMap H X g) (𝟙 _)` is a neighbourhood of `1` in `G`.

1. One copy. By `TestTriple.exists_locus_subset_range_localizedSigmaCofan`,
   `τ.locus` lies in a single copy `c₀`, i.e. in `Set.range (Sigma.mk c₀)`.
2. Finitely many test triples on `X`. The preimage of `τ.locus` under
   `copy H X c₀` is compact (`isCompact_preimage_localizedSigmaCofan_inj`).
   The Library lemma `exists_isNear_postcomp` therefore gives a finite set `E`
   of test triples on `X` with the following property. If `φ, ψ : W ⟶ X` are
   near for every triple in `E`, then
   `IsNear τ (φ ≫ copy H X c₀) (ψ ≫ copy H X c₀)`.
3. The neighbourhood. By continuity of the action of `H` on `X`,
   `V = ⋂_{τ' ∈ E} ρ⁻¹(nearIdentity τ')` is a neighbourhood of `1` in `H`
   (a finite intersection). Since `H` is open, its image in `G` is a
   neighbourhood of `1` in `G`. Its preimage `W` under the continuous map
   `g ↦ c₀.out⁻¹ * g * c₀.out`, which sends `1` to `1`, is again a
   neighbourhood of `1` in `G`.
4. Elements of `W`. Let `g ∈ W` and `h ∈ V` with
   `(h : G) = c₀.out⁻¹ * g * c₀.out`. Then
   `(g * c₀.out)⁻¹ * c₀.out = h⁻¹ ∈ H`, so `g • c₀ = c₀`. The correction
   `correction H g c₀ = (g • c₀).out⁻¹ * (g * c₀.out)` equals `h`.
5. Testing copy by copy. By `isNear_of_localizedSigmaCofan` it suffices to
   show, for every coset `c`, that
   `IsNear τ (copy H X c ≫ actionMap H X g) (copy H X c)`. By
   `copy_actionMap`, the left morphism is
   `X.ρ (correction H g c) ≫ copy H X (g • c)`.
   - If `c = c₀`, it is `X.ρ h ≫ copy H X c₀`. Since `h ∈ V`, `X.ρ h` and
     `𝟙 X.V` are near for every triple in `E`. Step 2 gives the claim.
   - If `c ≠ c₀`, then also `g • c ≠ c₀`, because `g • c₀ = c₀` and `g • ·` is
     injective. Both morphisms factor through a copy other than `c₀`, so their
     underlying maps miss `τ.locus`
     (`preimage_locus_comp_localizedSigmaCofan_inj_eq_empty`).
     `isNear_of_preimage_eq_empty` gives the claim.

## Relation to the expected route

The statement's Markdown sketches a route through the finitely many copies
`c_1, …, c_n` met by the compact domain `U`, using the open subgroup
`⋂ c_i.out H c_i.out⁻¹`. The implemented proof is a special case of that
route with `n = 1`. In the Library's saturated presentation of a disjoint
union, every test domain is a local domain inside one chart of the
disjoint-union atlas. It therefore lies in a single copy, so no finiteness
argument over copies is needed. The continuity of the `H`-action enters only
through the finitely many test triples on `X` provided by
`exists_isNear_postcomp`.
