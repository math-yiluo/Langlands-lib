# Proof: the spaces `X_Σ` of discrete `G`-sets are `G`-spaces

Author: Worker 148, adapting the proof of `InducedSpace.continuityStatement`
by Worker 99.

This module proves the Library statement
`Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace.ContinuityStatement`
(module `SetInducedSpaceContinuityStatement`). The source is Berkovich,
*Étale equivariant sheaves on p-adic analytic spaces* (unfinished manuscript,
1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.2, printed p.4. The theorem is

`Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace.continuityStatement :
ContinuityStatement.{u, v, z}`.

Let `G` be a topological group, `X` a `G`-space (`gSpaceProperty K G X`) and
`S` a `G`-set all of whose stabilizers are open. Then Berkovich's space
`setInduced X S` satisfies `gSpaceProperty K G`. Its underlying space is
Hausdorff, and its action of `G` is continuous for Berkovich's test triples.
Berkovich uses this fact on p.4 without stating it separately.

The lemmas on disjoint unions come from the helper module
`LocalizedSigmaNearness` by Worker 99, written for the sibling statement
`InducedSpace.ContinuityStatement`. The proof below follows Worker 99's proof
of that statement (`InducedSpace.continuityStatement`). Here the action
moves a copy without the conjugation by coset representatives, so the steps
with representatives are not needed.

## Hausdorff

The underlying space of `X_S = (copies X S).pt` is by definition the
topological sigma type `(_ : S) × (space of X)`. The space of `X` is Hausdorff
by the first half of `gSpaceProperty K G X`. A sigma type of Hausdorff spaces
is Hausdorff (Mathlib instance).

## Continuity

Fix a test triple `τ` on `X_S`. We must show that the set of `g` with
`IsNear τ (actionMap X S g) (𝟙 _)` is a neighbourhood of `1` in `G`.

1. One copy. By `TestTriple.exists_locus_subset_range_localizedSigmaCofan`,
   `τ.locus` lies in a single copy `s₀`, i.e. in `Set.range (Sigma.mk s₀)`.
2. Finitely many test triples on `X`. The preimage of `τ.locus` under
   `copy X S s₀` is compact (`isCompact_preimage_localizedSigmaCofan_inj`).
   The Library lemma `exists_isNear_postcomp` therefore gives a finite set `E`
   of test triples on `X` with the following property. If `φ, ψ : W ⟶ X.V`
   are near for every triple in `E`, then
   `IsNear τ (φ ≫ copy X S s₀) (ψ ≫ copy X S s₀)`.
3. The neighbourhood. By continuity of the action of `G` on `X`, the set
   `V = ⋂_{τ' ∈ E} X.ρAut⁻¹(nearIdentity τ')` is a neighbourhood of `1` in
   `G`, because it is a finite intersection (`Filter.biInter_finset_mem`).
   The stabilizer of `s₀` is open by hypothesis and contains `1`. So
   `N = stabilizer(s₀) ∩ V` is a neighbourhood of `1` in `G`.
4. Testing copy by copy. Let `g ∈ N`, so `g • s₀ = s₀`. By
   `isNear_of_localizedSigmaCofan` it suffices to show, for every `s : S`,
   that `IsNear τ (copy X S s ≫ actionMap X S g) (copy X S s)`. By
   `copy_actionMap`, the left morphism is `X.ρ g ≫ copy X S (g • s)`.
   - If `s = s₀`, it is `X.ρ g ≫ copy X S s₀`. Since `g ∈ V`, the morphisms
     `X.ρ g` and `𝟙 X.V` are near for every triple in `E`. Step 2 gives the
     claim.
   - If `s ≠ s₀`, then also `g • s ≠ s₀`, because `g • s₀ = s₀` and `g • ·`
     is injective. Both morphisms factor through a copy other than `s₀`, so
     their underlying maps miss `τ.locus`
     (`preimage_locus_comp_localizedSigmaCofan_inj_eq_empty`).
     `isNear_of_preimage_eq_empty` gives the claim.

## Relation to the expected route

The statement's Markdown sketches a route through the finitely many copies
`s_1, …, s_n` met by the compact domain `U`, using the open subgroup
`⋂ stabilizer(s_i)`. The implemented proof is the case `n = 1` of that route.
In the Library's saturated presentation of a disjoint union, every test
domain is a local domain inside one chart of the disjoint-union atlas. It
therefore lies in a single copy, so no finiteness argument over copies is
needed. The continuity of the action on `X` enters only through the finitely
many test triples on `X` provided by `exists_isNear_postcomp`. The proof does
not use the comparison `SetInducedSpace.inducedIso` mentioned there.
