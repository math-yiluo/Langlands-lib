# Cyclic subfields and the canonical reduced-norm kernel

Let `K` be a field and `D` a finite-dimensional central division
`K`-algebra, both in an arbitrary universe `u`. Let `L : Type uL` be a
finite field extension of `K`, in an independent arbitrary universe.
Fix an actual embedding `ι : L →ₐ[K] D`. There is no characteristic
restriction. Write `N = Langlands.BinaryElementary.Reduced.coefficientNorm K D`
for the restriction of the canonical reduced norm to `Dˣ`, and
`f = Units.map ι.toMonoidHom : Lˣ →* Dˣ`.

The definition `Langlands.CentralDivision.fieldNormOneImage ι` is the
subgroup `f(ker(Units.map (Algebra.norm K : L →* K)))` of `Dˣ`.
It uses the actual field norm and the actual embedding. The definition
does not require `L/K` to be Galois or to have a specified degree.

If `Module.finrank K L = Langlands.CentralSimple.reducedDegree K D`,
`coefficientNorm_comp_field` proves

`N.comp f = Units.map (Algebra.norm K : L →* K)`.

It applies the proved elementwise comparison
`Langlands.CentralSimple.reducedNorm_eq_field_norm` to the underlying
element of each unit, then uses extensionality for units and
homomorphisms. The theorem `fieldNormOneImage_eq_range_inf_ker` rewrites
the resulting subgroup as

`fieldNormOneImage ι = f.range ⊓ N.ker`.

Its proof identifies the field-norm kernel with the preimage of `N.ker`
and uses the subgroup identity for the image of a preimage. These two
comparisons require the displayed degree equality but do not require
separability.

The theorem `commutator_le_ker_coefficientNorm` proves

`commutator Dˣ ≤ N.ker`.

This has no field-extension, embedding, or degree hypothesis. It is
Mathlib's `Abelianization.commutator_subset_ker` applied to `N`, whose
target `Kˣ` is commutative.

Now assume `[IsGalois K L]` and `[IsCyclic (L ≃ₐ[K] L)]`.
The theorem `exists_commutator_of_mem_fieldNormOneImage` proves that
each `x ∈ fieldNormOneImage ι` is a single commutator:

`∃ v u : Dˣ, x = ⁅v, u⁆`.

Here `⁅v, u⁆ = v * u * v⁻¹ * u⁻¹` in the original group `Dˣ`.
The proof takes a field-norm-one unit mapping to `x` from subgroup
image membership. Equality of the corresponding norm units gives
field norm one on underlying elements. The imported theorem
`exists_commutator_of_cyclic_field_norm_eq_one` then supplies the
commutator, with its implementing unit constructed by field-embedding
conjugacy. No generator or implementing unit is an added premise.
The theorem `fieldNormOneImage_le_commutator` places this subgroup in
`commutator Dˣ` by the usual membership lemma for a commutator.
These two theorems do not require the reduced-degree equality.

With the degree equality as well,
`exists_commutator_of_field_image_reducedNorm_eq_one` proves that an
original unit `x : Dˣ` satisfying `x ∈ f.range` and `N x = 1` is a single
commutator in `Dˣ`. It uses `fieldNormOneImage_eq_range_inf_ker` to
reduce to the preceding theorem. Finally,
`range_inf_ker_coefficientNorm_eq_range_inf_commutator` proves

`f.range ⊓ N.ker = f.range ⊓ commutator Dˣ`.

One inclusion uses the cyclic-field commutator result; the other uses
`commutator_le_ker_coefficientNorm`. Thus the equality concerns the
intersection with the specified field-unit image.

Worker 1757 authored this internal deduction from the imported
canonical reduced-norm comparison, cyclic field-norm commutator proof,
and Mathlib's subgroup and abelianization identities. It introduces
no new source assertion.

The embedding and the degree condition remain supplied data where
stated. This module constructs no local cyclic maximal subfield and
does not move arbitrary division-algebra units into one modulo
commutators. It does not prove local SK₁ vanishing or
`Langlands.GroupScheme.LocalKneserTitsStatement`.
