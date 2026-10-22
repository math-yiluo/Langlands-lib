# Proof of the canonical unramified criterion

Author: Worker 231.

The closing theorem `Langlands.PadicField.canonicalUnramifiedCriterion` has type
`Langlands.PadicField.CanonicalUnramifiedCriterion.{u}`, the proposition published in
`Langlands.Galois.Local.UnramifiedCriterionStatement`, for an arbitrary universe `u`.
Thus, for every prime `p`, every `F : PadicField.{u} p`, every
`E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier` and every
instance `IsGalois F.Carrier E.field`, it proves

```lean
F.canonicalTopologicalData.ramificationIndex =
    (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex ↔
  F.absoluteInertia F.canonicalTopologicalData ≤ E.field.fixingSubgroup
```

The proof adds no hypotheses. It never uses the `IsGalois` instance, and none of
the auxiliary lemmas below assumes it. The statement pair and its imports are
unchanged. Besides the statement, the module imports the published modules
`Langlands.Weil.Local.IntermediateWeil`, `Langlands.LocalField.Normalization.Proof`
and `Langlands.Galois.Local.AbsoluteProof`. The closing theorem depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Strategy

Every subgroup below lies in the absolute Galois group
`G_F = Field.absoluteGaloisGroup F.Carrier`, and indices are Mathlib's
`Subgroup.index`. Write `I` for `F.absoluteInertia F.canonicalTopologicalData`
and `S` for the image of `G_E` under the published Galois map of an embedding
`F → E`. Write `n = [E : F]` and `r` for the relative residue degree. The proof
has three steps.

1. `S` has index `n` and `S ⊔ I` has index `r`, so `I ≤ S` exactly when `r = n`.
2. The canonical absolute ramification indices satisfy `e_E * r = n * e_F`, so
   `e_F = e_E` exactly when `r = n`.
3. For the prescribed intermediate field, `I ≤ E.field.fixingSubgroup` exactly when
   `I ≤ S`. This follows by conjugating with the published closure correction,
   because `I` is normal.

This route differs from the source derivation recorded in the statement Markdown.
It does not construct the maximal unramified extension or identify the fixed field
of inertia. Instead, it combines the published surjectivity and kernel of the
absolute residue action with the published identity `e * f = [F : Q_p]`.

## Embedding lemmas

Section `Embedding` works for `F : PadicField.{u} p` and `E : PadicField.{v} p` in
independent universes and for an arbitrary `f : F.Carrier →ₐ[Padic p] E.Carrier`.
It uses the following notation.

- `S = (extensionGaloisMap F E f).toMonoidHom.range` is the image of `G_E` in `G_F`.
- `φ = (localResidueMap F).toMonoidHom` is, by definition,
  `F.absoluteResidueHom F.canonicalTopologicalData`, the absolute residue action
  `G_F →* G_{k_F}` with `k_F = localResidueField F`.
- `n = extensionDegree F E f`.
- `r = extensionResidueDegree F E f` is the dimension of `k_E` over `k_F` for the
  residue algebra `extensionResidueAlgebra F E f`.

### The residue image and its index

`extensionResidueIntermediateField F E f` is an auxiliary definition used only in
this proof. It is the intermediate field of `AlgebraicClosure k_F` over `k_F`
given by the field range of the published
`extensionResidueFieldAlgHom F E f : k_E →ₐ[k_F] AlgebraicClosure k_F`. That
homomorphism is `ψ⁻¹ ∘ algebraMap`, where `ψ = extensionResidueClosureEquiv F E f`
is the published comparison of the algebraic closures of `k_F` and `k_E`. Thus
this field is the residue analogue of the published `extensionIntermediateField`.
`mem_extensionResidueIntermediateField` unfolds membership in it.

`extensionResidueGaloisMap_range` proves that the image of the published
`extensionResidueGaloisMap F E f : G_{k_E} → G_{k_F}` is the fixing subgroup of
this intermediate field. The proof follows that of the published
`extensionGaloisMap_range`. Every image element fixes the field by
`extensionResidueGaloisMap_fixes`. Conversely, let `τ ∈ G_{k_F}` fix the image
of `k_E`. Then the ring automorphism `ρ = ψ ∘ τ ∘ ψ⁻¹` of `AlgebraicClosure k_E`
fixes `k_E`, by the fixing hypothesis and `ψ ∘ ψ⁻¹ = id`, so
`AlgEquiv.ofRingEquiv` makes it an element of `G_{k_E}`. Its image is `τ` by
`extensionResidueClosureEquiv_galoisMap` and the injectivity of `ψ`.

`extensionResidueGaloisMap_range_index` proves that this image has index `r`.
`AlgHom.equivFieldRange` identifies the field range with `k_E` as a
`k_F`-algebra, so its `k_F`-dimension is `r`. The proof assembles the instance
`IsGalois k_F (AlgebraicClosure k_F)` from Mathlib's normality and separability
instances. Separability holds because the finite field `k_F` is perfect. Mathlib's
`IntermediateField.finrank_eq_fixingSubgroup_index` then equates `r` with the
index of the fixing subgroup.

### The residue action on `S`

`map_localResidueMap_extensionGaloisMap_range` proves that `φ(S)` is the image of
`extensionResidueGaloisMap F E f`. The inclusion `⊆` is the published commutation
`localResidueMap_extensionGaloisMap`, which states
`localResidueMap F (extensionGaloisMap F E f σ) =
extensionResidueGaloisMap F E f (localResidueMap E σ)`. For `⊇`, the published
surjectivity `E.absoluteResidueHom_surjective E.canonicalTopologicalData` writes
every `κ ∈ G_{k_E}` as `localResidueMap E σ` with `σ ∈ G_E`. The same commutation
then shows that the image of `κ` lies in `φ(S)`.

### The index of `S ⊔ I`

`extensionGaloisMap_range_sup_absoluteInertia_index` proves `(S ⊔ I).index = r`.
The published `absoluteResidueHom_ker` identifies the kernel of `φ` with `I`. The
published `absoluteResidueHom_surjective` shows that `φ` is surjective. Mathlib's
`Subgroup.comap_map_eq` gives `φ⁻¹(φ(S)) = S ⊔ ker φ`, and
`Subgroup.index_comap_of_surjective` shows that this preimage has the index of
`φ(S)`. The two preceding lemmas compute that index as `r`.

### Inertia inside `S`

`absoluteInertia_le_extensionGaloisMap_range_iff` proves `I ≤ S ↔ r = n`.
Mathlib's `Subgroup.relIndex_mul_index` for `S ≤ S ⊔ I`, the published
`extensionGaloisMap_range_index` (`S.index = n`) and the preceding lemma give
`S.relIndex (S ⊔ I) * r = n`. If `I ≤ S`, then `S ⊔ I = S`. The relative index is
then one, so `r = n`. Conversely, if `r = n`, cancelling `n > 0`
(`extensionDegree_pos`) makes the relative index one. Then
`Subgroup.relIndex_eq_one` gives `S ⊔ I ≤ S`, hence `I ≤ S`.

### The ramification identity

`ramificationIndex_mul_extensionResidueDegree` proves

```lean
E.canonicalTopologicalData.ramificationIndex * extensionResidueDegree F E f =
  extensionDegree F E f * F.canonicalTopologicalData.ramificationIndex
```

that is, `e_E * r = n * e_F`. Here `e_F` and `e_E` are the existing canonical
absolute ramification indices. Write `f_F` and `f_E` for the residue degrees
over `ZMod p` (`TopologicalData.residueDegree`). The published
`residueCardinality_eq_pow` gives residue cardinalities `p ^ f_F` and `p ^ f_E`.
The published `extensionResidueCardinality` gives `p ^ f_E = (p ^ f_F) ^ r`.
Since `p ≥ 2`, `Nat.pow_right_injective` gives `f_E = f_F * r`. The published
absolute identity `ramificationIndex_mul_residueDegree` states
`e_F * f_F = [F : Q_p]` and `e_E * f_E = [E : Q_p]`. The published tower law
`finrank_mul_extensionDegree` states `[F : Q_p] * n = [E : Q_p]`. Hence

```text
e_E * r * f_F = e_E * f_E = [E : Q_p] = [F : Q_p] * n = n * e_F * f_F.
```

Cancelling `f_F > 0` (`residueDegree_pos`) proves the identity.

`ramificationIndex_eq_iff_extensionResidueDegree_eq` deduces `e_F = e_E ↔ r = n`.
If `e_F = e_E`, the identity reads `e_F * r = e_F * n`, and `e_F > 0`
(`ramificationIndex_pos`) cancels. If `r = n`, it reads `n * e_E = n * e_F`, and
`n > 0` cancels.

`absoluteInertia_le_extensionGaloisMap_range_iff_ramificationIndex_eq` combines
the two equivalences: `I ≤ S ↔ e_F = e_E`.

## The prescribed intermediate field

Section `Intermediate` fixes `E : FiniteIntermediateExtension F.Carrier` and
writes `EP = E.asPadicField (p := p)`. As in `IntermediateWeil`, it uses the
`Padic p`-algebra structure of `EP` on `E.field` as a local instance. The
embedding is the published `intermediateEmbedding F E`, the literal inclusion
`F.Carrier →ₐ[Padic p] E.field`. The published `extensionGaloisMap_range` writes
`S` as the fixing subgroup of the image field
`extensionIntermediateField F EP (intermediateEmbedding F E)` of the chosen
closure lift. That image field need not be the literal `E.field`.

`absoluteInertia_le_fixingSubgroup_iff` proves
`I ≤ E.field.fixingSubgroup ↔ I ≤ S`. Let `c = intermediateClosureCorrection F E`.
The published `intermediateClosureCorrection_conj_mem` states that
`c * τ * c⁻¹ ∈ E.field.fixingSubgroup` exactly when `τ` fixes the image field.
The subgroup `I` is normal by the published instance `absoluteInertia_normal`.

- Suppose `I` fixes `E.field` and `τ ∈ I`. Then `c * τ * c⁻¹ ∈ I` fixes `E.field`,
  so `τ` fixes the image field.
- Suppose `I ≤ S` and `τ ∈ I`. Then `c⁻¹ * τ * c ∈ I` fixes the image field. Hence
  `c * (c⁻¹ * τ * c) * c⁻¹` fixes `E.field`, and this element is `τ`. The tactic
  `group` closes the group identity.

## The closing theorem

`canonicalUnramifiedCriterion` introduces `p`, its primality instance, `F`, `E`
and the unused Galois instance. It composes `absoluteInertia_le_fixingSubgroup_iff F E`
with `absoluteInertia_le_extensionGaloisMap_range_iff_ramificationIndex_eq` applied
to `EP` and `intermediateEmbedding F E`. The symmetric form of the resulting
equivalence is exactly the target.

## Normal intermediate fields and alternate index formulas

The following supplementary lemmas are due to Worker 282. They reuse the
existing `extensionResidueIntermediateField` and
`Langlands.Weil.Local.intermediateEmbedding` definitions, which are the same
constructions as that contribution's `criterionResidueImage` and
`criterionInclusion`. The closing theorem above and the existing public helpers
retain their statements and proofs.

`criterion_residueImage_index` states that
`(extensionResidueIntermediateField F E f).fixingSubgroup.index` equals
`extensionResidueDegree F E f`. It applies
`IntermediateField.finrank_eq_fixingSubgroup_index` to the residue image and
identifies its dimension with that of the residue field using
`AlgHom.equivFieldRange`. This is the fixing-subgroup form of the existing
`extensionResidueGaloisMap_range_index`.

`criterion_ramificationIndex_mul` retains the alternate orientation of the
ramification identity:

```lean
F.canonicalTopologicalData.ramificationIndex * extensionDegree F E f =
  E.canonicalTopologicalData.ramificationIndex * extensionResidueDegree F E f
```

Its proof first deduces the residue-degree tower identity from
`extensionResidueCardinality` and injectivity of powers of the prime `p`. It
then combines the absolute ramification identities with
`finrank_mul_extensionDegree` and cancels the positive absolute residue degree
of `F`. Its hypotheses and independent field universes are unchanged.

For `E : LocalClassField.FiniteIntermediateExtension F.Carrier`, the remaining
two lemmas assume `Normal F.Carrier E.field`. They use the actual inclusion
`intermediateEmbedding F E` with the composite p-adic algebra of
`E.asPadicField`.

- `criterion_intermediateField_eq` identifies the chosen comparison field
  `extensionIntermediateField F (E.asPadicField (p := p))
  (intermediateEmbedding F E)` with `E.field`. The proof packages
  `extensionFieldEmbedding` as an `F.Carrier`-algebra homomorphism using
  `extensionFieldEmbedding_comp`, then applies
  `AlgHom.fieldRange_of_normal`.
- `criterion_galoisMap_range` rewrites `extensionGaloisMap_range` with that
  equality to identify the image of the absolute Galois map with the actual
  `E.field.fixingSubgroup`.

These normality-based equalities supplement the existing
`absoluteInertia_le_fixingSubgroup_iff`, whose proof does not require normality.
The duplicate residue-range, mapped-range and joined-inertia-index lemmas use
the existing `extensionResidueGaloisMap_range`,
`map_localResidueMap_extensionGaloisMap_range` and
`extensionGaloisMap_range_sup_absoluteInertia_index` declarations. The identical
final criterion is represented by `canonicalUnramifiedCriterion` above.
