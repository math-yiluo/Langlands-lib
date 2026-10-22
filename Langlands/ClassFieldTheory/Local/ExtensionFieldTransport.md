# Canonical field transport to the common algebraic closure

Author: Worker 28. This is an internal derived construction for comparison of
standalone and common-closure Weil reciprocity candidates. All declarations
are in `Langlands.LocalClassField`. The two fields retain independent universes;
the input is any prime `p`, finite p-adic fields `F` and `E`, and an actual
`Padic p`-algebra homomorphism `f : F.Carrier →ₐ[Padic p] E.Carrier`.

## Actual constructions

`extensionFiniteIntermediate F E f` packages the existing
`Weil.Local.extensionIntermediateField F E f` with its existing
finite-dimensionality certificate as a `FiniteIntermediateExtension F.Carrier`.
Write `J` for this package and `Jp` for `J.asPadicField (p := p)`.

`extensionIntermediatePadicEquiv` has the underlying ring equivalence of the
published `extensionIntermediateFieldEquiv`. Its codomain has exactly the
composite p-adic algebra structure used by `Jp`, not a supplied algebra
structure. The base-scalar compatibility follows from `f.commutes` and the
original equivalence's compatibility with scalars from `F`.
`extensionIntermediatePadicEquiv_coe` identifies its value in the algebraic
closure with the original `extensionFieldEmbedding F E f`.

`extensionIntermediateContinuousAlgEquiv` equips this same equivalence with
continuity in both directions for `E.canonicalTopologicalData` and
`CommonClosure.canonicalData F J`. Both maps are isometries for the canonical
spectral norms by the published `extension_isometry` theorem. The topology in
`canonicalTopologicalData` is definitionally the one from that norm.

`extensionIntermediateUnitsEquiv` is the induced topological group equivalence
`E.Carrierˣ ≃ₜ* J.fieldˣ`. Its underlying map is Mathlib's `Units.mapEquiv`
applied to the actual field equivalence, and its continuity proofs use
`Continuous.units_map`. The theorem `extensionIntermediateUnitsEquiv_apply`
records its action on underlying field elements.

## Normalized absolute values

`extensionIntermediate_canonicalNorm` proves that the field equivalence
preserves the base-extending spectral norm. The theorem
`extensionIntermediate_normalizedAbs` then proves

`(CommonClosure.canonicalData F J).normalizedAbs (extensionIntermediatePadicEquiv F E f x) = E.canonicalTopologicalData.normalizedAbs x`.

The proof rewrites each normalized absolute value as its canonical norm
raised to its degree over `Padic p`, uses spectral norm preservation, and
identifies the two degrees with the actual p-adic linear equivalence's
`finrank_eq`. This applies to every field element, including zero.

`extensionIntermediateUnitsEquiv_normalizedAbs` is the same identity on
units. `extensionIntermediateUnitsEquiv_symm_normalizedAbs` gives the inverse
identity used when composing a common-closure reciprocity component with the
inverse unit equivalence. It follows by applying the forward field identity
and the equivalence's inverse law.

## Derived provenance and source locations

This module derives its constructions from existing Library results rather
than asserting a new theorem from external literature:

- `Langlands/Weil/Local/ExtensionGalois.lean`, declarations
  `extensionFieldEmbedding`, `extensionIntermediateField`,
  `extensionIntermediateFieldEquiv`, and
  `extensionIntermediateField_finiteDimensional`: the exact chosen embedding,
  image field, algebraic equivalence and finiteness certificate.
- `Langlands/ClassFieldTheory/Local/ReciprocitySystem.lean`, namespace
  `FiniteIntermediateExtension`, declarations `asPadicField` and `field`,
  and `CommonClosure.canonicalData`: the exact common-closure field and
  topological structures that the transport must match.
- `Langlands/Weil/Local/ExtensionResidue.lean`, declarations
  `canonicalNorm_map` and `extension_isometry`: preservation of the spectral
  norm under a p-adic algebra embedding, proved from
  `minpoly.algHom_eq` rather than a compatibility hypothesis.
- `Langlands/LocalField/Normalization/Proof.lean`, declaration
  `PadicField.TopologicalData.normalizedAbs_eq_canonicalNorm_pow_degree`:
  the actual residue-cardinality normalization as a power of the spectral
  norm. Its paired Markdown explains the arithmetic derivation.
- Pinned Mathlib, `Topology/Algebra/Algebra/Equiv.lean` supplies
  `ContinuousAlgEquiv`; `Algebra/Group/Units/Equiv.lean` supplies
  `Units.mapEquiv`; `Topology/Algebra/Monoid.lean` supplies
  `Continuous.units_map`. The equivalence degree identity is
  `LinearEquiv.finrank_eq`.

The imported modules' paired documentation records their original-source
provenance. In particular, the spectral-norm and normalization inputs refer
to Serre, *Local Fields*, Chapter II, section 2, Proposition 3 and its
corollaries, pages 28–30, and section 5, page 36. This helper's proof is the
formal composition above; it does not claim a separate original-source
formulation of these implementation interfaces.

## Scope

The field identification retains the choice of algebraic-closure embedding
already present in `extensionIntermediateFieldEquiv`. No independence,
identity/composition coherence, or selected reciprocity map is asserted.
This module supplies the field side of the comparison only. The Weil-group
comparison, residue-degree scaling, candidate composition and geometric
normalization are separate parts of the surrounding comparison construction.
It asserts no reciprocity existence, uniqueness, norm-residue relation or
epsilon-system existence.
