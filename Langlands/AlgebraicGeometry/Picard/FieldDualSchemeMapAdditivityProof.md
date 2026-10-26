# Proof of additivity of the dual scheme maps over a field

Module `Langlands.AlgebraicGeometry.Picard.FieldDualSchemeMapAdditivityProof`
proves the Library proposition
`Langlands.AbelianScheme.FieldDualSchemeMapAdditivityStatement`, with no
hypotheses.

## Main theorem

`Langlands.AbelianScheme.fieldDualSchemeMapAdditivity :
FieldDualSchemeMapAdditivityStatement.{u}`.

The statement quantifies over all proofs `preservation` of
`pullbackTensorComparisonIsIsoStatement` and `stability` of
`PicardZeroPullbackStatement`, every field `k : Type u`, all abelian schemes
`A`, `B` over `Spec k` with chosen dual schemes `hA`, `hB`, and all
homomorphisms `f g : A ⟶ B`. It asserts

`dualSchemeMap homPicardZeroPullback (f + g) hA hB =
  prod.lift (dualSchemeMap homPicardZeroPullback f hA hB)
    (dualSchemeMap homPicardZeroPullback g hA hB) ≫
      dualTensor stability A hA preservation`,

that is, `(f + g)^∨ = f^∨ + g^∨` for the group law on the dual given by the
tensor product of line bundles.

## Proof

The theorem applies `fieldDualSchemeMapAdditivity_of_classification`
(module `DualSchemeMapAdditivity`) to two proofs:

* `picardZeroLineBundleClassification` (module
  `PicardZeroLineBundleClassificationProof`), which proves
  `PicardZeroLineBundleClassificationStatement`;
* `Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions` (module
  `SmoothProperConnectedGlobalFunctionsProof`), which proves
  `SmoothProperConnectedGlobalFunctions` over an arbitrary base.

The first result derives the target from these two propositions. The proof
is this single term; the Markdown of the three modules documents the steps.

## Provenance

The target is the additivity of dualization of homomorphisms; compare
Edixhoven, van der Geer and Moonen, *Abelian Varieties* (registered
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), Chapter VII,
Lemma (7.16)(i), printed p.104 (PDF p.108). See the Markdown of
`DualSchemeMapAdditivity` for the route.
