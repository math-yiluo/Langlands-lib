# Standalone Weil groups in the prescribed common closure

Author: Worker 100. This is the minimal local-factor wrapper for the derived
construction in `Langlands.Weil.Local.IntermediateWeil`; that module's paired
Markdown explains the closure choice, exact range, topology and proofs.

For any `F : PadicField.{uF} p` and `E : CommonClosure.Extension F`,
`CommonClosure.standaloneWeilEquiv F E` is the constructed continuous group
isomorphism

```lean
localWeilGroup (E.asPadicField (p := p)) ≃ₜ* CommonClosure.weilSubgroup F E
```

It is an abbreviation for `intermediateWeilEquiv F E`; the codomain is the
actual subgroup fixing the specified `E.field`. No comparison hypothesis is
added. Its direction pulls common-closure representations back to the
standalone group; its inverse pulls standalone representations back to the
common-closure group. Existing `FiniteRepresentation.continuousRestrict` and
`ExactGrothendieckGroup.continuousRestrict` apply directly. No additional
representation quotient is defined.

`standaloneWeilEquiv_baseDegree` and `standaloneWeilEquiv_degree` translate the
proved residue-degree scaling into the existing
`CommonClosureSpectral.baseDegree`, in multiplicative and integer notation.
The multiplier is the actual
`extensionResidueDegree F (E.asPadicField (p := p)) (intermediateEmbedding F E)`.
`standaloneWeilEquiv_normCharacter` and its `symm` version identify
`CommonClosureWeilDeligne.normCharacter` with the standalone normalized norm.
These are direct uses of the group-level formulas.

`commonClosureInertia_eq` states that
`CommonClosureWeilDeligne.inertia F E`, defined as the kernel of restricted
base degree, equals `intermediateInertia F E`, defined as the inverse image
of ambient inertia under the subgroup inclusion. This is definitional
equality. The forward and inverse inertia membership lemmas and
`standaloneInertiaEquiv` expose the proved continuous identification of
standalone inertia with precisely that existing kernel.

The wrapper imports the group construction and the existing
`CommonClosureWeilDeligne` module. The group construction does not import any
local-factor module, so this introduces no circular dependency. All wrapper
facts are derived directly from these imports. There are no additional
literature claims and no upper-filtration, conductor, epsilon or DH81 laws.
Private signature and consumer checks preserve the separate `uF` and `uV`
parameters of `CommonClosure.Virtual.{uF,uV}` in both directions.
