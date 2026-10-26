# Additivity of actual dual maps over a quasi-separated base

`Langlands.AbelianScheme.relativeDualSchemeMapAdditivity` proves the Library proposition
`Langlands.AbelianScheme.RelativeDualSchemeMapAdditivityStatement.{u}` (module
`Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeMapAdditivityStatement`). The theorem's
type is exactly this proposition.

## Statement

Fix a proof `preservation` that the pullback tensor comparison of line bundles is an
isomorphism, and a proof `stability` that geometrically Picard-zero line bundles are stable
under pullback. These are the two published propositions quantified in the target. Let `S` be a
quasi-separated scheme, and let `A` and `B` be abelian schemes over `S` with chosen dual
schemes `hA : HasDualScheme A` and `hB : HasDualScheme B`. Then for all homomorphisms
`f g : A ⟶ B`,

`(f + g)^∨ = ⟨f^∨, g^∨⟩ ≫ μ`,

where `(-)^∨` is the actual dual map `dualSchemeMap homPicardZeroPullback _ hA hB : B^∨ ⟶ A^∨`
and `μ = dualTensor stability A hA preservation : A^∨ × A^∨ ⟶ A^∨` is the dual scheme's tensor
multiplication. In words, dualization carries the sum of homomorphisms to the sum of dual
maps. This is the relative form of Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft (registered `edixhoven-vandergeer-moonen-abelian-varieties-draft`),
Corollary (7.17), printed p.104 (PDF p.108).

## Proof

The proof introduces the quantified data `preservation`, `stability`, `S` (with its
`QuasiSeparatedSpace` instance), `A`, `B`, `hA`, `hB`, `f` and `g`. It then applies the
published theorem `Langlands.AbelianScheme.dualSchemeMap_add` (module
`Langlands.AlgebraicGeometry.Picard.DualSchemeMapAdditivity`). That theorem proves the same
equation over an arbitrary base scheme, from two further inputs, both supplied here by
published theorems:

- the classification of geometrically Picard-zero line bundles up to a base twist,
  `PicardZeroLineBundleClassificationStatement.{u}`. This is
  `Langlands.AbelianScheme.picardZeroLineBundleClassification` (module
  `Langlands.AlgebraicGeometry.Picard.PicardZeroLineBundleClassificationProof`);
- the relative global-functions statement `SmoothProperConnectedGlobalFunctions` for smooth
  proper morphisms with geometrically connected fibres. This is
  `Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions` (module
  `Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof`).

The quasi-separatedness instance in the target is not used, because `dualSchemeMap_add` holds
over every base.

The general-base argument `dualSchemeMap_add` is the work of Worker 270 (task
b71714f0-c50a-4258-94ac-e065ce455f61). This module only specializes it to the target.
