# Limits of dual diagrams from the Frobenius chain

Worker 151. Module `Langlands.Representation.Category.FrobeniusChainLimits`,
namespace `Langlands.SmoothRep`.

## Provenance and scope

This is an internal consequence of the adjunction constructed in
`FrobeniusChainAdjunction`. That construction packages Renard 2026, VI.9.6,
the Hom-chain (VI.9.6.3), printed p.202 / PDF p.208. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The limit-preservation consequence here is internal and is not asserted as a
separate result of the source.

Let `L` go from smooth complex representations of `M` to those of `G`, and let
`r` and `R` go in the other direction. The groups and representation carriers
have independent universes. Write `D_G` and `D_M` for their smooth
contragredient functors. The hypotheses are precisely:

- an adjunction `F : r ⊣ L`;
- a natural isomorphism `C : L.op ⋙ D_G ≅ D_M ⋙ L`;
- a natural isomorphism `Ψ : D_G ⋙ R ≅ r.op ⋙ D_M`.

No exactness or admissibility hypothesis is used.

## Declarations and implemented proof

`frobeniusChainDualLimit F C Ψ hc` supplies a limit cone as follows. For any
diagram `K : J ⥤ SmoothRep ℂ G` and colimit cocone `c` with proof
`hc : IsColimit c`, take its opposite cone, apply `D_G`, and then apply `R`.
The resulting cone over `K.op ⋙ D_G ⋙ R` is limiting. Indeed, `c.op` is a
limit cone, and `D_G ⋙ R` is a right adjoint by
`frobeniusChainAdjunction F C Ψ`. Mathlib's theorem that right adjoints
preserve limits supplies the proof.

`preservesLimit_contragredient_of_frobeniusChain F C Ψ K` states
`PreservesLimit (K ⋙ D_G) R` for a diagram
`K : J ⥤ (SmoothRep ℂ G)ᵒᵖ` with a supplied instance `HasLimit K`.
Both `D_G` and `D_G ⋙ R` preserve the limit of `K`, because both are right
adjoints. Thus the image under `D_G` of a chosen limit cone is a limit cone
whose image under `R` is limiting. Preservation of this one limiting cone
implies preservation of every limit cone over `K ⋙ D_G`.

For a discrete diagram, this proves preservation of the product of its smooth
contragredients whenever the corresponding coproduct exists in the original
category. The Library's `SmoothCoproducts` supplies concrete direct sums when
the carrier universe contains the index universe. The present result needs
no chosen product construction and makes no assertion about products whose
index universe exceeds the available carrier universe.

## Remaining obligations

This result alone proves neither preservation of arbitrary products by `R`
nor the adjunction `L ⊣ R`. In particular it does not prove the chain-unit
factorization of `ChainUnitAdjunction`, identify a possible left adjoint of
`R` with `L`, or discharge the unconditional pointwise VI.9.6 equivalence.
