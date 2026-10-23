# Dual maps preserve the constructed tensor multiplication

For an actual abelian-scheme homomorphism `f : A → B` over any scheme `S`,
this module proves that pullback along `f` preserves the constructed tensor on
rigidified families and their classes. With chosen dual parameter schemes, it
then proves that the already constructed dual scheme map preserves their
actual multiplication morphisms. All schemes have universe `u`.

## Rigidified families and classes

The construction retains three explicit propositions about the fixed maps:
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`, and
`PullbackTensorLeftUnitorStatement`.

For every test scheme `T : Over S`, the existing `homFamilyPullback f T`
is the actual rigidified pullback along `T ×_S A → T ×_S B`, with the identity
on `T` and the square of unit sections. `homFamilyPullbackTensorIso`
specializes the proved `RigidifiedLineBundle.pullbackTensorIso` to exactly this
square. Its source is pullback of the constructed rigidified tensor; its target
is tensor of the two pulled-back families. Its underlying morphism is therefore
the fixed canonical tensor comparison, with its rigidification compatibility
already proved.

`homClassesPullback_tensor` descends that compatible isomorphism to equality
on relative classes. It uses induction on both quotient representatives and
quotient soundness. The quotient is by actual isomorphism compatible with
rigidification, so the underlying unrigidified comparison alone would not
suffice.

For Picard-zero classes, the additional hypothesis
`HomPicardZeroPullbackStatement` is retained. This states that the actual
homomorphism pullback preserves the chosen geometric-fibre condition.
`homPicardZeroClassesPullback_tensor` applies subtype extensionality and the
class equation above. No new geometric preservation claim is assumed
implicitly or proved here.

## Action on dual points and multiplication

Let `hA : HasDualScheme A` and `hB : HasDualScheme B` be proofs of existence of
actual universal Picard-zero families. To use the existing point-class maps,
the module additionally takes `PicardZeroPullbackStatement`, preservation under
pullback in the test scheme.

For every `p : T → dualScheme B hB`, `dualPointClass_dualSchemeMap` identifies
the class of `p ≫ dualSchemeMap f` with the homomorphism pullback of the class
of `p`. The proof specializes the published universal action
`dualSchemeMap_classifies`, uses the inverse classification identity, and
applies `dualPointClass`. It supplies the already proved
`RigidifiedModule.pullbackCoherence` to the universal action. This point-action
lemma needs the two geometric preservation hypotheses and the dual existence
proofs; it does not need tensor-comparison hypotheses.

Finally, `dualSchemeMap_tensor` states the following equality of morphisms
from `dualScheme B hB ×_S dualScheme B hB` to `dualScheme A hA`. Writing `d`
for the constructed dual map and `μ_A, μ_B` for `dualTensor`, it says

`μ_B ≫ d = prod.lift (prod.fst ≫ d) (prod.snd ≫ d) ≫ μ_A`.

The right-hand pairing is the product of `d` with itself. Injectivity of the
actual classification map reduces the equation to equality of Picard-zero
classes. The point-action formula, the defining tensor multiplication
specification, and preservation of tensor by homomorphism pullback prove the
result. The equation retains all three canonical tensor-comparison premises,
the two geometric preservation premises, and both dual existence proofs.

## Provenance and scope

This is derived infrastructure for the dual homomorphism construction.
Edixhoven–van der Geer–Moonen, *Abelian Varieties*, Chapter VI paragraph (6.2),
printed p.88 (PDF p.92), specifies compatible rigidified classes, tensor,
pullback and universal classification. Definition (6.19), printed p.96
(PDF p.100), characterizes the dual map by the compatible pullback of the
Poincare bundle. The present proof verifies multiplication preservation for
the Library's map constructed by that characterization.

The source's Remark (6.20) on the same page distinguishes this fact from
additivity of the assignment `f ↦ fᵗ`. This module proves preservation of
tensor by each fixed dual map. It does not prove additivity in `f`, and it does
not construct the rational extension on `Hom⁰`.

The chosen dual schemes have the previously constructed multiplication, but
associativity, inverses, and their abelian-scheme geometry remain separate
obligations. Consequently this module does not yet package the dual map as an
abelian-scheme homomorphism. All unproved canonical comparison and geometric
preservation propositions remain explicit; no arbitrary-base existence result
or extra field, projectivity, or noetherian hypothesis is asserted.
