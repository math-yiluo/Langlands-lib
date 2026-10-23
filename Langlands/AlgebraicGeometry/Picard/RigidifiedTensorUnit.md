# Unit isomorphisms for rigidified line-bundle tensor

This module lifts the actual explicit left and right sheaf tensor unitors to
rigidified line bundles along an arbitrary scheme morphism `ε : S ⟶ X`.
It proves both unit laws for the resulting operation on relative isomorphism
classes. All objects use the existing sheafified tensor construction.

## Assumptions

The rigidified constructions take two explicit published propositions:

- `pullbackTensorComparisonIsIsoStatement`, used to construct the tensor
  rigidification and prove local rank-one closure;
- `PullbackTensorUnitCoherenceStatement`, whose two equations assert that
  the fixed pullback tensor and structure-sheaf comparisons respect the
  explicit left and right sheaf unitors.

The module does not prove either proposition or replace the specified maps
by freely chosen comparisons. No geometric restriction on the schemes or
morphism is assumed. The unit is `RigidifiedLineBundle.trivial ε`, the
structure sheaf of `X` with rigidification `(pullbackUnitIso ε).symm`.

## Implemented proofs

Three preliminary lemmas in `Langlands.Scheme.Modules` are unconditional.
`tensorLeftUnitor_naturality` and `tensorRightUnitor_naturality` prove
naturality of the explicit sheaf unitors: first use functoriality of
sheafification and the presheaf unitor naturality equation, then use
naturality of the sheafification counit. `tensorUnitors_equal` proves that
their homomorphisms agree on the structure sheaf by sheafifying the
presheaf equality `MonoidalCategory.unitors_equal` and postcomposing
with the same counit.

`RigidifiedLineBundle.tensorLeftUnitor_compatibility` replaces pullback of
the left unitor using the first coherence equation. Composing the tensor
rigidification with the canonical pullback comparison reduces it to the
inverse unit followed by the tensor of the two input rigidifications.
Tensor functoriality combines this with the pullback-unit comparison;
its inverse cancels the trivial bundle's rigidification. Naturality of
the sheaf left unitor and the inverse-hom identity finish the proof.
`tensorLeftUnitIso` packages that actual module unitor with this equation
as an isomorphism of rigidified line bundles.

`tensorRightUnitor_compatibility` follows the same calculation with the
second coherence equation and right unitor naturality. The tensor
rigidification was defined using the left unitor on the structure sheaf,
so the final cancellation also uses `tensorUnitors_equal`.
`tensorRightUnitIso` packages the resulting compatible right unitor.

For `f : X ⟶ S`, a section `ε` with `ε ≫ f = 𝟙 S`, and any `T : Over S`,
`classesTensor_left_unit` and `classesTensor_right_unit` prove that the
class of the canonically rigidified structure sheaf on `X ×_S T` is a
left and right unit for `classesTensor`. Each proof uses quotient
induction, then the corresponding compatible unitor isomorphism.

## Provenance and scope

This is a derived unit-law construction for the rigidified tensor formula
in Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary
draft, Chapter VI (6.2), printed p.88 (PDF p.92). The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The argument is the categorical calculation above, implemented with the
published explicit comparisons and Mathlib's presheaf monoidal laws.
It needs none of the extra geometric hypotheses in EGM's condition (*).

The module proves unit isomorphisms and unit equations only. Associativity,
commutativity, inverses, compatibility with relative pullback and the full
abelian-group-valued presheaf remain separate obligations.
