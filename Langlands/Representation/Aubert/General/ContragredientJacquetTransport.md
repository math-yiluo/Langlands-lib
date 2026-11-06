# Transport of Jacquet–contragredient isomorphisms along Levi identifications

Lean module: `Langlands.Representation.Aubert.General.ContragredientJacquetTransport`,
namespace `Langlands.Aubert.General`.

## Provenance

Internal infrastructure for Renard 2026, VI.9.6 Theorem (VI.9.6.2) (printed p.201, PDF
p.207). The Library states (VI.9.6.2) for represented parabolics
(`RepresentedParabolic.LeviJacquetContragredientStatement`) with Jacquet functors valued in
smooth representations of `M(F)` itself. Those functors are the normalized Jacquet functor to
the literal Levi image in `G(F)`, followed by pullback along a topological-group isomorphism.
A duality constructed for abstract closed subgroups therefore has to be moved across that
pullback. Renard does not state this step, because he identifies `M(F)` with its image. The
module contains only that bookkeeping and no analytic input.

## Contents

`contragredientPullbackNatIso e`, for a topological-group isomorphism `e : H ≃ₜ* G` between
topological groups, is the natural isomorphism

`(pullbackFunctor e).op ⋙ contragredientFunctor ≅ contragredientFunctor ⋙ pullbackFunctor e`

of functors `(SmoothRep ℂ G)ᵒᵖ ⥤ SmoothRep ℂ H`, i.e. `(e^* A)~ ≅ e^*(A~)` naturally in `A`.
Its components are the published `contragredientPullbackIso e A`, which keep each linear
functional (`Aubert/General/ContragredientTransport.lean`). Naturality is the published
`contragredientPullbackIso_natural`. The simp lemma `contragredientPullbackNatIso_hom_app`
records the components.

`contragredientCompPullbackIso J' J e α` takes functors
`J' J : SmoothRep ℂ G ⥤ SmoothRep ℂ M`, an isomorphism `e : H ≃ₜ* M` and a natural isomorphism
`α : contragredientFunctor ⋙ J' ≅ J.op ⋙ contragredientFunctor`. It returns the natural
isomorphism

`contragredientFunctor ⋙ (J' ⋙ pullbackFunctor e) ≅ (J ⋙ pullbackFunctor e).op ⋙ contragredientFunctor`.

It is `α` whiskered on the right by `pullbackFunctor e`, followed by
`contragredientPullbackNatIso e` (inverted and whiskered on the left by `J.op`), up to
associators.

`nonempty_contragredient_normalizedJacquet_pullback_iso` is stated for a locally compact
nonarchimedean group `G` and a topological group `H`. Its data are closed subgroups `U`, `O`
of `G` and two subgroups `M₁`, `M₂` with `hM : M₁ = M₂`. `M₁` normalizes `U` and `M₂`
normalizes `O`. There are isomorphisms `e₁ : H ≃ₜ* M₁` and `e₂ : H ≃ₜ* M₂` with
`(e₁ x : G) = e₂ x` for all `x`. The hypothesis `hiso` says that for every proof that `M₂`
normalizes `U`,

`contragredientFunctor ⋙ normalizedJacquetFunctor U M₂ … ≅ (normalizedJacquetFunctor O M₂ …).op ⋙ contragredientFunctor`

is nonempty, that is `r_U(π~) ≅ (r_O π)~` naturally as smooth representations of `M₂`. The
conclusion is

`Nonempty (contragredientFunctor ⋙ (normalizedJacquetFunctor U M₁ … ⋙ pullbackFunctor e₁) ≅ (normalizedJacquetFunctor O M₂ … ⋙ pullbackFunctor e₂).op ⋙ contragredientFunctor)`,

as functors `(SmoothRep ℂ G)ᵒᵖ ⥤ SmoothRep ℂ H`. The two Levi terms are kept separate
because, for represented parabolics, the Levi image for `P̄` is `pointImage (mbar ≫ pbar)` and
the one for `P` is `pointImage (m ≫ p)`. These are equal but not syntactically the same.

## Proof

Substitute `hM`. Then `e₁ = e₂` by extensionality of continuous multiplicative equivalences
(`ContinuousMulEquiv.ext`, with `Subtype.ext` on the values in `G`). Apply `hiso` to the given
normalizer proof and transport the resulting isomorphism with
`contragredientCompPullbackIso`.
