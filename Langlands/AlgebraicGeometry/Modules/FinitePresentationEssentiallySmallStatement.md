# Essential smallness of locally finitely presented module sheaves

Module: `Langlands.AlgebraicGeometry.Modules.FinitePresentationEssentiallySmallStatement`.

Author: Worker 3694, for task `5b9ad399-34f2-4314-bb39-902f491aad01`.

This module states a proposition and proves nothing.

## Statement

`FinitePresentationEssentiallySmallStatement.{u}` says: for every scheme
`Y : Scheme.{u}`,

```text
ObjectProperty.EssentiallySmall.{u} (SheafOfModules.isFinitePresentation.{u} Y.ringCatSheaf).
```

Here `Y.Modules` is Mathlib's category `SheafOfModules Y.ringCatSheaf` of sheaves
of modules over the structure sheaf, with values in `ModuleCat.{u}`. The property
`SheafOfModules.isFinitePresentation` holds for a module sheaf that is locally
finitely presented. On the members of some covering family of opens it is the
cokernel of a map between finite free module sheaves. Mathlib's
`ObjectProperty.EssentiallySmall.{u} P` means: some property `Q` with
`Small.{u} (Subtype Q)` satisfies `P ≤ Q.isoClosure`. Since local finite
presentation is invariant under isomorphism, Mathlib's
`ObjectProperty.EssentiallySmall.exists_eq_isoClosure_ofObj` makes this
equivalent to the following: there are a type
`ι : Type u` and module sheaves `N : ι → Y.Modules` such that the locally finitely
presented module sheaves on `Y` are exactly those isomorphic to some `N i`.

The isomorphism classes of objects of `Y.Modules` do not form a `u`-small
collection in general; finite presentation is essential.

## Source and derivation

This is a set-theoretic input, not a theorem stated in this form in the cited
source. The registered original `stacks-artin-axioms-approximation-2026-11-06`
(folder SHA-256
`f2f078895a7155a2277c0db49c51f80b73993f0439ffc51c35eb54e9b6e0990b`), file
`artin.pdf`, Chapter 98 (Artin's Axioms), Section 98.14, lists axiom [-1], a
set-theoretic condition. Footnote 2 on printed page 24 spells it out. Over the
finite type fields `k` over `S`, the supremum of the cardinalities of
`Ob(𝒳_{Spec k})/≅` and of `Arrows(𝒳_{Spec k})` is at most the size of some
object of `(Sch/S)_fppf`. Lemma 98.17.1 (Tag 07Y4, printed page 27) uses it in
footnote 7 to bound the index set of the coproduct atlas. The registered
original `stacks-coherent-sheaf-stack-08ka-2026-11-01` (folder SHA-256
`4ac7cc2a6a797cd51c3a793bbf7684229a8f43b69031e852a0681c219ab99078`), file
`08KA.html`, proves Theorem 99.5.12 through Lemma 98.17.1 and states: "We omit
the verification of [-1]".

For the stack of coherent sheaves of a proper scheme `X` over a field, the
objects over `Spec K` are flat finitely presented module sheaves on `X_K`. The
proposition above, applied to `Y = X_K`, gives a `u`-small set of
representatives of their isomorphism classes. The proposition is stated for all
schemes in the universe, without restricting to these fibres, and only for
objects; the bound on arrows is not needed by the Library's atlas assembly.
Universe smallness in Lean replaces the cardinal bound of the source.
