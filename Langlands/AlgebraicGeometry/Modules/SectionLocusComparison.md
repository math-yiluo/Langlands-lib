# Stalk and maximality comparisons for the section trivialization locus

Author: Worker 223.

The closing theorem `Langlands.SchemeModule.sectionLocusComparison` proves
exactly the published proposition `SectionLocusComparison.{u}` of
`Langlands.AlgebraicGeometry.Modules.SectionLocusStatements`. It holds for
every scheme `X`, every actual sheaf of modules `M : X.Modules` and every
global section `s`. No local-freeness, finiteness or quasi-coherence
assumption is used. Write `φ = sectionHom M s : 𝒪_X ⟶ M` for the morphism
sending one to `s`. The three conjuncts are the theorems
`localStalkCriterion`, `trivializationOpenInterior` and
`maximalTrivialization`.

## Helper lemmas

`isIso_iff_stalk_isIso` states that a morphism `φ : N ⟶ P` of `X.Modules` is
an isomorphism iff every stalk map of its underlying morphism of abelian
presheaves, `(stalkFunctor Ab x).map ((Scheme.Modules.toPresheaf X).map φ)`,
is an isomorphism. The proof packages the underlying presheaves as abelian
sheaves using `Scheme.Modules.isSheaf`, and the presheaf morphism as a sheaf
morphism `ψ`. The forgetful functor `TopCat.Sheaf.forget Ab X` is fully
faithful and `Scheme.Modules.toPresheaf X` reflects isomorphisms (a Mathlib
instance), so `ψ` is an isomorphism iff `φ` is. Mathlib's
`TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso` then compares `ψ` with its
stalk maps.

`isIso_stalk_restrict_iff` states that for an open `U` and a point `y` of the
open subscheme `U`, the stalk map at `y` of the restricted morphism
`(Scheme.Modules.restrictFunctor U.ι).map φ` is an isomorphism iff the stalk
map of `φ` at `U.ι y` is. It is `NatIso.isIso_map_iff` applied to Mathlib's
natural isomorphism `Scheme.Modules.restrictStalkNatIso U.ι y` between the
functors `restrictFunctor U.ι ⋙ toPresheaf U ⋙ stalkFunctor Ab y` and
`toPresheaf X ⋙ stalkFunctor Ab (U.ι y)`.

## (1) Local stalk criterion

`localStalkCriterion` proves `LocalStalkCriterion.{u}`:
`TrivializesOn M s U ↔ ∀ x ∈ U, IsStalkFrame M s x`. By definition
`TrivializesOn M s U` is `IsIso ((restrictFunctor U.ι).map φ)`. Applying
`isIso_iff_stalk_isIso` on the scheme `U` and then `isIso_stalk_restrict_iff`
at every point turns it into: for every point `y` of `U`, the stalk map of
`φ` at `U.ι y` is an isomorphism. That map is `IsStalkFrame M s (U.ι y)`.
Since `U.ι y` is definitionally the underlying point `y.1 ∈ U`, this is the
right-hand side.

## (3) Maximality

`isStalkFrame_of_mem_trivializationOpen` shows that every point of
`trivializationOpen M s` is a stalk frame. The trivialization open is the
supremum `sSup {U | TrivializesOn M s U}` in the complete lattice of opens.
`Opens.mem_sSup` gives an open `V` with `TrivializesOn M s V` containing the
point, and the forward direction of (1) on `V` concludes.

`maximalTrivialization` proves `MaximalTrivialization.{u}`:
`TrivializesOn M s U ↔ U ≤ trivializationOpen M s`. The forward direction is
`le_sSup`. Conversely, if `U` lies in the trivialization open, every point of
`U` is a stalk frame by the previous lemma, so the backward direction of (1)
shows that `s` trivializes on `U`.

## (2) Interior of the stalk-frame locus

`trivializationOpenInterior` proves `TrivializationOpenInterior.{u}`: the
underlying set of `trivializationOpen M s` equals
`interior {x | IsStalkFrame M s x}`. The proof is by antisymmetry of sets.

- The trivialization open is open and contained in the stalk-frame set by
  `isStalkFrame_of_mem_trivializationOpen`, so `interior_maximal` places it
  in the interior.
- The interior is an open `W`. Each of its points is a stalk frame by
  `interior_subset`, so `s` trivializes on `W` by (1). Maximality (3) then
  gives `W ≤ trivializationOpen M s`.

## Closing theorem

`sectionLocusComparison` is the triple
`⟨localStalkCriterion, trivializationOpenInterior, maximalTrivialization⟩`,
in the order of the conjunction `SectionLocusComparison.{u}`.
