# An initial Picard source stage over a finite-type integer algebra

This internal assembly reuses the published `FiniteBasisPicardFamily` and
`ArtinianPolynomialPresentation` constructions. It introduces no new literature
input. All rings, schemes, line bundles and the source retain the arbitrary
common universe `u`.

The inputs are a commutative ring `k` of finite type over the integers, a field
`K` with its original finite-type `k`-algebra structure, a proper morphism
`f : X → Spec k`, and an actual line bundle `M` on the relative residue scheme.
No domain, reducedness, separability, projectivity or smoothness assumption is
added. Flatness is unnecessary for this initial stage.

`residueModuleFinite` applies the published
`NoetherianApproximation.isJacobsonRing_int`, preservation of the Jacobson
property under finite-type algebras, and Mathlib's Jacobson-ring Zariski lemma.
It proves that `K` is finite as a module over the original ring `k`. Finite type
over the integers also makes `k` Noetherian.

`sourceRing` is exactly the complete local polynomial source already chosen by
`ArtinianPolynomialPresentation` for `FiniteBasisPicardFamily.test f M`. The
latter is the split square-zero test `K ⊕ K^Index` for a finite basis of actual
pointed dual-number Picard classes. The presentation covers the entire test
algebra. Its localization and completion retain the original `k`-algebra
structure. The published source construction supplies the Noetherian, local
and maximal-ideal adic completeness instances. `augmentation` is its specified
residue map, and `augmentation_surjective` retains its surjectivity.

`stage` packages the unchanged test, the existing surjective source cover,
its exact augmentation equation, and the existing pointed basis family as an
`ArtinianPicardSourceStep.Stage`. The residue identification is part of that
actual pointed family. No new choice of line-bundle representative is made.

`postcomp_surjective` specializes the established completed-polynomial-source
mapping theorem to this same source. Every compatible scalar-preserving map to
an actual Artinian test lifts across every surjective augmented test arrow.
It retains the whole original map, rather than only its residue values.

This unit constructs the source and initial stage required by the Picard
source tower. The tangent-basis restriction theorem remains the published
`FiniteBasisPicardFamily.existsUnique_parameter`. Conversion to the full
specified-isomorphism point-fibre lifting predicate, and formal versality of
an effective bundle, are separate obligations.
