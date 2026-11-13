# Proof: representability of the Picard class sheaf from noetherian affine tests

Proof module for
`Langlands.AlgebraicGeometry.Picard.NoetherianAffineTestsPicardExtensionStatement`.

## Theorem

`noetherianAffineTestsPicardExtension : NoetherianAffineTestsPicardExtensionStatement.{u}`,
for arbitrary universe `u`.

## Proof as implemented

The proof introduces the noetherian ring `R`, the morphism `f : X ⟶ Spec R` with
its hypotheses (proper, flat, geometrically integral), the section `ε` with
`ε ≫ f = 𝟙`, the object `P` with `P.hom` locally of finite presentation, and the
natural isomorphism `α` on noetherian affine tests. It then applies
`NoetherianAffineTests.nonempty_representableBy_of_noetherianAffine f ε hε α`
from the helper module `NoetherianAffineTestsPicardExtension`, whose
instance arguments (`IsNoetherianRing R`, `IsProper f`, `Flat f`,
`GeometricallyIntegral f`, `LocallyOfFinitePresentation P.hom`) are found from
the introduced hypotheses.

That theorem, documented in `NoetherianAffineTestsPicardExtension.md`, proceeds
as follows:

1. `P.left` is locally noetherian, being locally of finite type over the
   noetherian scheme `Spec R`.
2. A universal element `ξ ∈ F(P)` of the class sheaf `F` is glued from the
   sections `α(W ↪ P)` over the affine opens `W` of `P.left`, which are noetherian
   affine tests (`NoetherianAffineTestsUniversalElement.exists_universal_map`).
   It satisfies `F.map g.op ξ = α(g)` for every noetherian affine test `T` and
   every `g : T ⟶ P`, so `g ↦ F.map g.op ξ` is bijective on noetherian affine
   tests.
3. This bijectivity extends to every test `T` with affine underlying scheme
   (`NoetherianAffineTests.bijective_of_isAffine`). Write `T ≅ Spec A` over
   `Spec R`; `Spec A` is the directed limit of `Spec B` over the finitely
   generated `R`-subalgebras `B ⊆ A`, each noetherian. Morphisms `Spec A ⟶ P`
   factor through some `Spec B` (`P` locally of finite presentation; Library
   `exists_affinePoint_subalgebra`). Line bundles on `X ×_R Spec A`, and
   isomorphisms between pullbacks of line bundles, descend to some `Spec B`
   (Library `NoetherianApproximation.lineBundleSubalgebraDescent` and
   `NoetherianApproximation.lineBundleIsoSubalgebraDescent`). Sections of `F`
   over any test are classes of rigidified line bundles, with equal classes only
   for isomorphic bundles (Library
   `RigidifiedLineBundle.properFlatIntegralClassIso`, which uses the section and
   the hypotheses on `f`). Surjectivity and injectivity over `Spec A` then follow
   from those over the noetherian stages.
4. A section of an fppf sheaf that gives a bijection on all affine tests
   represents the sheaf (`NoetherianAffineTestsUniversalElement.representableByOfBijectiveAffine`,
   via the Library lemma `LineHom.isIso_of_bijective_affine`).

## Dependencies

The proof imports only the statement module and the helper modules
`NoetherianAffineTestsPicardExtension` and `NoetherianAffineTestsUniversalElement`,
which in turn use published Library results. It does not use
`NormalFiniteTypeAbelianPicardSheafAFSchemeStatement`,
`FiniteTypeAbelianPicardSheafSchemeStatement`, or the abelian-scheme
representability statements, nor anything depending on them.
