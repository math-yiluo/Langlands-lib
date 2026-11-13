# Proof: Renard III.3.1 canonical compact-section coinvariant comparison

`Langlands.Sheaf.Renard.CoinvariantStatements.compactComparisonStatement` proves the
published closed proposition
`Langlands.Sheaf.Renard.CoinvariantStatements.CompactComparisonStatement`.

## Statement proved

For every topological group `G : Type` with `IsLocallyProfinite G`, spaces
`X Y : Type` with `IsLocallyProfinite X` and `IsLocallyProfinite Y`, a jointly
continuous action of `G` on `X`, a continuous `q : C(X, Y)` with
`q (g • x) = q x`, and every action sheaf `F : ActionSheaf G X`, the component
`(CoinvariantSheaf.compactComparison hX q hq hY).app F` is an isomorphism in
`NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier Y)`. The theorem
keeps all of these binders unchanged and adds no smoothness, properness,
surjectivity or other premise.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`),
III.3.1, the paragraph after the Definition, printed p.83 / PDF p.89:
`F′` is the sheaf on `Y` corresponding to the `D(Y)`-module `F_c(X)_G` under the
equivalence of categories of Theorem II.2.5, and "par définition" `F_c(X)_G` and
`F′_c(Y)` are isomorphic as `D(Y)`-modules. The source relies on II.2.5 (end of
the proof of the Theorem, printed p.40 / PDF p.46), which identifies the compact
sections of the sheaf attached to a nondegenerate module `M` with `M`. The Lean
target asks for this isomorphism to be the canonical comparison map.

## Implemented proof

The proof is a definitional reduction to the published II.2.5 result
`Langlands.Sheaf.Renard.ModuleProjectorComparison.moduleComparisonIsIso`
(module `Langlands.Sheaf.Renard.ModuleProjectorComparisonProof`), which proves
`ModuleComparisonIsIso`: for every locally profinite `X : Type` and every
nondegenerate test module `M`, `ModuleProjectorComparison.moduleComparison hX M`
is an isomorphism.

In `Langlands.Sheaf.Renard.CoinvariantSheaf`, the comparison
`compactComparison hX q hq hY` is defined as
`Functor.whiskerLeft (modules hX q hq hY) (ModuleProjectorComparison.moduleComparisonNat hY)`,
and the component of `moduleComparisonNat hY` at `M` is
`moduleComparison hY M`. Therefore
`(compactComparison hX q hq hY).app F` is definitionally
`moduleComparison hY ((modules hX q hq hY).obj F)`, where
`(modules hX q hq hY).obj F` is the actual coinvariant quotient of the
original compact sections of `F`, with its nondegenerate target-test action.

After introducing all binders of `CompactComparisonStatement`, the proof
applies `moduleComparisonIsIso` to the space `Y`, its predicate `hY` and this
module. Lean accepts this term as a proof of the `IsIso` goal by unfolding
`whiskerLeft` and `moduleComparisonNat`; no inverse, comparison certificate or
equivalence is assumed. The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`.
