# Renard I.5.3: free quotients and projective direct summands

Authors: Worker 6 (shared draft revision 1: statement design, Lean and
documentation), Worker 734 (source and errata checks, compilation,
documentation revision and submission).

This statement unit formalizes the two positive assertions in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, I.5.3, printed p.27 / PDF p.33. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source defines a free module as an object of M(A) isomorphic to a direct
sum of modules isomorphic to A. It proves that every module in M(A) is a
quotient of a free module. It then states, citing the unital argument of
Lang's *Algebra* (its reference [36]), that every projective module is a
direct summand of a free module.

The projectivity convention is Renard A.VIII.2, printed p.267 / PDF p.273:
an object X is projective when Hom(X, •) to ℤ-modules is exact. Exactness of
a functor is defined in A.VIII.1, printed p.266 / PDF p.272. The 2010-edition
errata `renard-2010-corrections-complements` (SHA-256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`) were
searched for free modules, direct summands and projectives. They contain no
entry for this passage.

The declarations are proposition definitions. This file contains no proof of
either assertion.

## Declarations

The module is `Langlands.Algebra.NonUnitalModuleFreeStatements`, and all
declarations are in the namespace of the same name. Each has the universe
parameters `uA uM`:

- `FreeQuotientStatement : Prop`
- `ProjectiveFreeSummandStatement : Prop`
- `FreeModuleAssertions : Prop`, defined as
  `FreeQuotientStatement.{uA, uM} ∧ ProjectiveFreeSummandStatement.{uA, uM}`.

The imports are the published `Langlands.Algebra.NonUnitalModuleFree`
(the free object), `Langlands.Algebra.NondegenerateModuleAbelianProof`
(the abelian structure) and
`Langlands.CategoryTheory.Renard.HomObjectProperties` (`HomProjective`).

## Original modules, actions and universes

The coefficient ring `A : Type uA` is an arbitrary nonunital ring satisfying
`IsIdempotented A`. Each module keeps its original additive group and action
in `NondegenerateModuleCat`. The source assumes a complex algebra with
idempotents. This unit extends both assertions to arbitrary idempotented
nonunital rings. The assertions use only finite local units, additive original
actions and categorical splitting, so they need no complex coefficients.

Both the module carrier and the free index type live in `Type (max uA uM)`.
The coefficient and module universe parameters stay independent; the unequal
pairs `(0, 1)` and `(1, 0)` are checked in the file. The free source is exactly
`NonUnitalModuleFree.object.{uA,uM,max uA uM} hA I`. Its carrier is the actual
finite-support sum of copies of `ULift.{uM} A`, with original left multiplication
on each copy. The lift only places the coefficient carrier in the common
universe. The published intertwiners `NonUnitalModuleFree.regularDown` and
`regularUp` identify each lifted copy with the original regular module
`NonUnitalModule.regular A`.

## Quotients of actual free sums

`FreeQuotientStatement` quantifies over every actual nondegenerate module `M`
and asks for an index type `I` and an original categorical intertwiner
`q : object hA I ⟶ M`. It requires both categorical `Epi q` and ordinary
surjectivity of the original additive map `q.hom`. So the quotient condition
holds on the original carrier as well as in the category.

This is the source's quotient assertion over the constructed regular sum. The
statement does not prescribe an index set or a map formula. In the source
proof, the index set consists of the vectors of `M`; the map from each regular
copy is the original orbit map `a ↦ a • m`.

## Projectives as actual biproduct summands

`ProjectiveFreeSummandStatement` installs exactly
`NondegenerateModuleCat.abelian A hA`, whose inherited Hom groups are those of
the original full subcategory. Its only hypothesis on the object `P` is
`Langlands.Renard.HomProjective P`: exactness of the actual
integer-module-valued covariant Hom functor, as in Renard A.VIII.2.

The conclusion supplies `I`, an actual nondegenerate module `Q`, and an actual
categorical isomorphism
`NonUnitalModuleFree.object hA I ≅ P ⊞ Q`. The biproduct and its maps are those
of this abelian category. An isomorphism is a pair of mutually inverse original
intertwiners, so this conclusion expresses a genuine direct summand.

## Scope

`FreeModuleAssertions` is the conjunction of these two closed targets. It does
not assert that the regular module or arbitrary free modules are projective.
It also asserts no converse from being a summand of a free module to
projectivity. The source warns that these implications can fail for algebras
with idempotents. That warning remains a separate obligation.

## Provenance

The two statements follow the source assertions directly. The only additions
are the extension from complex algebras to arbitrary idempotented nonunital
rings and the explicit universe placement described above.
