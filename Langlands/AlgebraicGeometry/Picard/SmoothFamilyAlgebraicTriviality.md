# Algebraic triviality via actual smooth families

This module defines an explicit smooth-family predicate for actual line bundles
on abelian schemes and descends its geometric-fibre version to the existing
rigidified classes. All schemes and fields use the existing universe `u`.
Its only proofs are the two projection formulas, invariance under actual
isomorphisms, and the equivalence with the predicate on a representative.

## Smooth parameters and the field predicate

For `K : Type u` with `Field K` and `IsAlgClosed K`, and an existing
`A : AbelianScheme (Spec (CommRingCat.of K))`,
`IsAlgebraicallyTrivialViaSmoothFamily A L` asserts the existence of:

- An actual `C : Over (Spec (CommRingCat.of K))` with `Smooth C.hom`,
  `IsSeparated C.hom`, `LocallyOfFiniteType C.hom`, `QuasiCompact C.hom`,
  and `GeometricallyIntegral C.hom`.
- Two actual slice morphisms `c0,c1 : Over.mk (𝟙 (Spec K)) ⟶ C`.
- An actual `N : LineBundle (C ×_K A)` with isomorphisms from its
  restrictions at `c0` and `c1` to `LineBundle.trivial A.X.left` and `L`,
  respectively.

Here `LocallyOfFiniteType` together with `QuasiCompact` expresses finite type.
The explicit geometric integrality condition is Mathlib's predicate on the
structure morphism: its pullback along every field-valued point has integral
total space. Thus the parameter satisfies the source's variety convention,
including separatedness, finite type, and geometric integrality. No dimension
is specified, and the two rational points need not be distinct.
`LineBundle` is the existing category of locally free rank-one module sheaves.
The endpoint isomorphisms are `Nonempty` of actual categorical isomorphisms.
No chosen coherent isomorphisms are included.

The total space of the family is the actual scheme pullback
`(relativeSpace A.X.hom).obj C = pullback C.hom A.X.hom`, with the parameter
first. For a section `c`, `smoothFamilyPointMap A C c` is the universal
pullback map
`pullback.lift (A.X.hom ≫ c.left) (𝟙 A.X.left) ...`.
The section equation `c.left ≫ C.hom = 𝟙 (Spec K)` supplies its compatibility.
The projection lemmas identify its first composite with `A.X.hom ≫ c.left`
and its second with `𝟙 A.X.left`. This is the map `a ↦ (c,a)`.
The helper is defined over any base `S`; its construction itself needs no
smoothness hypothesis. Restrictions in the predicate use the actual functor
`LineBundle.pullback (smoothFamilyPointMap A C c)`.

`isAlgebraicallyTrivialViaSmoothFamily_of_iso` retains `C,c0,c1,N` and all
geometric conditions. It composes the second restriction isomorphism with
the supplied `e : L ≅ M`. Applying this construction to `e` and `e.symm`
gives `isAlgebraicallyTrivialViaSmoothFamily_iff_of_iso`.

## Geometric fibres and rigidified families

For arbitrary `S : Scheme.{u}`, `A : AbelianScheme S` and an actual bundle
`L` on `A.X.left`, `IsFibrewiseAlgebraicallyTrivialViaSmoothFamily A L`
quantifies over every algebraically closed field `K : Type u` and every
scheme morphism `s : Spec K ⟶ S`. It applies the field predicate above to
`(baseChange s).obj A` and the existing `fibreLineBundle A L s`.
The latter is the actual pullback of `L` along
`pullback.fst A.X.hom s : A ×_S Spec K ⟶ A`.
Its target is the existing abelian-scheme base change, whose total space
has order `A ×_S Spec K` and whose structure map is the second projection.
The witness family is allowed to depend on `K` and `s`.

The fibrewise isomorphism-invariance lemmas pull an actual isomorphism
`L ≅ M` back along this first projection and apply field invariance.
There is no additional geometric hypothesis on `S`.

For `T : Over S` and `L : RigidifiedFamily A T`,
`IsAlgebraicallyTrivialFamilyViaSmoothFamily A L` is exactly the fibrewise
predicate on `(baseChange T.hom).obj A` and `familyLineBundle A L`.
The existing rigidified relative category uses `T ×_S A`.
`familyLineBundle` forgets the rigidification and pulls back along
`(relativeSpaceSymmetry A.X.hom T).inv : A ×_S T ⟶ T ×_S A`,
so that its output lives on the existing base change `A_T`.
Thus the geometric points tested for this family are all maps
`Spec K ⟶ T.left`, and its fibre restrictions use the first projection
from the actual further base change of `A_T`.

The rigidified isomorphism-invariance lemma maps the given isomorphism
through `RigidifiedLineBundle.forget` and the same symmetry pullback, then
uses fibrewise invariance. `IsAlgebraicallyTrivialClassViaSmoothFamily`
uses `Quotient.lift` on the existing `RigidifiedClasses A T`, whose relation
is nonempty actual rigidified isomorphism. `propext` converts invariance
into the equality of propositions required for this descent.
`isAlgebraicallyTrivialClassViaSmoothFamily_classOf`, proved by `Iff.rfl`,
is the equivalence with the condition on any actual representative.
`AlgebraicallyTrivialClassesViaSmoothFamily A T` is the resulting subtype
of the existing rigidified classes.

## Provenance and comparisons still required

The governing registered original is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary version of the first chapters,
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The retained file is
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
Notation (0.4), printed p.1/PDF p.5, supplies the variety convention and
the locally free rank-one interpretation of line bundles.
Remark (6.9), printed p.91/PDF p.95, defines divisor algebraic equivalence
using a smooth parameter variety and flat codimension-one families on
`X ×_k T`, then describes the line-bundle interpretation in terms of
connected components of the Picard scheme.
Section (7.24), printed p.107/PDF p.111, formulates algebraic equivalence
of line bundles using the Néron–Severi group and explains its relation
over an algebraic closure to Remark (6.9).

The explicit line-bundle-family predicate here is derived infrastructure
motivated by those passages. It uses the source's smooth parameter
convention, with the parameter first in the product; the canonical
symmetry accounts for the source's order `X ×_k T`.
No formal equivalence with the divisor formulation or the
identity-component/Néron–Severi formulation is proved or assumed.
Likewise, the comparison with the existing geometric translation-invariance
predicate remains a separate theorem. Corollary (7.22), printed
p.106/PDF p.110, motivates that comparison but supplies no imported Lean proof.

The relative motivation is Kai-Wen Lan, *Arithmetic compactifications of
PEL-type Shimura varieties*, thesis revision March 14, 2021,
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`,
Definition 1.3.2.1 and Lemma 1.3.2.2, printed pp.73–74/PDF pp.101–102.
Lan uses `A ×_S T`, rigidification along the induced identity section,
and algebraic equivalence on every ordinary fibre `t ∈ T`.
The geometric-fibre smooth-family predicate defined here is not asserted
to agree already with that ordinary-fibre condition.
The author's errata, `lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
PDF pp.1 and 8–9, were read: schemes use the quasi-separated convention,
and the quotient in Definition 1.3.2.1 uses bundles on `T`.
This module forms neither that ordinary Picard quotient nor an fppf sheaf.
No source-specific errata note was present in the checked project,
workspace or Library `notes/errata/` locations.

Only the elementary constructions and proofs described above are included.
Preservation under arbitrary relative pullback, normalization of
rigidifications, comparisons of algebraic equivalence definitions,
comparison with translation invariance, geometric detection or openness,
group laws, and representability remain separate obligations.
