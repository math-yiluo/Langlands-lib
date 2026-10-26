# Smooth-family algebraic triviality and translation invariance

This module states a derived comparison between the existing explicit
smooth-family predicate and translation invariance for actual line bundles on
abelian schemes. It imports
`Langlands.AlgebraicGeometry.Picard.SmoothFamilyAlgebraicTriviality` and changes
none of the imported definitions. Both declarations are proposition-valued
`def`s. They contain no proofs. All schemes and fields use the same universe `u`.

## The field comparison

`Langlands.AbelianScheme.SmoothFamilyTranslationInvarianceStatement.{u}` asserts
that for every `K : Type u` with `Field K` and `IsAlgClosed K`, every
`A : AbelianScheme (Spec (CommRingCat.of K))`, and every actual
`L : LineBundle A.X.left`,

```text
IsAlgebraicallyTrivialViaSmoothFamily A L
  ↔ Langlands.GroupScheme.IsTranslationInvariant A.toGrp L.
```

The left side is the published existential predicate. Its witness consists of
an actual parameter `C : Over (Spec K)` with smooth, separated, locally
finite-type, quasi-compact, and geometrically integral structure morphism.
Local finite type together with quasi-compactness expresses finite type. Thus
the parameter is a smooth variety in the source's convention. It has two actual
rational points `c0,c1 : Over.mk (𝟙 (Spec K)) ⟶ C`, and an actual line bundle
`N` on the parameter-first product
`(relativeSpace A.X.hom).obj C = C ×_K A`.

The first endpoint is an actual isomorphism from the pullback of `N` along
`smoothFamilyPointMap A C c0` to `LineBundle.trivial A.X.left`. The second is
an actual isomorphism from its pullback along `smoothFamilyPointMap A C c1`
to `L`. Each is expressed by `Nonempty` of the categorical isomorphism type.
The map in both restrictions is `a ↦ (c,a)`, constructed by the actual
pullback universal property. There is no dimension restriction on `C` and the
two points need not be distinct. No divisor or Picard-component symbol replaces
this family or either endpoint condition.

The right side quantifies over every section
`x : Over.mk (𝟙 (Spec K)) ⟶ A.X`. These are exactly the `K`-rational points
of the abelian scheme. For each, it requires an actual isomorphism
`(translation A.toGrp x)^* L ≅ L`, using the existing group law and line-bundle
pullback. On an abelian scheme this is translation by addition. This predicate
tests all sections over the current field; it does not itself quantify over
further base changes or choose a coherent collection of isomorphisms.

## The aggregate and its three lifts

The selected declaration is
`Langlands.AbelianScheme.SmoothFamilyPicardZeroComparisonStatement.{u}`.
It is the conjunction of the field proposition above and these three
equivalences:

1. For every `S : Scheme.{u}`, `A : AbelianScheme S`, and actual
   `L : LineBundle A.X.left`,
   `IsFibrewiseAlgebraicallyTrivialViaSmoothFamily A L ↔
   IsGeometricallyPicardZero A L`.
2. For every such `S,A`, every `T : Over S`, and actual
   `L : RigidifiedFamily A T`,
   `IsAlgebraicallyTrivialFamilyViaSmoothFamily A L ↔
   IsPicardZeroFamily A L`.
3. For every such `S,A,T` and `q : RigidifiedClasses A T`,
   `IsAlgebraicallyTrivialClassViaSmoothFamily A q ↔ IsPicardZeroClass A q`.

For the first lift, both existing predicates quantify over every algebraically
closed `K : Type u` and every map `s : Spec K ⟶ S`. They use the same actual
abelian scheme `(baseChange s).obj A` and the same
`fibreLineBundle A L s`. This bundle is the pullback of `L` along
`pullback.fst A.X.hom s : A ×_S Spec K ⟶ A`. Consequently, once the field
comparison is proved, its application to each such bundle gives the first
lift in both directions.

For the second lift, both predicates apply their respective geometric-fibre
condition to `(baseChange T.hom).obj A` and `familyLineBundle A L`.
The rigidified family is defined on `T ×_S A`, whereas that base change has
total space `A ×_S T`. The existing `familyLineBundle` forgets the
rigidification and pulls back along
`(relativeSpaceSymmetry A.X.hom T).inv : A ×_S T ⟶ T ×_S A`.
The second lift is therefore the first lift applied to this actual
transported bundle. In particular it tests every map `Spec K ⟶ T.left`.

For the third lift, both class predicates already descend their family
conditions by `Quotient.lift` through the existing relation of nonempty actual
rigidified isomorphism. Their published invariance lemmas forget a rigidified
isomorphism and pull it back along the same symmetry. Their representative
lemmas identify each class predicate with its family condition. Thus quotient
induction and the second lift give the claimed comparison on every class.
This describes the intended elementary descent; this module proves none of
the conjuncts.

The bases and test schemes in these lifts are arbitrary. No
quasi-separatedness, reducedness, projectivity, representability,
dual-existence, or supplied comparison hypothesis is added. The aggregate
asks for the field comparison itself, rather than assuming it as an
antecedent.

## Original source and remaining proof obligations

The governing registered original is B. Edixhoven, G. van der Geer and
B. Moonen, *Abelian Varieties*, preliminary version of the first chapters,
source ID `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The retained file is
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
No source-specific errata note was present in the checked workspace,
project, or Library `notes/errata/` locations.

Notation (0.4), printed p.1/PDF p.5, defines a variety as separated, finite
type, and geometrically integral, and a line bundle as a locally free
rank-one module sheaf. Paragraph (6.2), printed p.88/PDF p.92, describes
rigidified bundles and their isomorphism classes on `X ×_S T`. The existing
product symmetry accounts for the reversed factors in the Library's
rigidified-family category. Its stronger hypotheses for rigidified
automorphism triviality and Picard representability are not needed merely
to form the categories or the three comparison propositions.

Remark (6.9), printed p.91/PDF p.95, defines algebraic equivalence of
divisors on a smooth proper variety over an algebraically closed field by
smooth parameter varieties, flat codimension-one subvarieties of `X ×_k T`,
and differences of their fibres at two rational points. It then relates
the corresponding line-bundle classes to connected components of the Picard
scheme. Paragraph (7.24), printed p.107/PDF p.111, defines line-bundle
algebraic equivalence through the Néron–Severi component group and identifies
it after algebraic closure with the earlier divisor notion.

The present statement is a derived explicit line-bundle-family comparison,
not a verbatim statement of those divisor or component formulations. A
future proof using them must justify passage between the actual family
with its two restriction isomorphisms and the relevant divisor or
identity-component condition. In particular it must construct applicable
families and endpoint identifications, rather than assuming that an
identity-component membership symbol supplies them.

Chapter VI §3, printed p.95/PDF p.99, gives the source point formula
`φ_L(x) = [t_x^* L ⊗ L⁻¹]`. For an algebraically closed field the sections
tested in the Lean translation predicate range over precisely these rational
points. An isomorphism `t_x^* L ≅ L` corresponds to the vanishing of the
displayed line-bundle class at that point. Passing between these actual
isomorphisms and Picard classes, and between vanishing on all rational points
and vanishing of the source homomorphism as a scheme morphism, remain
justifications required of a proof through the Picard scheme.

Proposition (7.21), printed pp.105–106/PDF pp.109–110, expresses a bundle in
the kernel as `t_x^* H ⊗ H⁻¹` for an ample bundle `H` over an algebraically
closed field. An approach through that proposition must establish the
applicable field projectivity and ample-bundle existence and construct the
actual family with the required endpoints. Those facts are not added as
hypotheses here. Corollary (7.22), printed p.106/PDF p.110, identifies the
identity component with the kernel of `L ↦ φ_L`. It motivates this target
but alone supplies no imported proof of this exact existential-family
comparison.

The field comparison is the substantive obligation; the three lifts record
its pointwise and quotient consequences as one comparison unit. This module
does not assert an ordinary-fibre comparison, an fppf Picard comparison,
openness, normalization, or representability, and does not prove the parent
relative dual-existence statement. A proof of the selected aggregate belongs
to a separate task after independent statement acceptance and publication.
