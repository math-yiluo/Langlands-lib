# Translation-invariant bundles are algebraically trivial via a smooth family

This module proves the reverse direction of the field smooth-family
comparison. Over an algebraically closed field `K`, a translation-invariant
line bundle on an abelian variety is algebraically trivial via a smooth
family. Three geometric results that the Library states but has not proved
are explicit hypotheses of the final theorem.

## Declarations

In namespace `Langlands.AbelianScheme.SmoothFamilyOfTranslation`, for an
abelian scheme `A` over any base `S`:

- `pointMap_addition A c`: for a section `c` of `A`, composing
  `smoothFamilyPointMap A A.X c : A.X.left ⟶ A ×_S A` with the addition
  `mumfordAddition A` gives the translation `(GroupScheme.translation A.toGrp c).left`.
- `family A preservation H N`: the line bundle `μ^*H ⊗ pr₂^*N` on
  `(relativeSpace A.X.hom).obj A.X`, the product with the parameter factor
  first. Here `μ` is `mumfordAddition A` and `pr₂` is the second projection
  `pullback.snd A.X.hom A.X.hom`. The tensor product uses the tensor
  preservation statement `preservation`.
- `familyRestrictionIso A preservation H N c`: the restriction of the family
  along `smoothFamilyPointMap A A.X c` is isomorphic to `t_c^*H ⊗ N`.
- `familyRestrictionOneIso A preservation H N evaluation`: at the identity
  section `1`, the restriction is isomorphic to the trivial bundle, given
  `evaluation : tensorObj H.obj N.obj ≅ structureSheaf A.X.left`.

In namespace `Langlands.AbelianScheme`:

- `isAlgebraicallyTrivialViaSmoothFamily_of_isTranslationInvariant`: takes
  these hypotheses:
  - `integrality : SmoothGeometricIntegrality.{u}`;
  - `ample : GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u}`;
  - `lifting : AlgClosedFieldTranslationDifferenceLiftingStatement.{u}`.

  Then for an algebraically closed field `K`, an abelian scheme `A` over
  `Spec K` and `L : LineBundle A.X.left` with
  `GroupScheme.IsTranslationInvariant A.toGrp L`, it proves
  `IsAlgebraicallyTrivialViaSmoothFamily A L`.

## Proof

The parameter scheme is `C = A.X`, with the points `c0 = 1` and `c1 = x`.
It is smooth, separated, locally of finite type and quasi-compact because
`A` is an abelian scheme. It is geometrically integral by `integrality`,
since it is smooth and geometrically connected.

`ample` gives an ample `H` on `A.X.left`. The Library lemma
`LineBundle.exists_tensorObj_iso_structureSheaf` gives a line bundle `N`
with an isomorphism `evaluation : H ⊗ N ≅ 𝒪`. The tensor preservation
statement is the Library theorem
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`. `lifting` is
Proposition (7.21) of Edixhoven, van der Geer and Moonen, *Abelian
Varieties*. Applied to `H`, `N`, `evaluation` and `L`, it gives a rational
point `x` with `t_x^*H ⊗ N ≅ L`.

The family is `μ^*H ⊗ pr₂^*N`. Its restriction along the point map at `c`
is computed with the Library's pullback-of-tensor and
composition-of-pullbacks isomorphisms (`pullbackTensorIso`,
`pullbackCompIso` and `tensorIsoOf`, in namespace
`Langlands.AbelianScheme.MumfordPicardZero` of
`Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroReduction`). They
use `pointMap_addition` for the first factor and `smoothFamilyPointMap_snd`
for the second, so the restriction is `t_c^*H ⊗ N`.

`pointMap_addition` is proved in the category of `S`-schemes. The point map
is the morphism `A.X ⟶ mumfordProduct A` whose two coordinates are the
constant map to `c` and the identity. Composing it with
`mumfordFirst A * mumfordSecond A` gives `c * 𝟙`, which is
`GroupScheme.translation A.toGrp c` by definition (`MonObj.comp_mul`).

At `c = 1`, `t_1` is the identity (`pullbackCongr` and `pullbackId`), so
`evaluation` trivializes the restriction. At `c = x`, the restriction
composed with the (7.21) isomorphism is isomorphic to `L`.

## Scope

The bundle `N` is any tensor inverse of `H` chosen by the Library lemma,
not a canonical dual. The three hypotheses are the Library statements
named above, unchanged. The field `K` and the abelian scheme are
arbitrary, with no further hypotheses. This module does not prove the
forward direction of the comparison.
