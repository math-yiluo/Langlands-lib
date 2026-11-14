# A finite closed locus where a Mumford family is trivial

Author: Worker 372.

This internal helper module works with an abelian scheme `A` over `Spec K`, for an arbitrary
field `K`. It produces a relative line-bundle class over the parameter space `A`, trivial at the
unit parameter, whose trivial locus is a closed subscheme of `A` finite over `K`. In classical
terms the class is the Mumford family `Λ(L)` of an ample line bundle `L`. The Library builds it
(`Langlands.AbelianScheme.mumfordBundle`, module `Langlands.AlgebraicGeometry.Picard.MumfordBundle`) from the pullback of `L` along the addition and a chosen inverse
of `L`. The locus plays the role of the kernel `K(L)`.

## Declarations

`exists_finite_locus K A` gives the following data:

- a rigidified class `q : RigidifiedClasses A A.X`;
- a scheme `Z` and a closed immersion `j : Z ⟶ A.X.left` such that `j ≫ A.X.hom` is finite;
- `q` pulls back along the unit point `1 : T ⟶ A.X` to the trivial rigidified class, for every
  `T` over `Spec K`;
- for every `T` over `Spec K` and `h : T ⟶ A.X`, `h.left` factors through `j` if and only if the
  pullbacks of `q` and of the trivial class along `h` are equal.

Proof, step by step:

1. `Langlands.GroupScheme.fieldAmpleExistence` (Library proof of `FieldAmpleExistenceStatement`)
   gives an ample line bundle `L` on `A`. `LineBundle.exists_tensorObj_iso_structureSheaf` gives
   an inverse `M₀`. `fieldLineBundleTriviality` trivializes `M₀` along the unit section, which
   makes `M₀` a rigidified bundle `M`.
2. `q` is the class of `mumfordBundle A preservation M L evaluation`, where `preservation` is the
   Library proof `pullbackTensorComparisonIsIso`. `MumfordParameterAxes.mumfordBundleClass_one`
   gives triviality at the unit.
3. `rigidifiedClassesEqualizerClosed` (Library proof of `RigidifiedClassesEqualizerClosedStatement`)
   gives the closed subscheme `Z` where `q` agrees with the trivial class, with its universal
   property.
4. Finiteness repeats the argument of
   `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleTranslationStabilizerFiniteProof`,
   without the algebraic closure, which that argument never uses. On `Z` the tautological point
   gives an isomorphism of the two families. `antidiagonalTrivialization` turns it into
   `j^*L ⊗ (j ≫ ι)^*L ≅ 𝒪_Z`, where `ι` is the inversion. Both factors are ample
   (`closedImmersionPullbackAmple`; `ι` is an isomorphism). By `ampleTensor` the trivial bundle
   on `Z` is ample. `properAmpleTrivialFinite` then shows that the proper morphism
   `j ≫ A.X.hom` is finite.

`forgetClasses_classesPullback` and `forgetClasses_trivialClass` say that forgetting the
rigidification (`RigidifiedLineBundle.forgetClasses`) commutes with pullback of classes and sends
the trivial rigidified class to `0` in the relative Picard group.

`exists_finite_plain_locus K A` is the version with ordinary relative Picard classes. It gives
`Q : Picard.Group ((relativeSpace A.X.hom).obj A.X)` with `Group.pullback` along `1 : T ⟶ A.X`
equal to `0`, and with the same `Z` and `j`. Now `h.left` factors through `j` if and only if
`Group.pullback ((relativeSpace A.X.hom).map h) Q = 0`. `Q` is the forgotten class of `q`. The
equivalence follows from the rigidified one and from
`RigidifiedLineBundle.forgetClasses_injective`.

## Provenance

The finiteness argument is the one of Edixhoven, van der Geer and Moonen, *Abelian Varieties*
(registered source `edixhoven-vandergeer-moonen-abelian-varieties-draft`), Lemma (2.19): if `L`
is ample then `K(L)` is finite. As in the Library module
`AlgClosedFieldAmpleTranslationStabilizerFiniteProof`, the group scheme `K(L)` is replaced by
the closed agreement locus `Z`. No assumption on `K` beyond being a field is needed.
