# Proof that a finite Mumford map to the chosen dual over a field is surjective

Authors: Worker 3613, with Worker 2029 (the two-projection lifting argument in the support
module `Langlands.AlgebraicGeometry.Picard.FiniteTranslationDifferenceLifting` adapts Worker
2029's proof of `Langlands.AbelianScheme.algClosedFieldTranslationDifferenceLifting_of_cube`).

Module `Langlands.AlgebraicGeometry.Picard.FieldFiniteMumfordMapSurjectiveProof`. Support
module: `Langlands.AlgebraicGeometry.Picard.FiniteTranslationDifferenceLifting`.

## Target

The theorem `Langlands.AbelianScheme.fieldFiniteMumfordMapSurjective` has type exactly the
proposition `Langlands.AbelianScheme.FieldFiniteMumfordMapSurjectiveStatement.{u}` (module
`Langlands.AlgebraicGeometry.Picard.FieldFiniteMumfordMapSurjectiveStatement`), at arbitrary
universe `u`, with no further hypotheses: for the binders `preservation` and `square`, every
field `K`, every abelian scheme `A` over `Spec K` with dual datum `hA`, every rigidified line
bundle `L`, every `M` with `evaluation : L ⊗ M ≅ 𝒪`, if the underlying scheme morphism of
`f = mumfordSchemeMap preservation square A L M evaluation hA` is finite, then it is
surjective. Its proof applies `FiniteMumfordSurjective.surjective_mumfordSchemeMap` below.

## Route

The argument is Mumford's: every translation-invariant line bundle is a translation difference
of `L`. Edixhoven, van der Geer and Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), prove this for ample `L` as
Proposition (7.21), printed pp.105–106. It is applied here at geometric points of the chosen
dual. Finiteness of `f` replaces ampleness. The two-projection argument itself is the support
module's `translationDifferenceLifting_of_finite`; see its Markdown.

## Declarations

In namespace `Langlands.AlgebraicGeometry`:

- `finite_setOf_comp_eq_of_isFinite f e b`. Let `f : X ⟶ Y` be finite, `e : Spec K ⟶ Y` a
  point over a field `K`, and `b : Spec Ω ⟶ Spec K` a morphism from the spectrum of a field
  `Ω`. Then only finitely many `a : Spec Ω ⟶ X` satisfy `a ≫ f = b ≫ e`.

In namespace `Langlands.AbelianScheme`:

- `dualScheme_hom_ext A hA`: two morphisms `T ⟶ dualScheme A hA` over `S` with the same
  classified rigidified class (`RigidifiedLineBundle.classifyingMap` of the Poincaré family)
  are equal.

In namespace `Langlands.AbelianScheme.FiniteMumfordSurjective`, with `A` an abelian scheme
over `Spec K` for a field `K`, a rigidified line bundle `L`, a line bundle `M`, an evaluation
`L ⊗ M ≅ 𝒪`, and `b : Spec Ω ⟶ Spec K` for a field `Ω`:

- `pointOf A b x : Over.mk b ⟶ A.X`: the `K`-morphism `x.left ≫ pullback.fst A.X.hom b`
  underlying a rational point `x` of the base change `A_Ω = (baseChange b).obj A`.
  `pointOf_injective` states that `x ↦ (pointOf A b x).left` is injective.
- `difference preservation A L M b x`: the line bundle `t_x^* L_Ω ⊗ M_Ω` on `A_Ω`, where
  `L_Ω` and `M_Ω` are pullbacks along `pullback.fst A.X.hom b`.
- `familyLineBundleIso`: the line bundle of the Mumford family (`mumfordBundle`) pulled back
  along `pointOf A b x` is isomorphic to `difference … x`.
- `isTranslationInvariant_difference` (for algebraically closed `Ω`): every `difference … x`
  is translation invariant.
- `comp_mumfordSchemeMap_of_trivial`: if `difference … x` is trivial, then the Mumford map
  sends `pointOf A b x` to the origin: `(pointOf A b x).left ≫ f.left = b ≫ e_D.left`.
- `finite_setOf_difference_trivial` (for finite `f`): only finitely many rational points `x`
  of `A_Ω` have `difference … x` trivial.
- `evaluationOf`: the pulled-back evaluation `L_Ω ⊗ M_Ω ≅ 𝒪` on `A_Ω`.
- `exists_relativePullback_mumfordBundle_iso` (for algebraically closed `Ω` and finite `f`):
  every Picard-zero rigidified family over `Spec Ω` is isomorphic to the pullback of the
  Mumford family along some `pointOf A b x`.
- `exists_comp_mumfordSchemeMap_eq` (for algebraically closed `Ω` and finite `f`): every
  morphism `Over.mk b ⟶ dualScheme A hA` factors as `a ≫ f`.
- `surjective_mumfordSchemeMap`: if `f = mumfordSchemeMap preservation square A L M evaluation
  hA` is finite, then `f.left` is surjective.

In namespace `Langlands.AbelianScheme`:

- `fieldFiniteMumfordMapSurjective : FieldFiniteMumfordMapSurjectiveStatement.{u}`.

Here `preservation` and `square` are the two binders of the target proposition. They are used
as given and are not proved here.

## Proofs

`finite_setOf_comp_eq_of_isFinite`: the fibre product `pullback f e` is finite over `Spec K`,
hence affine with global functions a finite-dimensional `K`-algebra. A morphism `a` with
`a ≫ f = b ≫ e` gives `pullback.lift a b` and hence a `K`-algebra homomorphism from these
global functions to `Ω`. Morphisms into an affine scheme are determined by their maps on
global functions (`ext_of_isAffine`), and `a` is recovered as `pullback.lift a b ≫
pullback.fst`. So `a` is determined by this homomorphism. There are only finitely many
`K`-algebra homomorphisms from a finite-dimensional `K`-algebra to a field.

`dualScheme_hom_ext`: the classified class of `h₂` is Picard-zero, by
`isPicardZeroClass_pullback` (with the published `picardZeroPullback`) and
`poincareFamily_universal`. Both maps classify this class, so both equal its `dualClassify`
by `dualClassify_unique`.

`familyLineBundleIso`: the published `FieldMumfordPoint.carrierIso` identifies the module
underlying the pulled-back Mumford family with a supplied module. The supplied module here is
the pullback along the symmetry `σ : pullback b A.X.hom ≅ pullback A.X.hom b` of
`difference … x`. The factor pulled back from `Spec Ω` is trivialized by
`fieldLineBundleTriviality`. Pulling back along `σ.inv` and cancelling `σ.inv ≫ σ.hom = 𝟙`
gives the isomorphism of line bundles.

`isTranslationInvariant_difference`: the Mumford family is Picard-zero by `square`. Its
pullback along `pointOf A b x` is Picard-zero by `picardZeroPullback`. Over the algebraically
closed field `Ω` the line bundle of a Picard-zero family is translation invariant
(`isTranslationInvariant_of_isGeometricallyPicardZero`). Transport along
`familyLineBundleIso` finishes the proof.

`comp_mumfordSchemeMap_of_trivial`: `fieldMumfordPointComparison`, applied with the trivial
rigidified family `Q` over `Over.mk b`, gives an isomorphism between the pulled-back Mumford
family and `Q`. Its premise is the given trivialization of `difference … x`, composed with
`LineBundle.pullbackTrivialIso`. By `mumfordSchemeMap_points`, `pointOf A b x ≫ f` classifies
the trivial class. So it equals `dualClassify` of the trivial class, which is
`Over.homMk b ≫ dualOrigin A hA` by `dualClassify_trivial`. Taking underlying morphisms gives
the claim.

`finite_setOf_difference_trivial`: by the previous lemma, `x ↦ (pointOf A b x).left` maps the
set into `{a | a ≫ f.left = b ≫ e_D.left}`. That set is finite by
`finite_setOf_comp_eq_of_isFinite`, and the map is injective (`pointOf_injective`).

`exists_relativePullback_mumfordBundle_iso`: apply
`translationDifferenceLifting_of_finite` (support module `FiniteTranslationDifferenceLifting`) on
`A_Ω` with `L_Ω`, `M_Ω` and `evaluationOf`. Its invariance hypothesis is
`isTranslationInvariant_difference`, and its finiteness hypothesis is
`finite_setOf_difference_trivial`. Its target `P` is the line bundle of the given family,
which is translation invariant by `isTranslationInvariant_of_isGeometricallyPicardZero`. This
gives `x` with `difference … x ≅ P`. Then `fieldMumfordPointComparison` turns it into a
rigidified isomorphism between the pulled-back Mumford family and the given family.

`exists_comp_mumfordSchemeMap_eq`: apply the previous lemma to the pullback of the Poincaré
family along the given morphism `yo`. That pullback is Picard-zero by `picardZeroPullback`.
With `a = pointOf A b x`, `mumfordSchemeMap_points` shows that `a ≫ f` and `yo` classify the
same class. So `a ≫ f = yo` by `dualScheme_hom_ext`.

`surjective_mumfordSchemeMap`: let `y` be a point of the dual. Let `κ` be its residue field
and `Ω = AlgebraicClosure κ`. The composite
`Spec Ω ⟶ Spec κ ⟶ D.left` (`Scheme.fromSpecResidueField`) is a morphism over `Spec K` that
sends the closed point to `y`. Write it as `yo`. By `exists_comp_mumfordSchemeMap_eq`,
`yo = a ≫ f`, so `f.left` sends the image of the closed point under `a.left` to `y`. Here
`Spec κ` has a single point, and `fromSpecResidueField_apply` gives the image `y`.

`fieldFiniteMumfordMapSurjective`: introduce the binders and apply
`surjective_mumfordSchemeMap`.

No hypothesis beyond the binders is used. Apart from the support module, all cited results
are published Library proofs or Mathlib.
