# Geometric Picard zero from trivial field-isogeny pullback

This module proves `Langlands.AbelianScheme.FieldTrivialPullbackPicardZeroStatement`
exactly, as the theorem `Langlands.AbelianScheme.fieldTrivialPullbackPicardZero`.
Let `k` be a field and `f : A ⟶ B` an isogeny of actual abelian schemes over
`Spec k`. Let `T` be a test `k`-scheme and `L` a rigidified family on `T × B`
whose underlying line bundle has trivial `f_T` pullback. Then `L` satisfies
`IsPicardZeroFamily B L`.

The module assembles published results. It adds no new geometric argument.

- `algClosedFieldTrivialPullbackTranslationInvariant_of`: from
  `hinj : TrivialPullbackCharacterInjectiveStatement`, it proves
  `AlgClosedFieldTrivialPullbackTranslationInvariantStatement`. Fix an
  algebraically closed field `K`, an isogeny `f : A ⟶ B` of actual abelian
  schemes over `Spec K`, and a line bundle `L` on `B` with
  `(hom f)^* L ≅ O_A`. The proof applies
  `isTranslationInvariant_of_trivialHomPullback` with `S = Spec K`. Its
  section-lifting input is `exists_point_lift_of_isogeny hf`: every section
  `x : Over.mk (𝟙 (Spec K)) ⟶ B.X` is `a ≫ (groupHom f).hom.hom` for a
  section `a` of `A`. Its injectivity input is `hinj` at the base
  `Spec K`, the isogeny `f` and the test object `Over.mk (𝟙 (Spec K))`.

- `fieldTrivialPullbackPicardZero_of`: from `hinj`, it proves
  `FieldTrivialPullbackPicardZeroStatement`. The published reduction
  `fieldTrivialPullbackPicardZero_of_algClosed_translationInvariant` turns the
  previous theorem into the target statement. That reduction transports a
  trivialized family over an arbitrary test scheme `T` to every geometric
  fibre `Spec K → T`, where `K` is algebraically closed.

- `fieldTrivialPullbackPicardZero`: the target theorem. It applies
  `fieldTrivialPullbackPicardZero_of` to the published unconditional theorem
  `trivialPullbackCharacterInjective` (module
  `Langlands.AbelianScheme.TrivialPullbackCharacterInjective`). That theorem
  proves `TrivialPullbackCharacterInjectiveStatement` from the published
  uniqueness half of descent for line bundles along affine flat surjections
  (`unitCocycleDescentUniqueness`). So the entry theorem has no remaining
  hypothesis.

No hypothesis is added to the target. The field `k`, the test scheme `T` and
the rigidified family stay arbitrary. There is no reducedness, separability,
characteristic or projectivity assumption. The proof does not assume
Picard-zero membership, surjectivity of the class character, or existence of
a dual abelian variety.

The mathematics is the classical argument behind Edixhoven, van der Geer and
Moonen, *Abelian Varieties* (preliminary draft), Chapter VII, 7.2–7.5. If
`f^*L` is trivial, then `L` is invariant under translation by every point in
the image of `f`. Over an algebraically closed field every point of `B` lies
in this image, because `f` is finite and surjective. The source does not state
this geometric-fibre comparison as a separate numbered result. Here the
invariance comes from injectivity of the normalized kernel character on
classes with trivial pullback, which descent provides.
