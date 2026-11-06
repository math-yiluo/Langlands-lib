# Translation invariance of actual pulled-back families at geometric points

Authors: Worker 967.

Module `Langlands.AlgebraicGeometry.Picard.PicardZeroFamilyGeometricPointComparison`
is a helper module for the proof of
`Langlands.AbelianScheme.FiniteTypePicardZeroOpenLocusStatement`. It is an
internal compatibility module for the Library's predicates
`GroupScheme.IsTranslationInvariant`, `fibreLineBundle`,
`IsGeometricallyPicardZero` and `IsPicardZeroFamily`, and for the actual
rigidified relative pullback `RigidifiedLineBundle.relativePullback`. It
asserts no literature theorem. It defines one proposition,
`HasOpenFibreTranslationInvarianceLocus`, and proves four theorems. Its
last theorem reduces the geometric-point criterion needed by an open-locus
argument to a criterion for single line bundles on abelian schemes; it
proves no openness itself.

Throughout, `S` is an arbitrary scheme in universe `u`, `A` an abelian
scheme over `S`, `T` (or `P`) an arbitrary scheme over `S`, and `L` an
actual rigidified family on `T`. For a morphism `s : V ⟶ T.left`, the
pulled-back family `L_s` is
`(RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
(unitSection_comp A) (Over.homMk s rfl)).obj L`, a rigidified family on
`Over.mk (s ≫ T.hom)`. Its bundle `familyLineBundle A L_s` lives on the
direct base change `A_(s ≫ T.hom)`; the restriction
`fibreLineBundle (A_T) (familyLineBundle A L) s` of the original family
lives on the iterated base change `(A_T)_s`. No reducedness, finiteness,
flatness or Noetherian hypothesis is imposed anywhere.

## `isTranslationInvariant_fibreLineBundle_id_iff`

For a line bundle `F` on `A`, the restriction `fibreLineBundle A F (𝟙 S)`
to `A_(𝟙 S)` is translation invariant if and only if `F` is. The proof
applies the Library lemma `GroupScheme.isTranslationInvariant_pullback_iso_iff`
to the group-scheme isomorphism `GroupScheme.baseChangeIdIso A.toGrp` from
`A_(𝟙 S)` to `A`. The simp lemma `baseChangeIdIso_hom_left` identifies its
underlying morphism with the projection `pullback.fst A.X.hom (𝟙 S)` used by
`fibreLineBundle`, so the two statements agree.

## `isTranslationInvariant_relativePullback_iff_fibre`

For every scheme `V` and every `s : V ⟶ T.left`, the bundle
`familyLineBundle A L_s` is translation invariant on `A_(s ≫ T.hom)` if and
only if `fibreLineBundle (A_T) (familyLineBundle A L) s` is translation
invariant on `(A_T)_s`. The proof composes two published equivalences:

* `GroupScheme.isTranslationInvariant_pullback_iso_iff`, applied to the
  inverse of the group-scheme comparison
  `GroupScheme.baseChangeCompIso T.hom s A.toGrp`, says that invariance of
  `familyLineBundle A L_s` is equivalent to invariance of its pullback to
  `(A_T)_s` along that comparison;
* `GroupScheme.isTranslationInvariant_iff_of_iso`, applied to the Library
  isomorphism `geometricPointPullbackLineBundleIso A T s L` between that
  pullback and the restriction of the original family, transports
  invariance between them.

In the statement the implicit base of `familyLineBundle` is written out as
`Over.mk (s ≫ T.hom)`; this only fixes elaboration and changes nothing in
the meaning.

## `isTranslationInvariant_fibre_of_isPicardZeroFamily_relativePullback`

Let `K` be an algebraically closed field in universe `u` and
`s : Spec K ⟶ T.left`. If `IsPicardZeroFamily A L_s` holds, then the
restriction of the original family to the fibre over `s` is translation
invariant. The published
`isTranslationInvariant_of_isGeometricallyPicardZero` turns the hypothesis
into invariance of `familyLineBundle A L_s` on `A_(s ≫ T.hom)` itself
(testing the geometric condition at the identity of `Spec K`), and the
previous theorem moves it to the fibre. This is the argument of the reverse
implication in the published `picardZeroGeometricDetection`, stated here
separately.

## `HasOpenFibreTranslationInvarianceLocus`

The module's one definition is a proposition. For a scheme `B` in universe
`u`, an abelian scheme `G` over `B` and a line bundle `M` on `G.X.left`,
`HasOpenFibreTranslationInvarianceLocus G M` says that some open
`W : B.Opens` satisfies, for every algebraically closed field `K` in
universe `u` and every `t : Spec K ⟶ B`,
`IsTranslationInvariant (G_t) (fibreLineBundle G M t) ↔ Set.range t ⊆ W`.
Here `G_t` is `(baseChange t).obj G` with its group-scheme structure, and
`fibreLineBundle G M t` is the pullback of `M` to it along the first
projection. In words: an open subset of the base detects the geometric
points over which the restriction of `M` is translation invariant. The
definition puts no condition on `B`, `G` or `M`. It is the hypothesis of
the next theorem, which says nothing about when it holds.

## `exists_isPicardZeroFamily_relativePullback_iff_of_fibreCriterion`

Hypothesis `hcrit`: `HasOpenFibreTranslationInvarianceLocus G M` holds for
every scheme `B` in universe `u`, every abelian scheme `G` over `B` and
every line bundle `M` on `G.X.left`. Unfolded: some open `W ⊆ B` satisfies,
for every algebraically closed field `K` in universe `u` and every
`t : Spec K ⟶ B`,
`IsTranslationInvariant (G_t) (fibreLineBundle G M t) ↔ Set.range t ⊆ W`.

Conclusion: for every `A`, `P` and `L` as above, some open `U ⊆ P.left`
satisfies, for every algebraically closed `K` in universe `u` and every
`s : Spec K ⟶ P.left`,
`IsPicardZeroFamily A L_s ↔ Set.range s ⊆ U`.

Proof. Take `U` from `hcrit` for `G = A_P` and `M = familyLineBundle A L`.

* If `IsPicardZeroFamily A L_s` holds, the previous theorem gives invariance
  of the fibre of `M` over `s`, and `hcrit` gives `Set.range s ⊆ U`.
* Conversely, if `Set.range s ⊆ U`, then `hcrit` gives invariance of the
  fibre of `M` over `s`, and `isTranslationInvariant_relativePullback_iff_fibre`
  gives invariance of `M_s = familyLineBundle A L_s` on `G_s = A_(s ≫ P.hom)`
  over `Spec K`. Apply `hcrit` a second time, to `G_s` and `M_s`, obtaining
  an open `W ⊆ Spec K`. At the geometric point `𝟙 (Spec K)`,
  `isTranslationInvariant_fibreLineBundle_id_iff` and invariance of `M_s`
  give `Set.range (𝟙 _) ⊆ W`, so `W` contains every point of `Spec K`.
  Hence for every algebraically closed `K'` and `t : Spec K' ⟶ Spec K` the
  inclusion `Set.range t ⊆ W` holds, and `hcrit` gives invariance of the
  fibre of `M_s` over `t`. That is `IsPicardZeroFamily A L_s` by definition.

The hypothesis `hcrit` is quantified over all bases because the argument
uses it both over `P.left` and over each geometric point `Spec K`. The
conclusion is exactly the hypothesis `hU` of a geometric-point open-locus
criterion of the form `IsPicardZeroFamily A L_s ↔ Set.range s ⊆ U`; the
theorem proves nothing about arbitrary, non-geometric test schemes.
