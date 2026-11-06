# The locus where the Mumford bundle of a line bundle is trivial on fibres

Module `Langlands.AbelianScheme.MumfordTrivialLocus`.

Throughout, `G : AbelianScheme B` is an abelian scheme over an arbitrary scheme `B`
and `M : LineBundle G.X.left` is a line bundle on its total space. All classes live in
the Library's group of isomorphism classes of line bundles,
`LineBundle.IsoClasses pullbackTensorComparisonIsIso X`. Its product is the tensor
product, its inverse is the dual class and `1` is the class of the structure sheaf.
Pullback of classes along `f` is the group homomorphism
`LineBundle.pullbackHom pullbackTensorComparisonIsIso f`. In the source the local
notations `cl` and `pb` abbreviate `LineBundle.isoClass pullbackTensorComparisonIsIso`
and `LineBundle.pullbackHom pullbackTensorComparisonIsIso`.

## Definitions

- `mumfordClass G M`: the class on `X ×_B X` (the product `G.X ⨯ G.X` in `Over B`)

  `m^*[M] · (p₁^*[M])⁻¹ · (p₂^*[M])⁻¹ · (e ∘ q)^*[M]`,

  where `m = p₁ * p₂` is the group law, `p₁, p₂` are the two projections,
  `q : X ×_B X ⟶ B` is the structure morphism and `e` is the unit section
  `(1 : Over.mk (𝟙 B) ⟶ G.X).left`. The last factor is the correction that makes the
  class trivial on both coordinate axes over an arbitrary base. Over a field it is
  trivial, because it is pulled back from the spectrum of a field.
- `mumfordTrivialSet G M : Set B`: the points `b` such that the class pulled back along
  the fibre inclusion `(X ×_B X)_b ⟶ X ×_B X` (`Scheme.Hom.fiberι`) is `1`. Here the
  fibre is taken over the residue field `κ(b)`.
- `mumfordTrivialLocus G M : B.Opens`: the same set, bundled with the openness
  theorem `isOpen_mumfordTrivialSet`.
- `baseChangeProductMap G t`: for a field `K` and `t : Spec K ⟶ B`, the comparison
  morphism over `B` from the self-product of the base change
  `(Over.pullback t).mapGrp.obj G.toGrp` to `G.X ⨯ G.X`. Its two components are the
  images of the two projections under `GroupScheme.baseChangePointsEquiv`.

## Results

- `mem_mumfordTrivialLocus_iff`: membership in the locus is triviality of the pulled-back
  Mumford class on the fibre (true by definition).
- `pullbackHom_mumfordClass`: for points `a c : T ⟶ G.X`, pulling back along
  `prod.lift a c` gives
  `(a * c)^*[M] · (a^*[M])⁻¹ · (c^*[M])⁻¹ · (e ∘ T.hom)^*[M]`.
- `mumfordClass_firstAxis`, `mumfordClass_secondAxis`: the class is trivial on the axes
  `(id, e ∘ q)` and `(e ∘ q, id)`.
- `isOpen_mumfordTrivialSet`: the set is open.
- `isTranslationInvariant_of_mumfordClass_eq_one` (any field `K`) and
  `mumfordClass_eq_one_of_isTranslationInvariant` (algebraically closed `K`), combined in
  `isTranslationInvariant_iff_mumfordClass_eq_one`: for an abelian scheme `A` over
  `Spec K` and a line bundle `L` on it, `GroupScheme.IsTranslationInvariant A.toGrp L`
  holds if and only if `mumfordClass A L = 1`.
- `pullbackHom_mumfordClass_baseChange`: the Mumford class pulls back along
  `baseChangeProductMap G t` to the Mumford class of the base change `(baseChange t).obj G`
  with the line bundle `fibreLineBundle G M t`.
- `pullbackHom_baseChangeProductMap_eq_one` and
  `mem_mumfordTrivialSet_of_pullbackHom_eq_one`: for `t : Spec K ⟶ B` with `K` any
  field, the image `b` of the closed point lies in `mumfordTrivialSet G M` if and only if
  the Mumford class pulls back to `1` along `baseChangeProductMap G t`.
- **Main theorem** `isTranslationInvariant_fibreLineBundle_iff`: for an algebraically
  closed field `K` and `t : Spec K ⟶ B`,

  `GroupScheme.IsTranslationInvariant ((baseChange t).obj G).toGrp (fibreLineBundle G M t)
  ↔ Set.range t ⊆ mumfordTrivialLocus G M`.

  So a geometric fibre of `M` is translation invariant exactly when the geometric point
  lies in the open locus.

Helper lemmas in namespace `MumfordTrivialLocus`:
`pullbackHom_isoClass_eq_one_iff` (a pulled-back class is `1` exactly when the pulled-back
sheaf is isomorphic to the structure sheaf), `exists_isoClass_eq` (every class has a
representative) and `range_subset_iff` (the range of a morphism from the spectrum
of a field is the image of its closed point). The imported shared helper
`Langlands.AlgebraicGeometry.Picard.product_geometry` proves that a product of
smooth, proper, geometrically connected objects of `Over S` is again such.

## Proofs

- `pullbackHom_mumfordClass`: compose each factor with `prod.lift a c`, using
  `MonObj.comp_mul`, `prod.lift_fst`, `prod.lift_snd` and `Over.w`, and then
  `LineBundle.pullbackHom_comp_eq`.
- The axis lemmas apply `pullbackHom_mumfordClass` and cancel in the commutative group,
  using `Over.mkIdTerminal_from_left`.
- Openness: choose a representative line bundle `Λ` of the Mumford class. The axis lemmas
  and the hypothesis at `b` are three structure-sheaf isomorphisms. The Library theorem
  `localTwoAxisTriviality` (applied with `X = Y = G.X` and both sections the unit) gives
  an open `V ∋ b` over which `Λ` is trivial. For `b' ∈ V`, the morphism
  `Spec κ(b') ⟶ B` lifts through `V.ι` (`IsOpenImmersion.lift`), so the fibre inclusion
  over `b'` factors through the preimage of `V`. Hence the class is `1` there too.
- Over a field: if the class is `1`, pull it back along `(x ∘ q, id)` for a rational
  point `x`. The two factors pulled back from `Spec K` are `1`
  (`LineBundle.pullbackHom_eq_one_of_factor`), which leaves
  `[τ_x^* L] = [L]`. Conversely, over an algebraically closed field the Library lemma
  `TranslationInvariantIdentities.categorical_multiplication_class` gives
  `m^*[L] = p₁^*[L] · p₂^*[L]` for translation-invariant `L`. Since the correction factor
  is again `1`, the class is `1`.
- Base change: unfold both Mumford classes. `GroupScheme.baseChangePointsEquiv_left`
  identifies the components of `baseChangeProductMap` with the projections followed by
  `pullback.fst`, and `LineBundle.pullbackHom_comp` matches the factors one by one. The
  correction factor on the `B` side is `1` because it factors through `Spec K`.
- Fibre comparison: let `b` be the image of the closed point and
  `g : Spec K ⟶ Spec κ(b)` the canonical factorization of `t`
  (`Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`).
  If `b` is in the set, `baseChangeProductMap G t` factors through the fibre over `b`
  (`pullback.lift`), so its pullback is `1`. Conversely, let `f` be the fibre
  `(X ×_B X)_b ⟶ Spec κ(b)`. It is smooth, proper and geometrically connected, by
  `Langlands.AlgebraicGeometry.Picard.product_geometry` and base change. The pullback `(X ×_B X)_b ×_{κ(b)} Spec K` maps
  over `Spec K` into the base-change self-product, through `baseChangePointsEquiv`. Its
  composite with `baseChangeProductMap` is the projection to the fibre followed by the
  fibre inclusion. So the representative `Λ`, restricted to the fibre, becomes trivial
  after base change to `K`. The helper theorem `fieldBaseChangeTrivialityDescent` (module
  `Langlands.AlgebraicGeometry.Picard.FieldBaseChangeTrivialityDescent`, submitted with
  this module) descends the triviality to the fibre over `κ(b)`.
- Main theorem: combine `isTranslationInvariant_iff_mumfordClass_eq_one` for the base
  change, `pullbackHom_mumfordClass_baseChange`, `range_subset_iff` and the two directions
  of the fibre comparison.

## Selected definition

The selected definition of this contribution is
`Langlands.AbelianScheme.mumfordTrivialLocus`. It is the open subscheme of `B` whose
points are those over which the Mumford class of `M` is trivial on the fibre over the
residue field. `isTranslationInvariant_fibreLineBundle_iff` characterizes it through
geometric points. The final proof of
`Langlands.AbelianScheme.FiniteTypePicardZeroOpenLocusStatement` (task `40d423ed`) uses
both names.

## Provenance

This is a derived, internal construction for task `40d423ed`. It has no separate
literature statement. It is the classical argument that the Picard-zero locus of a line
bundle on an abelian scheme is open. For a line bundle `L` on an abelian variety over an
algebraically closed field, `L` is translation invariant exactly when the Mumford bundle
`m^*L ⊗ p₁^*L⁻¹ ⊗ p₂^*L⁻¹` is trivial. In a family, triviality of a line bundle on fibres
that is already trivial along two axes is an open condition (seesaw / theorem of the
cube). The literature behind the two inputs is recorded in the Markdown of the Library
statements `TranslationInvariantPullbackIdentitiesStatement` (algebraically closed field
identities) and `LocalTwoAxisTrivialityStatement` (Stacks Project, More on Morphisms,
"Theorem of the cube"). This module adds no further literature claim.

The factor `(e ∘ q)^*[M]` makes the axis triviality hold over an arbitrary base without
rigidifying `M`. The Library's `mumfordHomOfLineBundle` (module
`Langlands.AlgebraicGeometry.Picard.MumfordLineBundle`) builds an actual Mumford family
from an explicitly chosen normalization and inverse bundle. Here only isomorphism classes
are needed, so no inverse bundle or evaluation is chosen. Triviality on a fibre does not
depend on the representative.
