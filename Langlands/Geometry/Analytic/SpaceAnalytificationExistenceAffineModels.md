# Affine models of presheaf fibre squares of affine tests

Internal bookkeeping (derived provenance) for the conditional existence argument. All
statements are unconditional.

- `ty f`: for `f : A →ₐ[K] B`, the map of represented presheaves
  `(schemeYoneda _).map (ringTestMap K f) : Spec B → Spec A` over `Spec K`. The lemmas
  `ty_comp`, `ty_id`, `ty_injective` and `ty_surjective` state functoriality, faithfulness and
  fullness. Faithfulness and fullness follow from full faithfulness of `schemeYoneda` and
  from `affineRingPointEquiv`.
- `pointHom_changeRing`: the presheaf map of the restricted point `changeRing f x` is
  `ty f ≫ pointHom K x`.
- `exists_algHom_of_isPullback`: if `Spec C` with `f`, `g` is a presheaf pullback of
  `u : Spec A → F` and `v : Spec B → F`, then algebra maps `α : A → E` and `β : B → E` with
  `ty α ≫ u = ty β ≫ v` factor uniquely through `C`. The lift exists by the pullback property
  and is induced by an algebra map by fullness.
- `TestModel u v` bundles such a model: a coordinate algebra `C : CommAlgCat K`, a finite
  polynomial presentation `R`, the two algebra maps and the pullback square. Its API:
  `w` (commutativity), `exists_lift`, `algHom_ext`, `flip` (swap the factors) and `ofExists`
  (bundle an existential).
- `pointModel hX P Q x y`: a chosen model of `Spec A ×_X Spec B` for test points of a
  separated space, from `exists_affine_test_intersection`.
- `testModel P Q f g`: a chosen model of `Spec A ×_{Spec C₀} Spec B`, from
  `exists_affine_test_pullback`. Both existence lemmas are Worker 790's, in the module
  `SpaceAnalytificationAffineIntersections`, included unchanged from Worker 790's staged
  candidate c8676539-ec2a-4b74-9542-52fb5a971529.
- `TestModel.etale_f` and `TestModel.etale_g`: if the opposite leg is étale
  (`AlgebraicSpace.IsEtale`), the projection is an étale algebra map. `IsEtale.projection`
  makes the projection's scheme map `Spec.map` étale, and `HasRingHomProperty.Spec_iff`
  turns this into `RingHom.Etale`.
