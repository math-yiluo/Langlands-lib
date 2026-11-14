# Base change of the two-axis class presheaf: cartesian squares and carriers

Author: Worker 385.

This helper module supports the proofs of Murre's conditions (F2) and (F3) for the two-axis
class presheaf `TwoAxisRigidifiedLineBundle.classPresheaf A`. It contains no statement or proof
target of its own. Every declaration is internal to this project. Each one is either a routine
consequence of the Library's definitions of the class presheaf, or a standard property of the
self-product `A ×_S A` of an abelian scheme.

Throughout, `A : Langlands.AbelianScheme S`. For a test object `T : Over S`, `abelian A T` is
the Library's base change `A ×_S T`. `carrierMap A h` and `productMap A h` are the maps on base
changes and on their self-products induced by a test map `h : T ⟶ U`.

## Cartesian squares (namespace `TwoAxisFamily`)

- `carrierMap_isPullback A h`: the square with top `carrierMap A h : A ×_S T ⟶ A ×_S U`, sides
  the two structure maps and bottom `h.left : T ⟶ U` is a pullback square. Proof: the outer
  rectangle with `A ×_S U ⟶ A` is the defining pullback of `A ×_S T`, and the right square is
  the defining pullback of `A ×_S U`; `IsPullback.of_right` gives the left square.
- `productMap_isPullback A h`: the analogous square for `productMap A h` between the
  self-products, with sides the structure maps `(mumfordProduct _).hom`. It follows from the
  published `cartesianSelfProductMap_isPullback` applied to the previous square.

## Classes and actual carriers (namespace `TwoAxisRigidifiedLineBundle`)

- `classesPullback_mk`: pulling back the class of `L` is the class of the pulled-back
  representative (definitional).
- `classesPullback_comp`: `classesPullback A (h ≫ k) = classesPullback A h ∘ classesPullback A k`
  on elements. The proof uses the Library's `relativePullbackComp`.
- `mk_eq_mk_of_carrierIso`: two classes over `T` are equal as soon as the underlying actual line
  bundles of representatives are isomorphic as module sheaves. This is the published
  `nonempty_iso_of_carrierIso` (the rigidifications can always be matched on an abelian scheme)
  passed to the quotient.
- `nonempty_carrierIso_of_mk_eq_mk`: conversely, equal classes have isomorphic carriers (forget
  the rigidifications of an isomorphism of representatives).
- `classesPullback_mk_eq_iff`: combining the two, `classesPullback A h ⟦L⟧ = ⟦M⟧` holds exactly
  when the pullback of the carrier of `L` along `productMap A h` is isomorphic to the carrier of
  `M`.

## The self-product of an abelian scheme (namespace `Langlands.AbelianScheme`)

The structure map of `mumfordProduct A`, that is `A ×_S A ⟶ A ⟶ S`, is a composite of a base
change of `A ⟶ S` and `A ⟶ S` itself. The instances record that it is

- `mumfordProduct_smooth`: smooth;
- `mumfordProduct_isProper`: proper;
- `mumfordProduct_flat`: flat;
- `mumfordProduct_geometricallyConnected`: geometrically connected
  (`GeometricallyConnected.comp`);
- `mumfordProduct_geometricallyIntegral`: geometrically integral. By
  `GeometricallyIntegral.iff_geometricallyIntegral_fiber` it suffices to treat each fibre over a
  residue field. That fibre is smooth and geometrically connected, being a base change, and the
  published `smoothGeometricIntegrality` makes it geometrically integral.

Finally, `mumfordProduct_appTop_bijective` states the following. Let the base be
`Spec R` and let `B` be any `R`-algebra. Then the global-sections map of the projection
`(A ×_R A) ×_R B ⟶ Spec B` is bijective. This is the published
`smoothProperConnectedGlobalFunctions` applied to that base change, which is smooth, proper and
geometrically connected by the instances above. It is the global-functions hypothesis of the
published noetherian seesaw theorem `noetherianLineBundleSeesaw`.
