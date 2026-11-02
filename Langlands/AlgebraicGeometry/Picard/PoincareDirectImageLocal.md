# The perfect complex of the Poincaré bundle at the origin of the dual

Author: Worker 975. The shape of the support hypothesis of `homology_of_perfectModel` was
agreed with Worker 1165, who supplies it in the final assembly.

Module `Langlands.AlgebraicGeometry.Picard.PoincareDirectImageLocal`, namespace
`Langlands.AbelianScheme.PoincareDirectImage`. This is an internal helper module for the
proof of `Langlands.AbelianScheme.AlgClosedFieldPoincareDirectImageStatement`. Its main
theorem, `homology_of_perfectModel`, is the local computation at the origin in the second
proof of Theorem (9.1) of Edixhoven, van der Geer and Moonen, *Abelian Varieties*
(registered source `edixhoven-vandergeer-moonen-abelian-varieties-draft`), (9.6)–(9.9),
printed pp.128–130 (PDF pp.132–134). Everything is proved in the file, with no hypotheses
beyond the signatures. The main theorem takes the two Library propositions it relies on
as explicit hypotheses.

## Notation

Throughout, `K` is a field, `A : AbelianScheme (Spec K)` and `hA : HasDualScheme A`.
Write `D = dualScheme A hA`, `P = poincareLineBundle A hA` and

- `poincareProjection hA : A ×_K D ⟶ D` for `((baseChange D.hom).obj A).X.hom`;
- `originPoint hA` for the image of the closed point of `Spec K` under the origin
  `(dualOrigin A hA).left`.

For an affine open `V` of `D` with `hV : IsAffineOpen V`, write `B = Γ(D, V)`, and

- `affineFamily hV : (A ×_K D) ×_D Spec B ⟶ Spec B` for the pullback of the Poincaré
  projection along Mathlib's `hV.fromSpec`;
- `affinePoincare hV` for the pullback of `P` to that family, as a line bundle;
- `originIdeal hV hx`, for `hx : originPoint hA ∈ V`, for the prime ideal
  `hV.primeIdealOf ⟨originPoint hA, hx⟩` of `B`.

## The origin and its affine neighbourhood

- `isClosedImmersion_dualOrigin`, `range_dualOrigin` and `isClosed_originPoint`: the origin
  is a section of the separated morphism `D ⟶ Spec K` (`fieldDualSchemeSeparated`). By
  Mathlib's `IsClosedImmersion.of_comp` it is a closed immersion, so `originPoint hA` is a
  closed point.
- `isNoetherianRing_sections`: if `D ⟶ Spec K` is locally of finite type, `B` is
  noetherian.
- `structureHom hV : K ⟶ B` is the ring map underlying `Spec B ⟶ D ⟶ Spec K`.
  `originLift hV hx : Spec K ⟶ Spec B` lifts the origin through the open immersion
  `hV.fromSpec` (`originLift_fac`). `originEval hV hx : B ⟶ K` is its ring map.
  `structureHom_comp_originEval` says that `originEval` retracts `structureHom`.
  `ker_originEval` says that its kernel is `originIdeal hV hx`.
- `originEval_comp_eq` and `spec_map_comp_fromSpec_eq`: a ring map `φ : B ⟶ T` killing
  `originIdeal hV hx` factors through `originEval`. Hence `Spec T ⟶ Spec B ⟶ D` factors as
  `Spec T ⟶ Spec K` followed by the origin.

## The Poincaré bundle near the origin is trivial

`nonempty_pullback_poincare_iso_unit` holds over an arbitrary base `S`. Let `q : X ⟶ A ×_S D`
lie over a `T`-point of `D` that factors through the origin. Then `q^* P` is isomorphic to
the structure sheaf of `X`. The proof uses the Library's `dualPointClass_origin`: the
pullback of the Poincaré family along such a point has the class of the trivial
rigidified bundle. `Quotient.exact` turns this into an isomorphism of rigidified bundles.
Finally `q` factors through `T ×_S A`, and the isomorphism is pulled back along it.

## Fibres over field points

- `isZero_relativeCohomology_of_lt`: on a smooth proper scheme of relative dimension `g`
  over a field, every quasi-coherent module has vanishing cohomology above degree `g`.
  This is the Library's `noetherianSeparatedQuasicoherentVanishing` together with
  `fieldSmoothTopologicalKrullDim`.
- `finrank_relativeGlobalSections_unit`: on a smooth proper geometrically connected scheme
  over a field `T`, the global functions form a one-dimensional `T`-vector space. The
  Library's `smoothGeometricIntegrality` gives geometric integrality. Then
  `bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected`
  shows that `T` maps bijectively onto the global functions
  (`finrank_restrictScalars_self`).
- `smoothOfRelativeDimension_affineFamily`: `affineFamily hV` is smooth of relative
  dimension `g` when `A` is.
- `isZero_homology_baseChange_field`: let `Kc` be a complex over `B` and `T` a field. Assume
  `Kc ⊗ T` represents the derived sections of the pullback of `affinePoincare hV` to the
  fibre over `Spec T`. Then `Hⁱ(Kc ⊗ T)` vanishes for `i < 0` and for `i > g`. Negative
  degrees vanish by the Library's `isZero_homology_of_neg`, degrees above `g` by
  `isZero_relativeCohomology_of_lt`.
- `finrank_homology_zero_baseChange_field`: if moreover `B ⟶ T` kills
  `originIdeal hV hx`, then `H⁰(Kc ⊗ T)` is one-dimensional. The fibre maps to the origin,
  so the bundle on it is trivial by `nonempty_pullback_poincare_iso_unit`, and its global
  sections are `T` by `finrank_relativeGlobalSections_unit`.

## The tangent condition

- `relativeGlobalSectionsCompSpecMapIso`: global sections relative to `g ≫ Spec.map h` are
  the global sections relative to `g`, with scalars restricted along `h`.
- `restrictScalarsSelfIso`: a ring seen through a ring isomorphism onto another ring is
  free of rank one.
- `isEmpty_homology_zero_quotient`: let `K` be algebraically closed, and let `R` be the
  localization of `B` at `originIdeal hV hx`. Let `J` be an ideal of `R` with
  `m² ≤ J ⋖ m`. Assume `Kc ⊗ (R ⧸ J)` represents the derived sections over `Spec (R ⧸ J)`.
  Then `H⁰(Kc ⊗ (R ⧸ J))` is not isomorphic to `R ⧸ J`. The proof assumes the
  proposition `AlgClosedFieldPoincareTangentSectionsStatement` as a hypothesis. The
  residue field of `R` is `K`, by `bijective_algebraMap_residueField`, so
  `nonempty_dualNumber_algEquiv` gives `ψ : K[ε] ≅ R ⧸ J`. The composite
  `t : Spec K[ε] ⟶ Spec (R ⧸ J) ⟶ Spec B ⟶ D` is a tangent vector at the origin. It is
  nonzero: otherwise the image of `originIdeal hV hx` would lie in `J`, so the maximal
  ideal of `R` would lie in `J`. The fibre over `Spec (R ⧸ J)`, with its map to
  `Spec K[ε]` through `ψ`, is a fibre product along `t` (`IsPullback.paste_horiz` and
  `IsPullback.of_iso`). An isomorphism of `H⁰` with `R ⧸ J` would therefore give a
  `K[ε]`-isomorphism of the sections with `K[ε]`, which the tangent proposition forbids.

This replaces the source's use in (9.8) of the universal property of `P` together with
the functoriality of the base-change isomorphisms in the ideal `J`.

## The local computation

`homology_of_perfectModel` assumes:

- `hAL : Langlands.CommutativeAlgebra.RegularLocalPunctualComplexStatement` and
  `hTAN : AlgClosedFieldPoincareTangentSectionsStatement`, as hypotheses;
- `K` algebraically closed, `A.HasRelativeDimension g`, and
  `SmoothOfRelativeDimension g D.hom`;
- an affine open `V` of `D` containing `originPoint hA`;
- a strictly perfect complex `Kc` over `B`, with an isomorphism, for every ring map
  `φ : B ⟶ T`, between `Kc ⊗ T` and the derived sections of the pullback of
  `affinePoincare hV` over `Spec T`. These are the base-change isomorphisms of the
  Library's `UniversalPerfectSectionsStatement`;
- for every `f ∈ originIdeal hV hx`, the homology of `Kc ⊗ B_f` vanishes.

It concludes that `Hⁿ(Kc) = 0` for `n ≠ g` and `H^g(Kc) ≅ B ⧸ originIdeal hV hx` as
`B`-modules.

Proof. Let `R` be the stalk of `D` at the origin. It is the localization of `B` at
`originIdeal hV hx` (Mathlib's `IsAffineOpen.isLocalization_stalk`), and that ideal is
maximal because the origin is closed. `R` is regular by the Library's
`AlgebraicGeometry.Smooth.isRegularLocalRing_stalk`. It has Krull dimension `g` by
`fieldSmoothClosedPointStalkDimension`. Apply `hAL` to `Kc ⊗ R`. Its four hypotheses are
checked as follows; the residue field is reached through the Library's
`baseChangeCompIso`.

1. `isZero_homology_baseChange_field`.
2. `finrank_homology_zero_baseChange_field`.
3. `exists_pow_le_annihilator_homology_localization`, from the support hypothesis.
4. `isEmpty_homology_zero_quotient`.

This gives `Hⁿ(Kc ⊗ R) = 0` for `n ≠ g` and `H^g(Kc ⊗ R) ≅` the residue field. Localization
is flat (`nonempty_baseChange_homology_iso_of_flat`), and a power of the origin ideal kills
every `Hⁿ(Kc)` (`exists_pow_le_annihilator_homology`). So `isZero_of_pow_le_annihilator`
and `nonempty_iso_quotient_of_pow_le_annihilator` transfer the two conclusions from
`Kc ⊗ R` to `Kc`.

In the source, the complex `K^•` of (9.6) over `A = O_{Xᵗ,0}` corresponds to `Kc ⊗ R`
here, and its cohomology there is `Rⁿ p_{2,*} P` near the origin. The vanishing above `g`
and `h⁰ = 1` correspond to the source's use of (7.27) in (9.8). The source works over
`O_{Xᵗ,0}`. This module works over the affine coordinate ring `B` and localizes inside the
proof, so that its conclusion is about `B`-modules, as the sheaf-level assembly needs.
