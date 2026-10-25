# The decomposition field of a finite place

Author: Worker 269.

This module is in namespace `Langlands.ClassField.Global` and imports
[IdeleSemilocal](IdeleSemilocal.md). Fix number fields `F E : Type u` with `[Algebra F E]` and
`[Normal F E]`. Fix finite places `v : HeightOneSpectrum (𝓞 F)` and
`w : HeightOneSpectrum (𝓞 E)` with `[w.asIdeal.LiesOver v.asIdeal]`. The decomposition map
`decompositionHom v w : Gal(E_w/F_v) →* Gal(E/F)` comes from
[FundamentalClassStatement](FundamentalClassStatement.md). It forgets `F_v`-linearity down to
`F`-linearity and then restricts to `E`. [IdeleSemilocal](IdeleSemilocal.md) proves that it is
injective (`decompositionHom_injective`).

The module defines the decomposition field `F'`, the fixed field in `E` of the image of the
decomposition map. It identifies `Gal(E_w/F_v)` with `Gal(E/F')` and computes `[F' : F]` and
`[E : F']`. It also proves that restriction of idele-class cohomology from `Gal(E/F)` to
`Gal(E/F')` is the restriction `decompositionRestriction v w n` along the decomposition map, up
to an explicit isomorphism. The module changes no imported definition and declares no instances.

## Definitions

- `decompositionField v w : IntermediateField F E` is
  `IntermediateField.fixedField (decompositionHom v w).range`. As a type it is a number field
  by Mathlib's instance `NumberField.of_intermediateField`. Its algebra structure over `F`, its
  algebra structure on `E` and the scalar tower `F → F' → E` are Mathlib's instances for
  intermediate fields. So `relativeIdeleClassRestriction F (decompositionField v w) E n` is the
  restriction map of [CohomologyMaps](CohomologyMaps.md) for these instances. This is the map
  that occurs in `FundamentalClass.InvariantRestrictionOnClasses` with
  `F' := decompositionField v w`.
- `decompositionEquiv v w : Gal(E_w/F_v) ≃* Gal(E/F')`, where `Gal(E/F')` is
  `E ≃ₐ[decompositionField v w] E`. It is the decomposition map onto its image
  (`MonoidHom.ofInjective` with `decompositionHom_injective`), followed by Mathlib's Galois
  correspondence `IntermediateField.subgroupEquivAlgEquiv` between a finite subgroup `H` of
  `Gal(E/F)` and `Gal(E/E^H)`.
- `decompositionCohomologyIso v w n`, for `n : ℕ`, is an isomorphism
  `relativeIdeleClassCohomology (decompositionField v w) E n ≅
  groupCohomology (Rep.res (decompositionHom v w) (relativeIdeleClassRepresentation F E)) n`.
  The left side is `Hⁿ(Gal(E/F'), C_E)`. The right side is `Hⁿ(Gal(E_w/F_v), C_E)`, with
  `Gal(E_w/F_v)` acting on `C_E` through `decompositionHom v w`; it is the target of
  `decompositionRestriction v w n` and `localIdeleClassMap v w n`. The isomorphism is
  `groupCohomology.mapIso` for the group isomorphism `(decompositionEquiv v w).symm` and the
  identity of the coefficient module `C_E`.
- `DecompositionRestrictionFactors v w n : Prop` is the proposition
  `relativeIdeleClassRestriction F (decompositionField v w) E n ≫
  (decompositionCohomologyIso v w n).hom = decompositionRestriction v w n`. It is only a name
  for the factorization below. The theorem `decompositionRestrictionFactors v w n` proves it.

## Theorems

- `restrictScalars_decompositionEquiv v w σ`: forgetting `F'`-linearity of
  `decompositionEquiv v w σ` gives `decompositionHom v w σ`.
- `restrictScalarsHom_comp_decompositionEquiv v w`: the same statement as an equality of
  monoid homomorphisms,
  `(AlgEquiv.restrictScalarsHom F).comp (decompositionEquiv v w).toMonoidHom =
  decompositionHom v w`.
- `decompositionHom_decompositionEquiv_symm v w g`: for `g : Gal(E/F')`, the decomposition map
  sends `(decompositionEquiv v w).symm g` to `g.restrictScalars F`.
- `finrank_decompositionField v w`, assuming `[IsGalois F E]`:
  `Module.finrank F (decompositionField v w) = (decompositionHom v w).range.index`. It uses
  `Subgroup.index`, so no `Fintype` instance appears in the statement.
- `finrank_decompositionField_eq_card v w`:
  `Module.finrank (decompositionField v w) E = Nat.card Gal(E_w/F_v)`. No Galois hypothesis on
  `E_w / F_v` is needed.
- `finrank_decompositionField_eq_local v w`, assuming
  `[IsGalois (padicField v).Carrier (w.adicCompletion E)]`:
  `Module.finrank (decompositionField v w) E =
  Module.finrank (padicField v).Carrier (w.adicCompletion E)`. The finite-dimensionality of
  `E_w / F_v` is supplied inside the proof by `FiniteExtension.local_finite v w`.
- `finrank_div_finrank_local v w`, under the same local Galois hypothesis:
  `Module.finrank F E / Module.finrank (padicField v).Carrier (w.adicCompletion E) =
  Module.finrank F (decompositionField v w)`. The left side is the natural-number quotient
  that appears as a scalar in `FundamentalClass.InvariantLocalOnClasses`.
- `relativeIdeleClassRestriction_comp_decompositionCohomologyIso v w n` and
  `decompositionRestrictionFactors v w n`: restriction from `Gal(E/F)` to `Gal(E/F')` followed
  by `(decompositionCohomologyIso v w n).hom` equals `decompositionRestriction v w n`.
- `decompositionCohomologyIso_relativeIdeleClassRestriction v w n b`: the same equality applied
  to a class `b : relativeIdeleClassCohomology F E n`.

## Proofs

`restrictScalars_decompositionEquiv` holds by extensionality and `rfl`: both automorphisms act
on `E` by the restriction of `σ`. The monoid-homomorphism form follows by `MonoidHom.ext`.
`decompositionHom_decompositionEquiv_symm` rewrites with the first lemma and
`MulEquiv.apply_symm_apply`.

`finrank_decompositionField` is Mathlib's `IntermediateField.finrank_eq_fixingSubgroup_index`
together with `IntermediateField.fixingSubgroup_fixedField`. The second lemma says that the
fixing subgroup of the fixed field of a subgroup is that subgroup.
`finrank_decompositionField_eq_card` is `IntermediateField.finrank_fixedField_eq_card`, which
gives `[E : E^H] = |H|`. The image of the injective decomposition map has the same cardinality
as `Gal(E_w/F_v)`. `finrank_decompositionField_eq_local` adds
`IsGalois.card_aut_eq_finrank` for `E_w / F_v`. `finrank_div_finrank_local` rewrites
`[E : F]` as `[F' : F] · [E : F']` (`Module.finrank_mul_finrank`), replaces `[E : F']` by the
local degree and cancels it. The local degree is positive by `Module.finrank_pos`.

`decompositionCohomologyIso` needs the compatibility of the identity of `C_E` with the two
actions. An element `g` of `Gal(E/F')` acts on `C_E` by `relativeIdeleClassAut F' E g`. The
corresponding local automorphism acts by
`relativeIdeleClassAut F E (decompositionHom v w ((decompositionEquiv v w).symm g))`. After
`decompositionHom_decompositionEquiv_symm` the two actions agree by `rfl`, because
`relativeIdeleClassAut` of [Cocycle](Cocycle.md) only uses the underlying ring equivalence
`σ.toRingEquiv`, which is the same for `g` and `g.restrictScalars F`.

For the factorization, `relativeIdeleClassRestriction F F' E n` is
`groupCohomology.map (AlgEquiv.restrictScalarsHom F) (𝟙 _) n`, and the forward map of
`decompositionCohomologyIso` is `groupCohomology.map (decompositionEquiv v w).toMonoidHom (𝟙 _) n`.
`groupCohomology.map_comp` combines the two into one map along the composite group
homomorphism `(AlgEquiv.restrictScalarsHom F).comp (decompositionEquiv v w).toMonoidHom`.
By `restrictScalarsHom_comp_decompositionEquiv` that composite is `decompositionHom v w`, and
`groupCohomology.map_congr` identifies the result with `decompositionRestriction v w n`. The
elementwise form follows by rewriting with the factorization.

## Provenance

The decomposition field is not a construction in the cited source. It is the standard way of
turning the decomposition group into a Galois group over a number field. Artin–Tate,
Preliminaries §1 (printed p.2, PDF p.11), calls the stabilizer `G_P` of a prime `P` the
decomposition group and uses `Hʳ(G_P, K_P*)`. Artin–Tate VII §3 (printed p.43, PDF p.52),
before Lemmas 2 and 3, works with a subgroup `H` of `G`, its fixed field `E` and the local
degrees `n_q = [E_q : k_p]`. This module takes `H` to be the image of `Gal(E_w/F_v)` under
`decompositionHom v w`. Then `[E : F'] = |H| = [E_w : F_v]` and `[F' : F]` is the index of `H`.
This module is a prerequisite for the proof of `GlobalInvariantLocalFromTotalStatement`
(task b8c567a8), which Worker 226 is writing. The names `decompositionEquiv`,
`decompositionCohomologyIso` and `DecompositionRestrictionFactors` are internal packaging.
