# Constant scalar comparisons and the tensor unit

This module supplies internal compatibility laws for the actual constant-sheaf scalar comparisons in `ConstantScalarExtension` and `ConstantScalarRestriction`. It also constructs the module tensor unit on group actions. Its provenance is categorical: the maps come from Mathlib's module tensor adjunction and sheafification, and the associated-sheaf laws follow from the existing invariant-limit inclusions. No Harris theorem is transcribed here.

For the site-level results, let `C : Type w` have morphisms in universe `v`, let `J` be a Grothendieck topology on `C`, and let `φ : R →+* S` be a homomorphism of commutative rings in universe `u`. Module carriers have universe `u`. Actual sheafification is assumed for both module categories; the site object and morphism universes are independent of `u`. Write `T` for module tensor extension, `U` for module scalar restriction, `E` for sheafified tensor extension, `Uₛ` for sheaf scalar restriction, and `c_R`, `c_S` for constant-sheaf functors. The previously constructed comparisons have directions

- `e_M : E(c_R M) ≅ c_S(T M)`;
- `r_N : Uₛ(c_S N) ≅ c_R(U N)`.

`constantExtendScalarsIso_inv_hom` identifies the inverse comparison on underlying presheaves with the sheafification of the inverse constant-composition identification followed by the sheafification of the tensor image of `toSheafify`. This is the defining formula for the imported comparison. `constantRestrictScalarsIso_toSheafify` says that applying `U` to the presheaf sheafification unit and then applying `r_N` equals the constant-composition identification followed by the sheafification unit for `U N`. Its proof uses the defining formula for `constantCommuteCompose`, the factorization for the sheafification comparison, and naturality of `toSheafify`.

`constantExtendScalarsIso_toSheafify` gives the analogous extension formula: apply `T` to the constant-presheaf sheafification unit, then the sheafification unit of the resulting tensor presheaf, then `e_M`. The result is the constant-composition identification followed by the sheafification unit for `T M`. The proof cancels the inverse comparison and uses its defining formula and naturality of `toSheafify`.

`constantScalarChange_unit` proves the compatibility equation

`ηₛ(c_R M) ≫ Uₛ(e_M.hom) ≫ r_(T M).hom = c_R(η_M)`.

Here `η` is the actual module tensor/restriction adjunction unit and `ηₛ` is the induced sheaf adjunction unit. The proof forgets to presheaves and applies the sheafification universal property. Naturality of the whiskered module unit moves the original sheafification unit across it. The two preceding normalization formulas then reduce the assertion to the constant-presheaf unit identity; after factoring off the final sheafification unit, the remaining identity is definitional.

`moduleExtensionActionUnit` is a natural transformation from the identity on `Action (ModuleCat R) G` to `T.mapAction G ⋙ U.mapAction G`. Its component has underlying map `η_(M.V)`. Naturality of the module adjunction unit proves commutation with every group operator, and also naturality for every equivariant module morphism. The group lies in universe `u`.

For the associated result, `X : Scheme.{u}` is an actual scheme and `Y : Action X.Etale G` is an arbitrary cover-object action on its small etale site. Write `A_R`, `A_S` for `constantAssociatedFunctor` over the two rings, `a_M : E(A_R M) ⟶ A_S(T_* M)` for the imported associated extension comparison, and `b_N : Uₛ(A_S N) ≅ A_R(U_* N)` for the associated restriction comparison. Then `constantAssociatedScalarChange_unit` proves

`ηₛ(A_R M) ≫ Uₛ(a_M) ≫ b_(T_* M).hom = A_R((moduleExtensionActionUnit φ).app M)`.

The proof uses the invariant-limit hom-extensionality theorem. After composing with the target invariant inclusion, the restriction and extension inclusion-normalization laws express the left side as the source inclusion followed by the product-section map of `ηₛ(c_R M.V) ≫ Uₛ(e_(M.V).hom) ≫ r_(T M.V).hom`. The site-level unit equation reduces this coefficient map to `c_R(η_(M.V))`. Naturality of the invariant inclusion supplies the right side.

These are compatibility laws for canonical maps already constructed from genuine sheaves and limits. No finite-group, flatness or torsor premise is used. Invertibility of the associated extension comparison, coefficient-reduction transition coherence, local triviality and the Harris geometric specialization remain separate obligations.
