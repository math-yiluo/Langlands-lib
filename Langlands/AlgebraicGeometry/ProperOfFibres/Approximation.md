# Finite-type models of a monomorphism into a proper scheme

Module `Langlands.AlgebraicGeometry.ProperOfFibres.Approximation`, namespace
`Langlands.AlgebraicGeometry.ProperOfFibres`. This is the noetherian approximation step of
the properness criterion used for relative parabolic quotients (compare the reduction to a
noetherian base "by direct limit considerations" in Conrad, *Reductive group schemes*
(2014), proof of Theorem 2.3.6, pp. 73–74). Given a
factorization `j ≫ g = f` of morphisms to `Spec V`, it produces a model over a subring of
`V` of finite type over `ℤ`. The statements are internal helpers; the descriptions below
follow the implemented Lean proofs. The descent results used are the FLT-project theorems
in `Langlands.AnthropicFLT.Theorems` imported by the module, and the Library theorem
`NoetherianApproximation.normalFiniteTypeSubalgebra`.

## Basic lemmas

- `specMap_algebraMap_comp`: for a scalar tower `R → R' → V`, the composite
  `Spec V ⟶ Spec R' ⟶ Spec R` is `Spec` of `algebraMap R V`. Proof: functoriality of
  `Spec` and `IsScalarTower.algebraMap_eq`.
- `isPullback_lift_of_fac`: if `X` is the base change of `X₁ ⟶ B` along `ι : Y ⟶ B`, and
  `ι = ι' ≫ κ` for some `κ : B' ⟶ B`, then `X` is the base change of
  `X₁ ×_B B' ⟶ B'` along `ι'`, with the comparison map given by `pullback.lift`. Proof:
  the pullback pasting lemma `IsPullback.of_right`.

## Models of single morphisms

`SchemeModel f R`, for `f : X ⟶ Spec V` and an `R`-algebra `V`, is a structure with
fields: a scheme `X₀`; a morphism `f₀ : X₀ ⟶ Spec R`; a map `π : X ⟶ X₀`; a proof that
the square formed by `π`, `f`, `f₀` and `Spec V ⟶ Spec R` is a pullback; and instances
stating that `f₀` is locally of finite presentation, quasi-compact and quasi-separated.

- `SchemeModel.baseChange M R'` (definition): for a scalar tower `R → R' → V`, the model
  over `R'` with `X₀ := X₀ ×_{Spec R} Spec R'`, `f₀` the second projection, and `π` the
  lift of `M.π` and `f ≫ (Spec V ⟶ Spec R')`. The pullback square comes from
  `isPullback_lift_of_fac`. The finiteness instances are stable under base change.
- `SchemeModel.prop_pullback_snd`: if `P` respects isomorphisms and `P f` holds, then
  `P` holds for `X₀ ×_{Spec R} Spec V ⟶ Spec V`. Proof: this projection is
  `f` composed with the isomorphism `IsPullback.isoPullback`.
- `SchemeModel.exists_subalgebra`: a quasi-compact, quasi-separated `f` that is locally of
  finite presentation has a model over some finitely generated `R`-subalgebra of `V`.
  Proof: the FLT theorem `exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation`.

## Models of factorizations

`Model f g j R`, for `f : X ⟶ Spec V`, `g : Y ⟶ Spec V` and `j : X ⟶ Y`, is a structure
with fields: models `MX` of `f` and `MY` of `g` over `R`; a morphism
`j₀ : MX.X₀ ⟶ MY.X₀`; a proof of `j₀ ≫ MY.f₀ = MX.f₀`; and a proof of
`j ≫ MY.π = MX.π ≫ j₀`.

- `Model.baseChange M hfac R'` (definition, needs `hfac : j ≫ g = f`): the base change of
  both scheme models, with `j₀` replaced by `pullback.map` of `j₀` and two identities.
- `Model.baseChange_MX_f₀`, `Model.baseChange_MY_f₀`: after base change the model
  morphisms are the second projections of the pullbacks along
  `Spec R' ⟶ Spec R` (by `rfl`).
- Instances `Model.smooth_baseChange`, `Model.isProper_baseChange` and
  `Model.isSeparated_baseChange`: smoothness of `MX.f₀`, and properness or separatedness
  of `MY.f₀`, are kept by `baseChange`. They are stable under base change.
- `Model.mono_pullbackMap_of_kernelPair`: let `j₀ ≫ g₀ = f₀` over `S` and `κ : S' ⟶ S`.
  Suppose the two projections of the kernel pair `X₀ ×_{Y₀} X₀` agree after base change
  along `κ`. Then the base change of `j₀` along `κ` is a monomorphism. Proof: for
  `c, d : W ⟶ X₀ ×_S S'` with equal images, form the induced map from `W` to the base
  change of the kernel pair. The hypothesis then forces the first components of `c` and
  `d` to agree, and their second components already agree.
- `Model.kernelPair_eq_of_mono` (needs `hfac` and `Mono j`): over `V` itself, the two
  projections of the kernel pair of `j₀` agree. Proof: a point of the base change of the
  kernel pair to `V` gives, through the pullback property of `MX`, two maps to `X` with
  the same composite with `j`. They are therefore equal because `j` is a monomorphism.
- Instance `Model.mono_baseChange`: if `j₀` is a monomorphism, so is the model of `j`
  after any further base change. Proof: by `mono_pullbackMap_of_kernelPair`, because the
  kernel-pair projections of a monomorphism are already equal.
- `Model.exists_of_models MX MY hfac`: models `MX` of `f` and `MY` of `g` over `R` give,
  over some finitely generated `R`-subalgebra `T` of `V`, a model of the factorization
  whose scheme models are `MX.baseChange T` and `MY.baseChange T`. Proof: transport `j`
  through the isomorphisms `IsPullback.isoPullback` to a morphism of base changes over
  `Spec V`. Then descend it by the FLT theorem
  `exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation`, whose
  uniqueness clause gives the compatibility `comm` after cancelling the isomorphism.

## Descending properties to the model

Each of the following lemmas takes a model `M` of `j ≫ g = f` over `R`. Each returns a
finitely generated `R`-subalgebra `T` of `V` over which `M.baseChange hfac T` has the
stated property.

- `Model.exists_smooth` (`f` smooth): `MX.f₀` becomes smooth. By the FLT theorem
  `Smooth.exists_fg_subalgebra_of_smooth_pullback_snd`, applied after
  `prop_pullback_snd`.
- `Model.exists_isSeparated` (`g` separated): `MY.f₀` becomes separated. By the FLT
  theorem `IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd`.
- `Model.exists_isProper` (`R` noetherian, `MY.f₀` separated, `g` proper): `MY.f₀` becomes
  proper. By the FLT theorem `IsProper.exists_fg_subalgebra_of_isProper_pullback_snd`.
- `Model.exists_mono` (`j` a monomorphism): `j₀` becomes a monomorphism. `j₀` is
  quasi-compact because `j₀ ≫ MY.f₀ = MX.f₀` is and `MY.f₀` is quasi-separated. The FLT
  theorem `exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType` descends the
  equality from `kernelPair_eq_of_mono` to some `T`, and `mono_pullbackMap_of_kernelPair`
  concludes.
- `finiteType_int_of_fg`: if `R` is of finite type over `ℤ` and `T` is a finitely
  generated `R`-subalgebra of `V`, then `T` is of finite type over `ℤ`
  (`Algebra.FiniteType.trans`).

## Main results

The stage lemmas `exists_model_of_isProper`, `exists_model_of_isSeparated`,
`exists_model_of_smooth`, `exists_model_of_model`, `exists_model_of_schemeModels` and
`exists_model_of_schemeModel` all have the conclusion of `exists_model`. Each one takes a
model over a ring `R` of finite type over `ℤ` that already has some of the required
properties. It applies one of the descent lemmas above over a finitely generated
`R`-subalgebra `T` and passes `M.baseChange hfac T` to the next stage. Properties already
established persist by the base-change instances. Each step passes through a fresh base
ring `R`. This avoids nested subalgebra types, for which Lean's instance synthesis fails.

- `exists_model`: let `f` be smooth and quasi-compact, `g` proper and locally of finite
  presentation, and `j` a monomorphism with `j ≫ g = f`. Then there are a ring `R` of
  finite type over `ℤ`, an `R`-algebra structure on `V`, and a model `M` of the
  factorization over `R`. In `M`, `MX.f₀` is smooth, `j₀` is a monomorphism and `MY.f₀` is
  proper. Proof: `f` is quasi-separated because `j ≫ g` is. Take a model of `f` over a
  finitely generated subalgebra of `V` over `⊥ : Subalgebra ℤ V`; the base ring must live
  in the universe of `V`, so `⊥` stands in for `ℤ`. Then run the stage lemmas: model of
  `g`, model of the factorization, smoothness, separatedness, properness (the base is
  noetherian since it is of finite type over `ℤ`), and finally monomorphism.
- `exists_normal_model`: if moreover `V` is an integrally closed domain, the model can be
  taken over a finitely generated, integrally closed `ℤ`-subalgebra `N` of `V`. Proof: let
  `R` be the ring from `exists_model`, generated over `ℤ` by a finite set `s`. The Library
  theorem `NoetherianApproximation.normalFiniteTypeSubalgebra` gives a finitely generated
  integrally closed `N` containing the image of `s`, hence the image of `R`. Make `N` an
  `R`-algebra by the corestricted map, so that `R → N → V` is a scalar tower. Then take
  `M.baseChange hfac N`.
