/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# Direct images of pullbacks from a separably closed field

Let `k` be a field, `Λ` a finite ring whose exponent is invertible in `k`, and consider a
cartesian square of separated `k`-schemes of finite type

```
  W --q--> X
  |        |
  pr       f
  v        v
  Y --c--> Spec k
```

The ordinary Künneth formula with an identity factor
(`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`, blueprint
`lemma-kunneth-one-identity-factor--1`) computes the direct image along `pr` of a complex pulled
back from `Y`:

`Rpr_* Lpr^* Q ≅ Lc^* Rf_* Λ_X ⊗ᴸ Q`

for every `Q ∈ Dctf(Y, Λ)`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_of_isPullback`).
If `k` is separably closed, `Rf_* Λ_X` is the constant complex on the cohomology `RΓ(X, Λ)`, so
`Rpr_* Lpr^* Q ≅ RΓ(X, Λ)_Y ⊗ᴸ Q`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_constantFunctor_of_isPullback`).
This is the form in which the cohomology of `𝔸¹` and `𝔾ₘ` over `k` is spread over a base `Y`
in `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineRelative`.

We also record that the derived pullback along an isomorphism is an equivalence, so that the unit
of `Le^* ⊣ Re_*` is invertible
(`AlgebraicGeometry.Etale.isIso_derivedUpperStarLowerStarAdjunction_unit_of_isIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Iso

variable {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e]

/-- The derived pullback along an isomorphism `e` is an equivalence, with inverse the derived
pullback along `e⁻¹`. -/
noncomputable def leftDerivedUpperStarEquivalenceOfIsIso :
    _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ≌
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  CategoryTheory.Equivalence.mk L((e)^*[ModuleCat.{u + 1} Λ]) L((inv e)^*[ModuleCat.{u + 1} Λ])
    ((leftDerivedUpperStarId _ Y).symm ≪≫
      leftDerivedUpperStarComp _ (inv e) e (𝟙 Y) (by simp))
    ((leftDerivedUpperStarComp _ e (inv e) (𝟙 X) (by simp)).symm ≪≫ leftDerivedUpperStarId _ X)

instance isEquivalence_leftDerivedUpperStar_of_isIso_of_equivalence :
    L((e)^*[ModuleCat.{u + 1} Λ]).IsEquivalence :=
  (leftDerivedUpperStarEquivalenceOfIsIso Λ e).isEquivalence_functor

/-- Along an isomorphism `e`, the unit `K ⟶ Re_* Le^* K` of the derived adjunction is
invertible. -/
instance isIso_derivedUpperStarLowerStarAdjunction_unit_of_isIso :
    IsIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e).unit :=
  inferInstance

/-- `Re_* Le^* K ≅ K` along an isomorphism `e`. -/
noncomputable def rightDerivedLowerStarLeftDerivedUpperStarIsoOfIsIso
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R((e)_*[ModuleCat.{u + 1} Λ])).obj ((L((e)^*[ModuleCat.{u + 1} Λ])).obj K) ≅ K :=
  (asIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e).unit.app K)).symm

end Iso

/-- The constant complex `Λ_X` lies in `Dctf(X, Λ)`: it is the constant sheaf `Λ` in degree
zero, constructible and flat. -/
theorem constructibleFiniteTor_constantComplex [IsNoetherianRing Λ] (X : Scheme.{u}) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (constantComplex Λ X) := by
  have hU : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X (𝟙_ _) :=
    (DerivedCategory.boundedConstructible _ X).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (DerivedCategory.boundedConstructible_singleFunctor_obj _ 0)
  have hUt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0 (𝟙_ _) :=
    (DerivedCategory.torAmplitudeIn _ X 0 0).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))
  exact ⟨hU, ⟨0, 0, hUt⟩⟩

section Kunneth

variable [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]

/-- The ordinary Künneth formula with an identity factor
(`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`) for a cartesian
square

```
  W --q--> X
  |        |
  pr       f
  v        v
  Y --c--> Spec k
```

of separated `k`-schemes of finite type and the constant complex on `X`: for `Q ∈ Dctf(Y, Λ)`,

`Rpr_* Lpr^* Q ≅ Lc^* Rf_* Λ_X ⊗ᴸ Q`. -/
theorem nonempty_iso_rightDerivedLowerStar_of_isPullback {X Y W : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {c : Y ⟶ Spec (.of k)} {q : W ⟶ X} {pr : W ⟶ Y}
    (sq : IsPullback q pr f c) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    {Q : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hQ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y Q) :
    Nonempty ((R((pr)_*[ModuleCat.{u + 1} Λ])).obj ((L((pr)^*[ModuleCat.{u + 1} Λ])).obj Q) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((L((c)^*[ModuleCat.{u + 1} Λ])).obj
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)))).obj Q) := by
  obtain ⟨κ⟩ := nonempty_iso_externalProduct_rightDerivedLowerStar Λ (𝟙 (Spec (.of k))) c f
    (constructibleFiniteTor_constantComplex Λ X) hQ
  -- the base `Spec k ×_k Y` of the Künneth formula is `Y`
  let e₀ := pullback.snd (𝟙 (Spec (.of k))) c
  have he₀ : pullback.fst (𝟙 (Spec (.of k))) c = e₀ ≫ c := by
    have := pullback.condition (f := 𝟙 (Spec (.of k))) (g := c)
    rwa [Category.comp_id] at this
  -- its total space `X ×_k Y` is `W`
  have sq' : IsPullback q pr (f ≫ 𝟙 _) c := by simpa using sq
  have hε : pullback.snd (f ≫ 𝟙 _) c = sq'.isoPullback.inv ≫ pr :=
    sq'.isoPullback_inv_snd.symm
  let m := pullback.mapOverBaseRight f (𝟙 (Spec (.of k))) c
  have hm : m ≫ e₀ = pullback.snd (f ≫ 𝟙 _) c := pullback.mapOverBaseRight_snd _ _ _
  let T := ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((L((c)^*[ModuleCat.{u + 1} Λ])).obj
    ((R((f)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)))).obj Q
  -- the left side of the Künneth formula is `Le₀^* T`
  let a : externalProduct (ModuleCat.{u + 1} Λ) (𝟙 _) c
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)) Q ≅
      (L((e₀)^*[ModuleCat.{u + 1} Λ])).obj T :=
    ((derivedTensor _ _).mapIso ((leftDerivedUpperStarComp _ e₀ c _ he₀).app _)).app _ ≪≫
      (leftDerivedUpperStarTensorIso _ e₀ _ _).symm
  -- the right side is `Rm_* L(snd)^* Q`
  let b : (R((m)_*[ModuleCat.{u + 1} Λ])).obj
      (externalProduct (ModuleCat.{u + 1} Λ) (f ≫ 𝟙 _) c (constantComplex Λ X) Q) ≅
      (R((m)_*[ModuleCat.{u + 1} Λ])).obj
        ((L((pullback.snd (f ≫ 𝟙 _) c)^*[ModuleCat.{u + 1} Λ])).obj Q) :=
    (R((m)_*[_])).mapIso (((derivedTensor _ _).mapIso
      (leftDerivedUpperStarConstantComplexIso Λ _)).app _ ≪≫ derivedTensorLeftUnitor _ _ _)
  exact ⟨((R((pr)_*[_])).mapIso ((R((sq'.isoPullback.inv)_*[_])).mapIso
      ((leftDerivedUpperStarComp _ sq'.isoPullback.inv pr _ hε).app Q) ≪≫
        rightDerivedLowerStarLeftDerivedUpperStarIsoOfIsIso Λ _ _)).symm ≪≫
    (rightDerivedLowerStarComp _ sq'.isoPullback.inv pr).app _ ≪≫
    (rightDerivedLowerStarCongr _ (hm.trans hε)).symm.app _ ≪≫
    ((rightDerivedLowerStarComp _ m e₀).app _).symm ≪≫
    (R((e₀)_*[_])).mapIso (a.symm ≪≫ κ ≪≫ b).symm ≪≫
    rightDerivedLowerStarLeftDerivedUpperStarIsoOfIsIso Λ e₀ T⟩

omit [Finite Λ] [HasInvertibleExponent Λ (Spec (.of k))] in
/-- Over a separably closed field `k`, the direct image of the constant complex along
`f : X ⟶ Spec k` is the constant complex on the cohomology: `Rf_* Λ_X ≅ RΓ(X, Λ)_{Spec k}`. -/
theorem nonempty_iso_rightDerivedLowerStar_constantComplex_of_isSepClosed [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    Nonempty ((R((f)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X) ≅
      (constantFunctor Λ (Spec (.of k))).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj (constantComplex Λ X))) := by
  obtain ⟨e⟩ := nonempty_iso_constantFunctor_rightDerivedGlobalSections_of_isSepClosed Λ
    ((R((f)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X))
  exact ⟨e ≪≫ (constantFunctor _ _).mapIso
    ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ f).app _)⟩

/-- The Künneth formula over a separably closed field `k`: in the cartesian square of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_of_isPullback`,

`Rpr_* Lpr^* Q ≅ RΓ(X, Λ)_Y ⊗ᴸ Q`

for every `Q ∈ Dctf(Y, Λ)`. -/
theorem nonempty_iso_rightDerivedLowerStar_constantFunctor_of_isPullback [IsSepClosed k]
    {X Y W : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {c : Y ⟶ Spec (.of k)} {q : W ⟶ X} {pr : W ⟶ Y}
    (sq : IsPullback q pr f c) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    {Q : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hQ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y Q) :
    Nonempty ((R((pr)_*[ModuleCat.{u + 1} Λ])).obj ((L((pr)^*[ModuleCat.{u + 1} Λ])).obj Q) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((constantFunctor Λ Y).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
          (constantComplex Λ X)))).obj Q) := by
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedLowerStar_of_isPullback Λ sq hQ
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedLowerStar_constantComplex_of_isSepClosed Λ f
  exact ⟨e₁ ≪≫ ((derivedTensor _ _).mapIso ((L((c)^*[_])).mapIso e₂ ≪≫
    (constantFunctorCompLeftDerivedUpperStarIso Λ c).app _)).app Q⟩

end Kunneth

section ConstantComplexes

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- The constant complex functor sends `Λ` in degree zero to the constant complex `Λ_Y`. -/
noncomputable def constantFunctorObjSingleIso (Y : Scheme.{u}) :
    (constantFunctor Λ Y).obj ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj
      (ModuleCat.of Λ Λ)) ≅ constantComplex Λ Y :=
  ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapDerivedCategorySingleFunctor
    0).app _ ≪≫ (constantComplexIsoSingleFunctor Λ Y).symm

instance projective_moduleCat_self : Projective (ModuleCat.of Λ Λ) :=
  ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{1} Λ)

variable {Λ} in
/-- A complex of `Λ`-modules whose cohomology is `Λ` in degree zero and vanishes in the other
degrees is `Λ` placed in degree zero. -/
theorem nonempty_iso_singleFunctor_of_homology
    (C : _root_.DerivedCategory (ModuleCat.{u + 1} Λ))
    (hC : ∀ q : ℤ, q ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj C))
    (e : (_root_.DerivedCategory.homologyFunctor _ 0).obj C ≅ ModuleCat.of Λ Λ) :
    Nonempty (C ≅ (_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj
      (ModuleCat.of Λ Λ)) := by
  obtain ⟨i⟩ := _root_.DerivedCategory.nonempty_iso_singleFunctor_obj_homologyFunctor_obj C 0 hC
  exact ⟨i ≪≫ (_root_.DerivedCategory.singleFunctor _ 0).mapIso e⟩
/-- In a preadditive category, `[f, g] : A ⊞ B ⟶ C` is an isomorphism if `f` is and `B` is
zero. -/
lemma isIso_biprod_desc_of_isZero_right {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    [HasBinaryBiproducts 𝒞] {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) [IsIso f] (hB : IsZero B) :
    IsIso (biprod.desc f g) :=
  ⟨⟨inv f ≫ biprod.inl, biprod.hom_ext' _ _ (by simp) (hB.eq_of_src _ _), by simp⟩⟩

/-- In a preadditive category, `[f, g] : A ⊞ B ⟶ C` is an isomorphism if `g` is and `A` is
zero. -/
lemma isIso_biprod_desc_of_isZero_left {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    [HasBinaryBiproducts 𝒞] {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) [IsIso g] (hA : IsZero A) :
    IsIso (biprod.desc f g) :=
  ⟨⟨inv g ≫ biprod.inr, biprod.hom_ext' _ _ (hA.eq_of_src _ _) (by simp), by simp⟩⟩

/-- An additive functor sends `[f, g]` to `[F f, F g]`, up to `F(A ⊞ B) ≅ F A ⊞ F B`. -/
lemma Functor.mapBiprod_inv_map_biprod_desc {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    [Preadditive 𝒞] [Preadditive 𝒟] [HasBinaryBiproducts 𝒞] [HasBinaryBiproducts 𝒟]
    (F : 𝒞 ⥤ 𝒟) [F.Additive] [PreservesBinaryBiproducts F] {A B C : 𝒞} (f : A ⟶ C)
    (g : B ⟶ C) :
    (F.mapBiprod A B).inv ≫ F.map (biprod.desc f g) = biprod.desc (F.map f) (F.map g) := by
  ext <;> simp [← F.map_comp]

variable {Λ} in
/-- A complex of `Λ`-modules whose cohomology is `Λ` in degrees zero and one and vanishes in the
other degrees is `Λ ⊕ Λ[-1]`. -/
theorem nonempty_iso_biprod_singleFunctor_of_homology
    (C : _root_.DerivedCategory (ModuleCat.{u + 1} Λ))
    (hC : ∀ q : ℤ, q ≠ 0 → q ≠ 1 →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj C))
    (e₀ : (_root_.DerivedCategory.homologyFunctor _ 0).obj C ≅ ModuleCat.of Λ Λ)
    (e₁ : (_root_.DerivedCategory.homologyFunctor _ 1).obj C ≅ ModuleCat.of Λ Λ) :
    Nonempty (C ≅ (_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj
      (ModuleCat.of Λ Λ) ⊞ (_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 1).obj
        (ModuleCat.of Λ Λ)) := by
  let P := ModuleCat.of Λ Λ
  let S := _root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ)
  let H := _root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ)
  let α := (_root_.DerivedCategory.homSingleEquivOfProjective P 0 C).symm e₀.inv
  let β := (_root_.DerivedCategory.homSingleEquivOfProjective P 1 C).symm e₁.inv
  have hα : IsIso ((H 0).map α) := by
    have h := (_root_.DerivedCategory.homSingleEquivOfProjective P 0 C).apply_symm_apply e₀.inv
    rw [_root_.DerivedCategory.homSingleEquivOfProjective_apply,
      _root_.DerivedCategory.homSingleToHomology, Iso.inv_comp_eq] at h
    rw [show (H 0).map α = _ from h]
    infer_instance
  have hβ : IsIso ((H 1).map β) := by
    have h := (_root_.DerivedCategory.homSingleEquivOfProjective P 1 C).apply_symm_apply e₁.inv
    rw [_root_.DerivedCategory.homSingleEquivOfProjective_apply,
      _root_.DerivedCategory.homSingleToHomology, Iso.inv_comp_eq] at h
    rw [show (H 1).map β = _ from h]
    infer_instance
  have hS : ∀ (n q : ℤ), q ≠ n → IsZero ((H q).obj ((S n).obj P)) := fun n q hq ↦
    _root_.DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor (Iso.refl _) hq
  have : IsIso (biprod.desc α β) := by
    rw [_root_.DerivedCategory.isIso_iff]
    intro q
    rw [← (isIso_comp_left_iff ((H q).mapBiprod _ _).inv), Functor.mapBiprod_inv_map_biprod_desc]
    by_cases h0 : q = 0
    · subst h0
      exact isIso_biprod_desc_of_isZero_right _ _ (hS 1 0 (by omega))
    by_cases h1 : q = 1
    · subst h1
      exact isIso_biprod_desc_of_isZero_left _ _ (hS 0 1 (by omega))
    exact ⟨⟨0, ((biprod_isZero_iff _ _).2 ⟨hS 0 q h0, hS 1 q h1⟩).eq_of_src _ _,
      (hC q h0 h1).eq_of_src _ _⟩⟩
  exact ⟨(asIso (biprod.desc α β)).symm⟩

end ConstantComplexes

end Etale

end AlgebraicGeometry
