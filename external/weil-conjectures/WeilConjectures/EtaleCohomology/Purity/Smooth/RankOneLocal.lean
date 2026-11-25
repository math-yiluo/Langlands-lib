/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologyHom
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerOrientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyHom
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField

/-!
# Cohomology with supports and the exceptional inverse image of a closed immersion

For a closed immersion `i : Z ⟶ X` the cohomology with supports `H^a_Z(X, K)` of
`AlgebraicGeometry.Etale.derivedSupportCohomology` is `Hom(Λ_Z, Ri^!(K[a]))`
(`AlgebraicGeometry.Etale.supportCohomologyAddEquiv`): by `H^a_Z(X, K) ≅ Hom(i_* Λ_Z, K[a])`
(`AlgebraicGeometry.Etale.derivedSupportCohomologyAddEquiv`), `i_* Λ_Z ≅ Ri_! Λ_Z` and the
adjunction `Ri_! ⊣ Ri^!`. This identification is `Λ`-linear
(`AlgebraicGeometry.Etale.supportCohomologyLinearEquiv`), as `H^a_Z(X, -)` is `Λ`-linear
(`AlgebraicGeometry.Etale.linear_derivedSupportCohomology`).

A morphism `g : Λ_Z ⟶ R` gives a global section of `H⁰(R)`, the image of `1` under
`H⁰(g) : Λ = H⁰(Λ_Z) ⟶ H⁰(R)` (`AlgebraicGeometry.Etale.homConstantComplexLinearMapΓHomologyZero`);
this is bijective when `R` is concentrated in degree zero.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- `H⁰` is bijective on morphisms between objects of `D(C)` that are isomorphic to objects
placed in degree zero. -/
lemma bijective_homologyFunctor_map_of_iso_singleFunctor {X Y : DerivedCategory C} {A B : C}
    (eX : X ≅ (singleFunctor C 0).obj A) (eY : Y ≅ (singleFunctor C 0).obj B) :
    Function.Bijective (fun f : X ⟶ Y ↦ (homologyFunctor C 0).map f) := by
  have hS (g : A ⟶ B) : (homologyFunctor C 0).map ((singleFunctor C 0).map g) =
      (singleFunctorCompHomologyFunctorIso C 0).hom.app A ≫ g ≫
        (singleFunctorCompHomologyFunctorIso C 0).inv.app B :=
    (NatIso.naturality_2 (singleFunctorCompHomologyFunctorIso C 0) g).symm
  refine ⟨fun f f' h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨g, hg⟩ := (singleFunctor C 0).map_surjective (eX.inv ≫ f ≫ eY.hom)
    obtain ⟨g', hg'⟩ := (singleFunctor C 0).map_surjective (eX.inv ≫ f' ≫ eY.hom)
    simp only at h
    have h₁ := hS g
    have h₂ := hS g'
    rw [hg, Functor.map_comp, Functor.map_comp] at h₁
    rw [hg', Functor.map_comp, Functor.map_comp, ← h, h₁] at h₂
    have hgg : g = g' := by
      simpa using congrArg (fun φ ↦ (singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫ φ ≫
        (singleFunctorCompHomologyFunctorIso C 0).hom.app B) h₂
    have h₃ : eX.inv ≫ f ≫ eY.hom = eX.inv ≫ f' ≫ eY.hom := by rw [← hg, ← hg', hgg]
    simpa using congrArg (fun φ ↦ eX.hom ≫ φ ≫ eY.inv) h₃
  · obtain ⟨g, hg⟩ : ∃ g : A ⟶ B, g = (singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
        (homologyFunctor C 0).map eX.inv ≫ h ≫ (homologyFunctor C 0).map eY.hom ≫
          (singleFunctorCompHomologyFunctorIso C 0).hom.app B := ⟨_, rfl⟩
    refine ⟨eX.hom ≫ (singleFunctor C 0).map g ≫ eY.inv, ?_⟩
    dsimp only
    rw [Functor.map_comp, Functor.map_comp, hS, hg]
    simp

end DerivedCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section SupportHom

variable [Finite Λ] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- `Ri_! Λ_Z ≅ i_* Λ_Z`, placed in degree zero, for a closed immersion `i`. -/
noncomputable def rightDerivedLowerShriekConstantComplexIso :
    (R(i)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj ((i)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))) :=
  (rightDerivedLowerShriekIsoRightDerivedLowerStar _ i).app _ ≪≫
    (rightDerivedFunctorLowerStarIsoMapDerivedCategory _ i).app _ ≪≫
    ((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.mapIso (constantComplexIsoSingleFunctor Λ Z) ≪≫
    (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _

/-- Blueprint `lem-pur-gysin-structure`: Structure of the exceptional inverse image of the zero
section (the identification of cohomology with supports with morphisms into `Ri^!`).

For a closed immersion `i : Z ⟶ X`, the cohomology with supports is
`H^a_Z(X, K) ≅ Hom(Λ_Z, Ri^!(K[a]))`. -/
noncomputable def supportCohomologyAddEquiv
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ) :
    (derivedSupportCohomology (ModuleCat.{u + 1} Λ) i a).obj K ≃+
      (constantComplex Λ Z ⟶ (R(i)^![Λ]).obj (K⟦a⟧)) :=
  (derivedSupportCohomologyAddEquiv Λ i K a).trans
    ((AddEquiv.mk ((rightDerivedLowerShriekConstantComplexIso Λ i).homCongr
      (Iso.refl (K⟦a⟧))).symm (fun f g ↦ by simp [Iso.homCongr])).trans
      ((rightDerivedUpperShriekAdjunction Λ i).homAddEquiv _ _))

end SupportHom

section Linear

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The derived sections with support `RΓ_Z(X, -)` are `Λ`-linear: they are `RΓ(Z, Ri^! -)`
(`AlgebraicGeometry.Etale.rightDerivedClosedUpperShriekCompIso`), and both factors are right
adjoints of `Λ`-linear functors. -/
instance linear_rightDerivedSectionsWithSupport :
    (rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) i).Linear Λ := by
  have := (lowerStarClosedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i i.openComplement.ι
    i.range_eq_compl_range_openComplement_ι).mapDerivedCategoryRightDerivedAdjunction
      |>.right_adjoint_linear (R := Λ)
  have := (constantSheafΓAdj Z.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).mapDerivedCategoryRightDerivedAdjunction.right_adjoint_linear (R := Λ)
  exact Functor.linear_of_iso Λ (rightDerivedClosedUpperShriekCompIso _ i)

/-- The cohomology with support `H^a_Z(X, -)` is `Λ`-linear. -/
instance linear_derivedSupportCohomology (a : ℤ) :
    (derivedSupportCohomology (ModuleCat.{u + 1} Λ) i a).Linear Λ :=
  inferInstanceAs ((rightDerivedSectionsWithSupport (ModuleCat.{u + 1} Λ) i ⋙
    _root_.DerivedCategory.homologyFunctor _ a).Linear Λ)

/-- Naturality of `H^a_Z(X, K) ≅ Hom(i_* Λ_Z, K[a])` in `K`. -/
lemma derivedSupportCohomologyAddEquiv_map
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : K ⟶ K') (a : ℤ) (x : (derivedSupportCohomology (ModuleCat.{u + 1} Λ) i a).obj K) :
    derivedSupportCohomologyAddEquiv Λ i K' a
        (((derivedSupportCohomology (ModuleCat.{u + 1} Λ) i a).map f).hom x) =
      derivedSupportCohomologyAddEquiv Λ i K a x ≫ f⟦a⟧' := by
  have h := ConcreteCategory.congr_hom
    ((shiftFunctorCompPreadditiveCoyonedaLowerStarConstantIso Λ i a).inv.naturality f) x
  exact h

/-- `H^a_Z(X, K) ≅ Hom(i_* Λ_Z, K[a])` is `Λ`-linear. -/
lemma derivedSupportCohomologyAddEquiv_smul
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ)
    (c : Λ) (x : (derivedSupportCohomology (ModuleCat.{u + 1} Λ) i a).obj K) :
    derivedSupportCohomologyAddEquiv Λ i K a (c • x) =
      c • derivedSupportCohomologyAddEquiv Λ i K a x := by
  have hx : c • x =
      ((derivedSupportCohomology (ModuleCat.{u + 1} Λ) i a).map (c • 𝟙 K)).hom x := by
    simp [Functor.map_smul]
  rw [hx, derivedSupportCohomologyAddEquiv_map, Functor.map_smul,
    CategoryTheory.Functor.map_id, Linear.comp_smul, Category.comp_id]

/-- Blueprint `lem-pur-gysin-structure`: Structure of the exceptional inverse image of the zero
section (the identification of cohomology with supports with morphisms into `Ri^!`,
`Λ`-linearly).

For a closed immersion `i : Z ⟶ X`, the `Λ`-linear isomorphism
`H^a_Z(X, K) ≅ Hom(Λ_Z, Ri^!(K[a]))` underlying
`AlgebraicGeometry.Etale.supportCohomologyAddEquiv`. -/
noncomputable def supportCohomologyLinearEquiv [Finite Λ]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ) :
    (derivedSupportCohomology (ModuleCat.{u + 1} Λ) i a).obj K ≃ₗ[Λ]
      (constantComplex Λ Z ⟶ (R(i)^![Λ]).obj (K⟦a⟧)) where
  __ := supportCohomologyAddEquiv Λ i K a
  map_smul' c x := by
    simp [supportCohomologyAddEquiv, derivedSupportCohomologyAddEquiv_smul, Iso.homCongr,
      Adjunction.homEquiv_unit]

@[simp]
lemma supportCohomologyLinearEquiv_toAddEquiv [Finite Λ]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ) :
    (supportCohomologyLinearEquiv Λ i K a).toAddEquiv = supportCohomologyAddEquiv Λ i K a :=
  rfl

@[simp]
lemma supportCohomologyLinearEquiv_apply [Finite Λ]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ)
    (x : (derivedSupportCohomology (ModuleCat.{u + 1} Λ) i a).obj K) :
    supportCohomologyLinearEquiv Λ i K a x = supportCohomologyAddEquiv Λ i K a x :=
  rfl

@[simp]
lemma supportCohomologyLinearEquiv_symm_apply [Finite Λ]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ)
    (g : constantComplex Λ Z ⟶ (R(i)^![Λ]).obj (K⟦a⟧)) :
    (supportCohomologyLinearEquiv Λ i K a).symm g = (supportCohomologyAddEquiv Λ i K a).symm g :=
  rfl

end Linear

section Endomorphisms

variable {Z : Scheme.{u}}

/-- On a connected scheme, the endomorphisms of the constant complex `Λ_Z` are the scalars. -/
theorem bijective_smul_id_constantComplex [Finite Λ] [ConnectedSpace Z] :
    Function.Bijective (fun c : Λ ↦ c • 𝟙 (constantComplex Λ Z)) := by
  let S := _root_.DerivedCategory.singleFunctor (Sheaf Z.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0
  let P := (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)
  let e : constantComplex Λ Z ≅ S.obj P := constantComplexIsoSingleFunctor Λ Z
  have hS : ∀ c : Λ, c • 𝟙 (constantComplex Λ Z) = e.hom ≫ S.map (c • 𝟙 P) ≫ e.inv := by
    intro c
    rw [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, e.hom_inv_id]
  constructor
  · intro c c' h
    simp only at h
    rw [hS, hS] at h
    have h' : S.map (c • 𝟙 P) = S.map (c' • 𝟙 P) := by
      simpa using congrArg (fun φ ↦ e.inv ≫ φ ≫ e.hom) h
    have h'' := S.map_injective h'
    have hz : (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
        ((c - c') • 𝟙 (ModuleCat.of Λ Λ)) = 0 := by
      rw [Functor.map_smul, CategoryTheory.Functor.map_id, sub_smul]
      exact sub_eq_zero.2 h''
    have := (ConnectedSpace.toNonempty (α := Z))
    have h0 := eq_zero_of_constantSheaf_map_eq_zero Λ _ hz
    have h1 := congrArg (fun φ : ModuleCat.of Λ Λ ⟶ ModuleCat.of Λ Λ ↦ φ.hom (1 : Λ)) h0
    simp only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_apply,
      smul_eq_mul, mul_one, ModuleCat.hom_zero, LinearMap.zero_apply] at h1
    exact sub_eq_zero.1 h1
  · intro f
    obtain ⟨c, hc⟩ := exists_eq_smul_id_constantSheaf Λ (S.preimage (e.inv ≫ f ≫ e.hom))
    refine ⟨c, ?_⟩
    simp only
    rw [hS, ← hc, S.map_preimage]
    simp

end Endomorphisms

section HomologyZero

variable {Z : Scheme.{u}}

/-- A morphism `g : Λ_Z ⟶ R` gives the global section of `H⁰(R)` which is the image of `1` under
`H⁰(g) : Λ = H⁰(Λ_Z) ⟶ H⁰(R)` (`AlgebraicGeometry.Etale.homologyZeroConstantComplexIso`), read
through the adjunction `Λ_Z ⊣ Γ(Z, -)`. -/
noncomputable def homConstantComplexLinearMapΓHomologyZero
    (R : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (constantComplex Λ Z ⟶ R) →ₗ[Λ] (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj
      ((_root_.DerivedCategory.homologyFunctor _ 0).obj R) where
  toFun g := ((constantSheafΓAdj Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).homEquiv _ _
    ((homologyZeroConstantComplexIso Λ Z).inv ≫
      (_root_.DerivedCategory.homologyFunctor _ 0).map g)).hom 1
  map_add' g g' := by simp [Adjunction.homEquiv_unit]
  map_smul' c g := by simp [Adjunction.homEquiv_unit, Functor.map_smul]

@[simp]
lemma homConstantComplexLinearMapΓHomologyZero_apply
    (R : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (g : constantComplex Λ Z ⟶ R) :
    homConstantComplexLinearMapΓHomologyZero Λ R g =
      ((constantSheafΓAdj Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).homEquiv _ _
        ((homologyZeroConstantComplexIso Λ Z).inv ≫
          (_root_.DerivedCategory.homologyFunctor _ 0).map g)).hom 1 :=
  rfl

/-- `AlgebraicGeometry.Etale.homConstantComplexLinearMapΓHomologyZero` is bijective when `R` is
isomorphic to a sheaf placed in degree zero. -/
lemma bijective_homConstantComplexLinearMapΓHomologyZero
    {R : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {B : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (e : R ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj B) :
    Function.Bijective (homConstantComplexLinearMapΓHomologyZero Λ R) := by
  have h : ⇑(homConstantComplexLinearMapΓHomologyZero Λ R) =
      ModuleCat.homSelfLinearEquiv Λ _ ∘
        (constantSheafΓAdj Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).homEquiv _ _ ∘
          (homologyZeroConstantComplexIso Λ Z).homCongr (Iso.refl _) ∘
            fun g ↦ (_root_.DerivedCategory.homologyFunctor _ 0).map g := by
    funext g
    simp [homConstantComplexLinearMapΓHomologyZero, Iso.homCongr, ModuleCat.homSelfLinearEquiv]
  rw [h]
  exact (ModuleCat.homSelfLinearEquiv Λ _).bijective.comp
    (((constantSheafΓAdj Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).homEquiv _ _).bijective.comp
      (((homologyZeroConstantComplexIso Λ Z).homCongr (Iso.refl _)).bijective.comp
        (_root_.DerivedCategory.bijective_homologyFunctor_map_of_iso_singleFunctor
          (constantComplexIsoSingleFunctor Λ Z) e)))

end HomologyZero

end Etale

end AlgebraicGeometry
