/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RelativeInjectiveResolution
public import WeilConjectures.Algebra.Homology.ShortComplex.HomologyToMap
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.ResolutionNaturality
public import WeilConjectures.AlgebraicGeometry.Cohomology.Flasque
public import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque

/-!
# The base change morphism of the higher direct images

Consider a commutative square of schemes
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
an `𝒪_X`-module `ℱ`, an `𝒪_{X'}`-module `ℱ'` and a morphism `θ : ℱ ⟶ g'_* ℱ'` (typically the
unit `ℱ ⟶ g'_* g'^* ℱ`). We construct the **base change morphism**
`R^i f_* ℱ ⟶ g_* R^i f'_* ℱ'` (`AlgebraicGeometry.Scheme.Modules.higherDirectImageBaseChange`).

It is computed by any *base change datum* (`AlgebraicGeometry.Scheme.Modules.BaseChangeData`):
a resolution `ℱ ⟶ P` by `f_*`-acyclic modules, a resolution `ℱ' ⟶ Q` by `f'_*`-acyclic modules
and a cochain map `u : P ⟶ g'_* Q` extending `θ`. The morphism is then the composite
`R^i f_* ℱ ≅ H^i(f_* P) ⟶ H^i(f_* g'_* Q) ≅ H^i(g_* f'_* Q) ⟶ g_* H^i(f'_* Q) ≅ g_* R^i f'_* ℱ'`,
and it does not depend on the datum
(`AlgebraicGeometry.Scheme.Modules.BaseChangeData.map_eq`): two data are compared through the
resolution of `ℱ` over `g'_* J` for an injective resolution `J` of `ℱ'`
(`CochainComplex.OverResolution`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T X' T' : Scheme.{u}} {f : X ⟶ T} {g : T' ⟶ T} {g' : X' ⟶ X} {f' : X' ⟶ T'}

/-- The identification `f_* ∘ g'_* ≅ g_* ∘ f'_*` for a commutative square `g' ≫ f = f' ≫ g`. -/
noncomputable def pushforwardSquareIso (w : g' ≫ f = f' ≫ g) :
    pushforward g' ⋙ pushforward f ≅ pushforward f' ⋙ pushforward g :=
  pushforwardComp g' f ≪≫ pushforwardCongr w ≪≫ (pushforwardComp f' g).symm

variable [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]

variable (f g' f') in
/-- A **base change datum** for a morphism `θ : ℱ ⟶ g'_* ℱ'`: a resolution `ℱ ⟶ P` by
`f_*`-acyclic modules, a resolution `ℱ' ⟶ Q` by `f'_*`-acyclic modules and a cochain map
`u : P ⟶ g'_* Q` extending `θ`. -/
structure BaseChangeData {ℱ : X.Modules} {ℱ' : X'.Modules} (θ : ℱ ⟶ (pushforward g').obj ℱ') where
  /-- The resolution of `ℱ`. -/
  P : CochainComplex X.Modules ℕ
  /-- The augmentation of `P`. -/
  ε : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ P
  [quasiIso_ε : QuasiIso ε]
  rightAcyclic_P (n : ℕ) : (pushforward f).rightAcyclic (P.X n)
  /-- The resolution of `ℱ'`. -/
  Q : CochainComplex X'.Modules ℕ
  /-- The augmentation of `Q`. -/
  η : (CochainComplex.single₀ X'.Modules).obj ℱ' ⟶ Q
  [quasiIso_η : QuasiIso η]
  rightAcyclic_Q (n : ℕ) : (pushforward f').rightAcyclic (Q.X n)
  /-- The cochain map `P ⟶ g'_* Q`. -/
  u : P ⟶ ((pushforward g').mapHomologicalComplex _).obj Q
  comm : ε.f 0 ≫ u.f 0 = θ ≫ (pushforward g').map (η.f 0)

attribute [instance] BaseChangeData.quasiIso_ε BaseChangeData.quasiIso_η

section OfResolutions

variable {ℱ : X.Modules} {ℱ' : X'.Modules} {P : CochainComplex X.Modules ℕ}
  (ε : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ P) [QuasiIso ε]
  (hP : ∀ n, (pushforward f).rightAcyclic (P.X n)) {Q : CochainComplex X'.Modules ℕ}
  (η : (CochainComplex.single₀ X'.Modules).obj ℱ' ⟶ Q) [QuasiIso η]
  (hQ : ∀ n, (pushforward f').rightAcyclic (Q.X n))

/-- The base change morphism `R^i f_* ℱ ⟶ g_* R^i f'_* ℱ'` computed by resolutions `P` of `ℱ`
and `Q` of `ℱ'` and a cochain map `u : P ⟶ g'_* Q`. -/
noncomputable def baseChangeOfResolutions (w : g' ≫ f = f' ≫ g)
    (u : P ⟶ ((pushforward g').mapHomologicalComplex _).obj Q) (i : ℕ) :
    (higherDirectImage f i).obj ℱ ⟶ (pushforward g).obj ((higherDirectImage f' i).obj ℱ') :=
  ((pushforward f).rightDerivedObjIsoOfResolution ε hP i).hom ≫
    HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map u) i ≫
    HomologicalComplex.homologyMap
      ((NatIso.mapHomologicalComplex (pushforwardSquareIso w) _).hom.app Q) i ≫
    HomologicalComplex.homologyToMap (pushforward g)
      (((pushforward f').mapHomologicalComplex _).obj Q) i ≫
    (pushforward g).map ((pushforward f').rightDerivedObjIsoOfResolution η hQ i).inv

/-- The base change morphism does not change along a cochain map `Q₁ ⟶ Q₂` over `ℱ'`. -/
lemma baseChangeOfResolutions_comp (w : g' ≫ f = f' ≫ g)
    (u : P ⟶ ((pushforward g').mapHomologicalComplex _).obj Q)
    {Q₂ : CochainComplex X'.Modules ℕ} (η₂ : (CochainComplex.single₀ X'.Modules).obj ℱ' ⟶ Q₂)
    [QuasiIso η₂] (hQ₂ : ∀ n, (pushforward f').rightAcyclic (Q₂.X n)) (v : Q ⟶ Q₂)
    (hv : η ≫ v = η₂) (i : ℕ) :
    baseChangeOfResolutions ε hP η₂ hQ₂ w (u ≫ ((pushforward g').mapHomologicalComplex _).map v) i =
      baseChangeOfResolutions ε hP η hQ w u i := by
  have hnat := (pushforward f').rightDerivedObjIsoOfResolution_hom_naturality η η₂ hQ hQ₂ (𝟙 ℱ') v
    (by rw [← hv, HomologicalComplex.comp_f, Category.id_comp]) i
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hnat
  have s1 : HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map
      (u ≫ ((pushforward g').mapHomologicalComplex _).map v)) i =
      HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map u) i ≫
        HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map
          (((pushforward g').mapHomologicalComplex _).map v)) i := by
    rw [Functor.map_comp, HomologicalComplex.homologyMap_comp]
  have s2 : HomologicalComplex.homologyMap (((pushforward f).mapHomologicalComplex _).map
        (((pushforward g').mapHomologicalComplex _).map v)) i ≫
      HomologicalComplex.homologyMap
        ((NatIso.mapHomologicalComplex (pushforwardSquareIso w) _).hom.app Q₂) i =
      HomologicalComplex.homologyMap
        ((NatIso.mapHomologicalComplex (pushforwardSquareIso w) _).hom.app Q) i ≫
      HomologicalComplex.homologyMap (((pushforward g).mapHomologicalComplex _).map
        (((pushforward f').mapHomologicalComplex _).map v)) i := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    congr 1
    exact (NatIso.mapHomologicalComplex (pushforwardSquareIso w) (ComplexShape.up ℕ)).hom.naturality
      v
  have s3 := HomologicalComplex.homologyMap_homologyToMap (pushforward g)
    (((pushforward f').mapHomologicalComplex _).map v) i
  have s4 : (pushforward g).map (HomologicalComplex.homologyMap
      (((pushforward f').mapHomologicalComplex _).map v) i) ≫
      (pushforward g).map ((pushforward f').rightDerivedObjIsoOfResolution η₂ hQ₂ i).inv =
      (pushforward g).map ((pushforward f').rightDerivedObjIsoOfResolution η hQ i).inv := by
    rw [← Functor.map_comp]
    congr 1
    rw [Iso.comp_inv_eq, Iso.eq_inv_comp, hnat]
  simp only [baseChangeOfResolutions]
  rw [s1, Category.assoc, reassoc_of% s2, reassoc_of% s3, s4]

/-- The base change morphism does not change along a cochain map `P₁ ⟶ P₂` over `ℱ`. -/
lemma baseChangeOfResolutions_of_comp (w : g' ≫ f = f' ≫ g)
    {P₂ : CochainComplex X.Modules ℕ} (ε₂ : (CochainComplex.single₀ X.Modules).obj ℱ ⟶ P₂)
    [QuasiIso ε₂] (hP₂ : ∀ n, (pushforward f).rightAcyclic (P₂.X n)) (a : P ⟶ P₂)
    (ha : ε ≫ a = ε₂) (u : P₂ ⟶ ((pushforward g').mapHomologicalComplex _).obj Q) (i : ℕ) :
    baseChangeOfResolutions ε hP η hQ w (a ≫ u) i =
      baseChangeOfResolutions ε₂ hP₂ η hQ w u i := by
  have hnat := (pushforward f).rightDerivedObjIsoOfResolution_hom_naturality ε ε₂ hP hP₂ (𝟙 ℱ) a
    (by rw [← ha, HomologicalComplex.comp_f, Category.id_comp]) i
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hnat
  simp only [baseChangeOfResolutions, Functor.map_comp, HomologicalComplex.homologyMap_comp,
    Category.assoc]
  rw [← reassoc_of% hnat]

end OfResolutions

variable {ℱ : X.Modules} {ℱ' : X'.Modules} {θ : ℱ ⟶ (pushforward g').obj ℱ'}

/-- The base change morphism `R^i f_* ℱ ⟶ g_* R^i f'_* ℱ'` computed by a base change datum. -/
noncomputable def BaseChangeData.map (D : BaseChangeData f g' f' θ) (w : g' ≫ f = f' ≫ g)
    (i : ℕ) :
    (higherDirectImage f i).obj ℱ ⟶ (pushforward g).obj ((higherDirectImage f' i).obj ℱ') :=
  baseChangeOfResolutions D.ε D.rightAcyclic_P D.η D.rightAcyclic_Q w D.u i

/-- The augmentation `ℱ ⟶ g'_* J⁰` for an injective resolution `J` of `ℱ'`. -/
noncomputable def baseChangeAugmentation (θ : ℱ ⟶ (pushforward g').obj ℱ')
    (J : InjectiveResolution ℱ') :
    ℱ ⟶ (((pushforward g').mapHomologicalComplex _).obj J.cocomplex).X 0 :=
  θ ≫ (pushforward g').map (J.ι.f 0)

omit [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules] in
lemma baseChangeAugmentation_d (θ : ℱ ⟶ (pushforward g').obj ℱ') (J : InjectiveResolution ℱ') :
    baseChangeAugmentation θ J ≫
      (((pushforward g').mapHomologicalComplex _).obj J.cocomplex).d 0 1 = 0 := by
  rw [baseChangeAugmentation, Category.assoc]
  erw [← Functor.map_comp, J.ι_f_zero_comp_complex_d]
  rw [Functor.map_zero, comp_zero]

omit [HasInjectiveResolutions X'.Modules] in
lemma rightAcyclic_pushforward_injective (I : X'.Modules) [Injective I] :
    (pushforward f).rightAcyclic ((pushforward g').obj I) :=
  rightAcyclic_pushforward_of_isFlasque f _
    (isFlasque_pushforward g' _ (isFlasque_of_injective I))

/-- The resolution of `ℱ` over `g'_* J`, for an injective resolution `J` of `ℱ'`. -/
noncomputable abbrev baseChangeResolution (θ : ℱ ⟶ (pushforward g').obj ℱ')
    (J : InjectiveResolution ℱ') : CochainComplex X.Modules ℕ :=
  have := (isGrothendieckAbelian X).enoughInjectives
  CochainComplex.OverResolution _ (baseChangeAugmentation θ J) (baseChangeAugmentation_d θ J)

omit [HasInjectiveResolutions X'.Modules] in
lemma rightAcyclic_baseChangeResolution (θ : ℱ ⟶ (pushforward g').obj ℱ')
    (J : InjectiveResolution ℱ') (n : ℕ) :
    (pushforward f).rightAcyclic ((baseChangeResolution θ J).X n) := by
  have := (isGrothendieckAbelian X).enoughInjectives
  obtain ⟨E, _, ⟨e⟩⟩ := CochainComplex.OverResolution.exists_iso_biprod _
    (baseChangeAugmentation θ J) (baseChangeAugmentation_d θ J) n
  exact (pushforward f).rightAcyclic.prop_of_iso e.symm
    (Functor.rightAcyclic_biprod (Functor.rightAcyclic_of_injective E)
      (rightAcyclic_pushforward_injective _))

/-- The base change datum built from the resolution over `g'_* J`, for an injective resolution
`J` of `ℱ'`. -/
noncomputable def baseChangeDataOfInjective (θ : ℱ ⟶ (pushforward g').obj ℱ')
    (J : InjectiveResolution ℱ') : BaseChangeData f g' f' θ :=
  have := (isGrothendieckAbelian X).enoughInjectives
  { P := baseChangeResolution θ J
    ε := CochainComplex.OverResolution.ι _ _ _
    rightAcyclic_P := rightAcyclic_baseChangeResolution θ J
    Q := J.cocomplex
    η := J.ι
    rightAcyclic_Q := fun _ ↦ Functor.rightAcyclic_of_injective _
    u := CochainComplex.OverResolution.c _ _ _
    comm := CochainComplex.OverResolution.ι_f_zero_c_f_zero _ _ _ }

/-- **The base change morphism does not depend on the datum.** -/
theorem BaseChangeData.map_eq (D₁ D₂ : BaseChangeData f g' f' θ) (w : g' ≫ f = f' ≫ g)
    (i : ℕ) : D₁.map w i = D₂.map w i := by
  have := (isGrothendieckAbelian X).enoughInjectives
  let J := injectiveResolution ℱ'
  -- move both data to the injective resolution `J`
  have key (D : BaseChangeData f g' f' θ) :
      D.map w i = (baseChangeDataOfInjective θ J).map w i := by
    let v := InjectiveResolution.descOfQuasiIso (𝟙 ℱ') J D.η
    have hv : D.η ≫ v = J.ι := by
      rw [InjectiveResolution.descOfQuasiIso_commutes, CategoryTheory.Functor.map_id,
        Category.id_comp]
    rw [BaseChangeData.map, ← baseChangeOfResolutions_comp D.ε D.rightAcyclic_P D.η
      D.rightAcyclic_Q w D.u J.ι (fun _ ↦ Functor.rightAcyclic_of_injective _) v hv]
    have hu : D.ε.f 0 ≫ (D.u ≫ ((pushforward g').mapHomologicalComplex _).map v).f 0 =
        baseChangeAugmentation θ J := by
      rw [HomologicalComplex.comp_f, reassoc_of% D.comm, baseChangeAugmentation]
      erw [← Functor.map_comp, ← HomologicalComplex.comp_f, hv]
    rw [← CochainComplex.OverResolution.lift_c D.ε _ hu,
      baseChangeOfResolutions_of_comp D.ε D.rightAcyclic_P J.ι _ w _
        (rightAcyclic_baseChangeResolution θ J) _ (CochainComplex.OverResolution.comp_lift _ _ hu)]
    rfl
  rw [key D₁, key D₂]

variable (ℱ ℱ' θ) in
/-- **The base change morphism** `R^i f_* ℱ ⟶ g_* R^i f'_* ℱ'` of the higher direct images for
a commutative square `g' ≫ f = f' ≫ g` and a morphism `θ : ℱ ⟶ g'_* ℱ'`. It is computed by any
base change datum (`AlgebraicGeometry.Scheme.Modules.BaseChangeData.map_eq`). -/
noncomputable def higherDirectImageBaseChange (w : g' ≫ f = f' ≫ g) (i : ℕ) :
    (higherDirectImage f i).obj ℱ ⟶ (pushforward g).obj ((higherDirectImage f' i).obj ℱ') :=
  (baseChangeDataOfInjective θ (injectiveResolution ℱ')).map w i

lemma BaseChangeData.map_eq_higherDirectImageBaseChange (D : BaseChangeData f g' f' θ)
    (w : g' ≫ f = f' ≫ g) (i : ℕ) : D.map w i = higherDirectImageBaseChange ℱ ℱ' θ w i :=
  D.map_eq _ w i

end AlgebraicGeometry.Scheme.Modules
