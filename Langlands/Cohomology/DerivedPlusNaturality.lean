import Langlands.Cohomology.ExtendMap

/-!
# Naturality of the cohomology of derived complexes

For an injective resolution `R` of `X`, `DerivedPlus.homologyIso F R n` identifies the
cohomology in degree `n : ℕ` of the derived complex `(derivedComplex F).obj X` with
`(F.rightDerived n).obj X`. This file proves that these identifications are natural in
`X`: for `f : X ⟶ Y` and any injective resolutions `I` of `X` and `J` of `Y`, they
intertwine the map induced by `f` on the cohomology of derived complexes with
`(F.rightDerived n).map f`. They therefore assemble to a natural isomorphism
`homologyNatIso F n : derivedComplex F ⋙ DerivedCategory.Plus.homologyFunctor D n ≅
F.rightDerived n`, whose component at `X` is `homologyIso` computed with any injective
resolution of `X`.

The proof follows the definition of `homologyIso` step by step. Each comparison in it
is natural with respect to a morphism of injective resolutions
`InjectiveResolution.Hom I J f`. Mathlib's `InjectiveResolution.desc` supplies such a
morphism for every `f`.
-/

noncomputable section

namespace Langlands.Cohomology.DerivedPlus

open CategoryTheory CategoryTheory.Limits

section Extend

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- The termwise comparison `extendXMapIso` is natural in the complex. -/
theorem extendXMapIso_hom_mapX {K L : HomologicalComplex C c} (φ : K ⟶ L) (i : Option ι) :
    (extendXMapIso F K i).hom ≫ F.map (HomologicalComplex.extend.mapX φ i) =
      HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map φ) i ≫
        (extendXMapIso F L i).hom :=
  match i with
  | none => (HomologicalComplex.extend.isZero_X _ rfl).eq_of_src _ _
  | some _ => (Category.id_comp _).trans (Category.comp_id _).symm

/-- Naturality of the comparison `mapExtendIso` between extending the image of a
complex and the image of the extended complex. -/
@[reassoc]
theorem mapExtendIso_hom_naturality (e : c.Embedding c') {K L : HomologicalComplex C c}
    (φ : K ⟶ L) :
    (mapExtendIso F K e).hom ≫
        (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e) =
      HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map φ) e ≫
        (mapExtendIso F L e).hom := by
  ext i'
  exact extendXMapIso_hom_mapX F φ (e.r i')


end Extend

section Derived

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
variable (F : C ⥤ D) [F.Additive]

variable {X Y : C} {f : X ⟶ Y} {I : InjectiveResolution X} {J : InjectiveResolution Y}

/-- The morphism of bounded below complexes between extended injective resolutions
induced by a morphism of injective resolutions. -/
def resolutionPlusMap (φ : InjectiveResolution.Hom I J f) :
    resolutionPlus I ⟶ resolutionPlus J :=
  ObjectProperty.homMk φ.hom'

omit [EnoughInjectives C] in
/-- The image of `singleIsoOfResolution R` in the unbounded derived category, written as
the composite used to define it. -/
theorem ι_map_singleIsoOfResolution_hom (R : InjectiveResolution X) :
    DerivedCategory.Plus.ι.map (singleIsoOfResolution R).hom =
      (DerivedCategory.Plus.singleFunctorιIso C 0).hom.app X ≫
        (DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
          DerivedCategory.Q.map R.ι' ≫
            (DerivedCategory.Plus.QCompιIso C).inv.app (resolutionPlus R) := by
  rw [singleIsoOfResolution, Functor.preimageIso_hom, Functor.map_preimage]
  rfl

omit [EnoughInjectives C] in
set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between an object in degree zero and an injective resolution is
natural with respect to morphisms of injective resolutions. -/
@[reassoc]
theorem singleIsoOfResolution_hom_naturality (φ : InjectiveResolution.Hom I J f) :
    (DerivedCategory.Plus.singleFunctor C 0).map f ≫ (singleIsoOfResolution J).hom =
      (singleIsoOfResolution I).hom ≫ DerivedCategory.Plus.Q.map (resolutionPlusMap φ) := by
  apply DerivedCategory.Plus.ι.map_injective
  have h₁ := (DerivedCategory.Plus.singleFunctorιIso C 0).hom.naturality f
  have h₂ := (DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality f
  have h₃ := (DerivedCategory.Plus.QCompιIso C).inv.naturality (resolutionPlusMap φ)
  have h₄ : DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map f) ≫
      DerivedCategory.Q.map J.ι' = DerivedCategory.Q.map I.ι' ≫ DerivedCategory.Q.map φ.hom' := by
    rw [← Functor.map_comp, ← Functor.map_comp, InjectiveResolution.Hom.ι'_comp_hom']
  simp only [Functor.comp_map] at h₁ h₂ h₃
  rw [Functor.map_comp, Functor.map_comp, ι_map_singleIsoOfResolution_hom,
    ι_map_singleIsoOfResolution_hom]
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₄, ← h₃]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between the derived complex and `F` applied to an injective
resolution is natural with respect to morphisms of injective resolutions. -/
@[reassoc]
theorem derivedComplexIso_hom_naturality (φ : InjectiveResolution.Hom I J f) :
    (derivedComplex F).map f ≫ (derivedComplexIso F J).hom =
      (derivedComplexIso F I).hom ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map (resolutionPlusMap φ)) := by
  have h := F.rightDerivedFunctorPlusUnit.naturality (resolutionPlusMap φ)
  simp only [Functor.comp_map] at h
  have h' : F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map (resolutionPlusMap φ)) ≫
      inv (F.rightDerivedFunctorPlusUnit.app (resolutionPlus J)) =
      inv (F.rightDerivedFunctorPlusUnit.app (resolutionPlus I)) ≫
        DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map (resolutionPlusMap φ)) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact h.symm
  simp only [derivedComplexIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
  change F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f) ≫ _ = _
  rw [← Functor.map_comp_assoc, singleIsoOfResolution_hom_naturality φ, Functor.map_comp,
    Category.assoc, h', Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The identification of the cohomology of the derived complex with the cohomology of
`F` applied to an integer-indexed injective resolution is natural with respect to
morphisms of injective resolutions. -/
@[reassoc]
theorem homologyResolutionIso_hom_naturality (φ : InjectiveResolution.Hom I J f) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).map ((derivedComplex F).map f) ≫
        (homologyResolutionIso F J n).hom =
      (homologyResolutionIso F I n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom')
          n := by
  have h₁ := derivedComplexIso_hom_naturality F φ
  have h₂ := (DerivedCategory.Plus.QCompιIso D).hom.naturality
    (F.mapCochainComplexPlus.map (resolutionPlusMap φ))
  have h₃ := (DerivedCategory.homologyFunctorFactors D n).hom.naturality
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom')
  simp only [Functor.comp_map] at h₂ h₃
  simp only [homologyResolutionIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Functor.map_comp_assoc, h₁, Functor.map_comp, Category.assoc]
  change _ ≫ (DerivedCategory.homologyFunctor D n).map _ ≫
    (DerivedCategory.homologyFunctor D n).map _ ≫ _ = _
  rw [← Functor.map_comp_assoc, h₂, Functor.map_comp, Category.assoc]
  erw [h₃]
  simp only [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identification `homologyIso` of the cohomology of the derived complex with
`F.rightDerived n` is natural with respect to morphisms of injective resolutions. -/
@[reassoc]
theorem homologyIso_hom_naturality_of_hom (φ : InjectiveResolution.Hom I J f) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor D n).map ((derivedComplex F).map f) ≫
        (homologyIso F J n).hom =
      (homologyIso F I n).hom ≫ (F.rightDerived n).map f := by
  have comm : I.ι.f 0 ≫ φ.hom.f 0 = f ≫ J.ι.f 0 :=
    φ.ι_f_zero_comp_hom_f_zero.trans (by rw [CochainComplex.single₀_map_f_zero])
  have h₁ := homologyResolutionIso_hom_naturality F φ n
  have h₂ := extendMapIso_hom_naturality ComplexShape.embeddingUpNat F φ.hom
  have h₃ := HomologicalComplex.extendHomologyIso_hom_naturality
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) ComplexShape.embeddingUpNat
    (j := n) (j' := (n : ℤ)) rfl
  have h₄ := InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ.hom comm F n
  simp only [homologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  have h₅ : HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom') n ≫
        HomologicalComplex.homologyMap
          (mapExtendIso F J.cocomplex ComplexShape.embeddingUpNat).inv n =
      HomologicalComplex.homologyMap
          (mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat).inv n ≫
        HomologicalComplex.homologyMap (HomologicalComplex.extendMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom)
            ComplexShape.embeddingUpNat) n :=
    (HomologicalComplex.homologyMap_comp _ _ _).symm.trans
      ((congrArg (fun g => HomologicalComplex.homologyMap g (n : ℤ)) h₂).trans
        (HomologicalComplex.homologyMap_comp _ _ _))
  rw [reassoc_of% h₁]
  simp only [Category.assoc]
  refine congrArg (_ ≫ ·) ?_
  change HomologicalComplex.homologyMap _ (n : ℤ) ≫
    HomologicalComplex.homologyMap _ (n : ℤ) ≫ _ = _
  rw [reassoc_of% h₅, reassoc_of% h₃, h₄]
  rfl

omit [HasDerivedCategory C] [EnoughInjectives C] in
variable (f I J) in
/-- The morphism of injective resolutions over `f` given by Mathlib's chosen lift
`InjectiveResolution.desc`. -/
def descHom : InjectiveResolution.Hom I J f where
  hom := InjectiveResolution.desc f J I
  ι_f_zero_comp_hom_f_zero :=
    (InjectiveResolution.desc_commutes_zero f J I).trans
      (by rw [CochainComplex.single₀_map_f_zero]; rfl)

variable (f I J) in
/-- The identification `homologyIso` of the cohomology of the derived complex with
`F.rightDerived n` is natural in the object, for any choice of injective resolutions. -/
@[reassoc]
theorem homologyIso_hom_naturality (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor D n).map ((derivedComplex F).map f) ≫
        (homologyIso F J n).hom =
      (homologyIso F I n).hom ≫ (F.rightDerived n).map f :=
  homologyIso_hom_naturality_of_hom F (descHom f I J) n

/-- In degree `n : ℕ`, cohomology of the derived complex is naturally isomorphic
to the right derived functor `F.rightDerived n`. -/
def homologyNatIso (n : ℕ) :
    derivedComplex F ⋙ DerivedCategory.Plus.homologyFunctor D n ≅ F.rightDerived n :=
  NatIso.ofComponents (fun X => homologyIso F (injectiveResolution X) n)
    (fun f => homologyIso_hom_naturality F f _ _ n)

/-- The components of `homologyNatIso` are the comparisons `homologyIso` computed
with any injective resolution. -/
theorem homologyNatIso_hom_app (n : ℕ) (R : InjectiveResolution X) :
    (homologyNatIso F n).hom.app X = (homologyIso F R n).hom := by
  have h := homologyIso_hom_naturality F (𝟙 X) (injectiveResolution X) R n
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h.symm

end Derived

end Langlands.Cohomology.DerivedPlus
