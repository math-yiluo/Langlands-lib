/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Derived pullback on ringed topoi

Source: Stacks Project, Cohomology on Sites, Tag 06YY, lemma-derived-base-change
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

private noncomputable abbrev moduleUnderlying
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})

private theorem moduleUnderlying_finiteLimits
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : PreservesFiniteLimits (moduleUnderlying R) := by
  let V := sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})
  have : PreservesFiniteLimits (V ⋙ sheafToPresheaf J (Type u)) :=
    show PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{u})) from
        comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits V :=
    preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type u))
  exact comp_preservesFiniteLimits _ _

private theorem moduleUnderlying_epi
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : (moduleUnderlying R).PreservesEpimorphisms := by
  let V := sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})
  have : V.PreservesEpimorphisms := ⟨fun {M N} f hf ↦ by
    have : Sheaf.IsLocallySurjective f :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} f).2 hf
    exact inferInstance⟩
  exact inferInstanceAs ((toSheaf _ ⋙ V).PreservesEpimorphisms)

private theorem algebraicInverseImage_finiteLimits
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {RI : Sheaf JD CommRingCat.{u}}
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)) [PreservesFiniteLimits L]
    (I : AlgebraicInverseImage L R RI) : PreservesFiniteLimits I.modules := by
  have := moduleUnderlying_finiteLimits R
  have := moduleUnderlying_finiteLimits RI
  have : PreservesFiniteLimits (moduleUnderlying R ⋙ L) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (I.modules ⋙ moduleUnderlying RI) :=
    preservesFiniteLimits_of_natIso I.moduleUnderlying.symm
  exact preservesFiniteLimits_of_reflects_of_preserves I.modules (moduleUnderlying RI)

private theorem algebraicInverseImage_epi
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {RI : Sheaf JD CommRingCat.{u}}
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u)) (adj : L ⊣ V)
    (I : AlgebraicInverseImage L R RI) : I.modules.PreservesEpimorphisms := by
  have := moduleUnderlying_epi R
  have := adj.leftAdjoint_preservesColimits
  constructor
  intro M N f hf
  apply (moduleUnderlying RI).epi_of_epi_map
  have : Epi ((moduleUnderlying R ⋙ L).map f) := inferInstance
  have hn := I.moduleUnderlying.hom.naturality f
  have : Epi ((I.modules ⋙ moduleUnderlying RI).map f ≫
      I.moduleUnderlying.hom.app N) := by
    rw [hn]
    infer_instance
  exact (epi_comp_iff_of_isIso _ (I.moduleUnderlying.hom.app N)).1 this

private noncomputable def scalarExtensionPresheaf
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      PresheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj where
  obj M := changeOfRingsPresheaf.{u, u, u} c M
  map {M N} f :=
    { app := fun U ↦ (ModuleCat.extendScalars (c.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality.{u, u, u} c M f }
  map_id M := by
    ext U : 1
    simp
    rfl
  map_comp f g := by
    ext U : 1
    exact (ModuleCat.extendScalars (c.hom.app U).hom).map_comp _ _

private theorem scalarExtensionPresheaf_additive
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S) :
    (scalarExtensionPresheaf c).Additive where
  map_add {M N} f g := by
    ext U : 1
    have : (ModuleCat.extendScalars (c.hom.app U).hom).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (c.hom.app U).hom).left_adjoint_additive
    simpa only [scalarExtensionPresheaf, add_val, PresheafOfModules.add_app] using
      (ModuleCat.extendScalars (c.hom.app U).hom).map_add
        (f := f.val.app U) (g := g.val.app U)

private noncomputable def scalarExtension
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) :=
  scalarExtensionPresheaf c ⋙ PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)

private theorem scalarExtension_additive
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S) :
    (scalarExtension c).Additive := by
  have hsheaf : (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 _)).left_adjoint_additive
  have := scalarExtensionPresheaf_additive c
  dsimp only [scalarExtension]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarExtensionPresheafIdIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    M.val ≅ (scalarExtensionPresheaf (𝟙 R)).obj M := by
  refine PresheafOfModules.isoMk
    (fun U ↦ ((ModuleCat.extendScalarsId (R.obj.obj U)).app (M.val.obj U)).symm) ?_
  intro U V i
  ext m
  change (ModuleCat.extendScalarsId (R.obj.obj V)).inv.app (M.val.obj V)
      (M.val.map i m) =
    changeOfRingsMap (𝟙 R) M i
      ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (M.val.obj U) m)
  rw [ModuleCat.extendScalarsId_inv_app_apply, ModuleCat.extendScalarsId_inv_app_apply]
  simpa [changeOfRingsMap] using
    (Classical.choose_spec (exists_changeOfRingsMap (𝟙 R) M i)
      (1 : R.obj.obj U) m).symm

private noncomputable def scalarExtensionIdIsoApp
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (scalarExtension (𝟙 R)).obj M ≅ M :=
  (PresheafOfModules.sheafification (𝟙 _)).mapIso
      (scalarExtensionPresheafIdIso R M).symm ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app M)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarExtensionIdIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : scalarExtension (𝟙 R) ≅ 𝟭 _ := by
  refine NatIso.ofComponents (scalarExtensionIdIsoApp R) ?_
  intro M N a
  let F := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let ψ := (scalarExtensionPresheaf (𝟙 R)).map a
  have hp : (scalarExtensionPresheafIdIso R M).hom ≫ ψ =
      a.val ≫ (scalarExtensionPresheafIdIso R N).hom := by
    ext U m
    change (ModuleCat.extendScalars (RingHom.id (R.obj.obj U))).map (a.val.app U)
      ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (M.val.obj U) m) =
        (ModuleCat.extendScalarsId (R.obj.obj U)).inv.app (N.val.obj U) (a.val.app U m)
    exact ConcreteCategory.congr_hom ((ModuleCat.extendScalarsId (R.obj.obj U)).inv.naturality
      (a.val.app U)) m
  have hp' : (scalarExtensionPresheafIdIso R M).inv ≫ a.val =
      ψ ≫ (scalarExtensionPresheafIdIso R N).inv := by
    rw [← cancel_epi (scalarExtensionPresheafIdIso R M).hom]
    simp only [← Category.assoc, hp]
    simp
  symm
  change F.map (scalarExtensionPresheafIdIso R M).inv ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app M ≫ a =
    F.map ψ ≫ F.map (scalarExtensionPresheafIdIso R N).inv ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit.app N
  rw [← (PresheafOfModules.sheafificationAdjunction (𝟙 _)).counit_naturality a]
  change F.map (scalarExtensionPresheafIdIso R M).inv ≫ F.map a.val ≫ _ = _
  rw [← F.map_comp_assoc, hp', F.map_comp_assoc]

open MonoidalCategory in
private noncomputable def siteTensorPresheafIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (M N : PresheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj) :
    M ⊗ N ≅ siteTensorPresheaf M N := by
  refine PresheafOfModules.isoMk (fun U ↦ Iso.refl _) ?_
  intro U V i
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' (R := R.obj.obj U) (R₂ := R.obj.obj U) ?_
  intro m n
  rfl

open MonoidalCategory in
private noncomputable def siteTensorRightIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    letI := monoidalCategory R
    MonoidalCategory.tensorRight N ≅ siteSheafTensorRight (J := J) (A := R) N := by
  letI := monoidalCategory R
  let F := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  refine NatIso.ofComponents
    (fun M ↦ tensorObjIsoSheafification M N ≪≫
      F.mapIso (siteTensorPresheafIso R M.val N.val)) ?_
  intro M M' f
  change f ▷ N ≫ ((tensorObjIsoSheafification M' N).hom ≫
      F.map (siteTensorPresheafIso R M'.val N.val).hom) =
    ((tensorObjIsoSheafification M N).hom ≫
      F.map (siteTensorPresheafIso R M.val N.val).hom) ≫
        F.map (siteTensorHom f.val N.val)
  have hn := whiskerRight_tensorObjIsoSheafification_hom (R := R) f N
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← F.map_comp, ← F.map_comp]
  congr 1

private theorem flat_onSite_of_flat
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hM : M.IsFlat) : IsFlatOnSite (J := J) (R := R) M := by
  let := monoidalCategory R
  exact ObjectProperty.prop_of_iso (exactFunctor _ _) (siteTensorRightIso R M) hM

set_option synthInstance.maxSize 256 in
open MonoidalCategory in
private theorem isKFlat_of_iso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    {P Q : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (e : P ≅ Q) (hP : P.IsKFlatTensor) : Q.IsKFlatTensor := by
  let := monoidalCategory R
  intro A hA n
  let F := (MonoidalCategory.curriedTensor (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let e' : CochainComplex.mapBifunctor A P (curriedTensor _) ≅
      CochainComplex.mapBifunctor A Q (curriedTensor _) :=
    HomologicalComplex₂.total.mapIso ((F.obj A).mapIso e) (ComplexShape.up ℤ)
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (hP A hA n)).of_iso
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso e').symm |>
      (HomologicalComplex.exactAt_iff_isZero_homology _ n).2

private theorem isKFlat_inverseImage
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {RI : Sheaf JD CommRingCat.{u}}
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (I : AlgebraicInverseImage L R RI) [I.modules.Additive]
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hP : P.IsKFlatTensor) (hf : ∀ n : ℤ, (P.X n).IsFlat) :
    CochainComplex.IsKFlatTensor
      ((I.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  have := algebraicInverseImage_finiteLimits L I
  have : I.modules.Additive := Functor.additive_of_preserves_binary_products I.modules
  have := scalarExtension_additive (𝟙 RI)
  let U := I.modules ⋙ scalarExtension (𝟙 RI)
  have hobj (M) : U.obj M = changeOfRings (𝟙 RI) (I.modules.obj M) := rfl
  have hmap {M N} (a : M ⟶ N) : U.map a = eqToHom (hobj M) ≫
      changeOfRingsHom (𝟙 RI) (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have hk := (isKFlat_ringedToposPullback L V adj I (𝟙 RI) U hobj hmap P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP)
      (fun n ↦ flat_onSite_of_flat (P.X n) (hf n))).1
  let e : U ≅ I.modules :=
    Functor.isoWhiskerLeft I.modules (scalarExtensionIdIso RI) ≪≫ I.modules.rightUnitor
  exact isKFlat_of_iso ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app P)
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk)

/-- A morphism of ringed topoi admits an exact derived pullback computed on
K-flat complexes with flat terms.  The functor `uStar` is the module-sheaf
pullback `M ↦ S ⊗_{u⁻¹R} u⁻¹M` attached to the morphism of ringed topoi.
Source: Stacks Project, Tag 06YY (auxiliary; not a blueprint node).
The proof first makes termwise pullback an exact functor on homotopy categories.
It then proves that pullback preserves quasi-isomorphisms between K-flat
complexes with flat terms, using exactness of inverse image and change of rings.
The resolving-class left-derived-functor theorem gives `LF`, its canonical
transformation `epsilon`, and the isomorphism on every such complex.  Finally,
for a resolution `p`, define `alpha p` as the inverse of `LF.map (Q p)` followed
by `epsilon`. Naturality follows from the resolution square and naturality of
`epsilon`. For resolutions p, q of the same object put C(q,p) = alpha(p) inverse
followed by alpha(q); cancellation proves the identity and composition laws,
and a chain map a with a followed by q = p induces exactly C(q,p).
-/
theorem ringedTopoiDerivedPullback
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {S RI : Sheaf JD CommRingCat.{u}}
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R), uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))] :
    ∃ (LF : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤
        DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
      (epsilon : DerivedCategory.Qh ⋙ LF ⟶
        uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor epsilon
        (HomotopyCategory.quasiIso (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)) ∧
      (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
      (∀ {P Q : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ} (s : P ⟶ Q),
        P.IsKFlatTensor → (∀ n : ℤ, (P.X n).IsFlat) →
        Q.IsKFlatTensor → (∀ n : ℤ, (Q.X n).IsFlat) → QuasiIso s →
          QuasiIso ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) ∧
      (∀ (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ),
        P.IsKFlatTensor → (∀ n : ℤ, (P.X n).IsFlat) →
          IsIso (epsilon.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) ∧
      ∃ (alpha : ∀ {A P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
        (p : P ⟶ A), P.IsKFlatTensor → (∀ n : ℤ, (P.X n).IsFlat) →
          QuasiIso p → (LF.obj (DerivedCategory.Q.obj A) ≅
            DerivedCategory.Q.obj
              ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))),
        (∀ {A P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ} (p : P ⟶ A)
          (hp : P.IsKFlatTensor) (hf : ∀ n : ℤ, (P.X n).IsFlat) [hq : QuasiIso p],
          (alpha p hp hf hq).hom = inv (LF.map (DerivedCategory.Q.map p)) ≫
            cast (by rfl)
              (epsilon.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) ∧
        (∀ {A A' P P' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
          (p : P ⟶ A) (p' : P' ⟶ A') (a : P ⟶ P') (b : A ⟶ A')
          (hp : P.IsKFlatTensor) (hf : ∀ n : ℤ, (P.X n).IsFlat) (hq : QuasiIso p)
          (hp' : P'.IsKFlatTensor) (hf' : ∀ n : ℤ, (P'.X n).IsFlat) (hq' : QuasiIso p'),
          p ≫ b = a ≫ p' →
          LF.map (DerivedCategory.Q.map b) ≫ (alpha p' hp' hf' hq').hom =
            (alpha p hp hf hq).hom ≫ DerivedCategory.Q.map
              ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).map a)) ∧
        (∀ {A P P' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
          (p : P ⟶ A) (p' : P' ⟶ A) (a : P ⟶ P')
          (hp : P.IsKFlatTensor) (hf : ∀ n : ℤ, (P.X n).IsFlat) (hq : QuasiIso p)
          (hp' : P'.IsKFlatTensor) (hf' : ∀ n : ℤ, (P'.X n).IsFlat) (hq' : QuasiIso p'),
          a ≫ p' = p →
          (alpha p hp hf hq).inv ≫ (alpha p' hp' hf' hq').hom =
            DerivedCategory.Q.map
              ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).map a)) ∧
        (∀ {A P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ} (p : P ⟶ A)
          (hp : P.IsKFlatTensor) (hf : ∀ n : ℤ, (P.X n).IsFlat) (hq : QuasiIso p),
          (alpha p hp hf hq).inv ≫ (alpha p hp hf hq).hom = 𝟙 _) ∧
        (∀ {A P P' P'' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
          (p : P ⟶ A) (p' : P' ⟶ A) (p'' : P'' ⟶ A)
          (hp : P.IsKFlatTensor) (hf : ∀ n : ℤ, (P.X n).IsFlat) (hq : QuasiIso p)
          (hp' : P'.IsKFlatTensor) (hf' : ∀ n : ℤ, (P'.X n).IsFlat) (hq' : QuasiIso p')
          (hp'' : P''.IsKFlatTensor) (hf'' : ∀ n : ℤ, (P''.X n).IsFlat)
          (hq'' : QuasiIso p''),
          ((alpha p hp hf hq).inv ≫ (alpha p' hp' hf' hq').hom) ≫
              ((alpha p' hp' hf' hq').inv ≫ (alpha p'' hp'' hf'' hq'').hom) =
            (alpha p hp hf hq).inv ≫ (alpha p'' hp'' hf'' hq'').hom) := by
  classical
  let A := SheafOfModules.{u}
    ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let B := SheafOfModules.{u}
    ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)
  let T := uStar.mapHomologicalComplex (ComplexShape.up ℤ)
  let H := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let F := uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have hpres : ∀ {P Q : CochainComplex A ℤ} (s : P ⟶ Q),
      P.IsKFlatTensor → (∀ n : ℤ, (P.X n).IsFlat) →
      Q.IsKFlatTensor → (∀ n : ℤ, (Q.X n).IsFlat) → QuasiIso s → QuasiIso (T.map s) := by
    have := algebraicInverseImage_finiteLimits uInv I
    have : I.modules.Additive := Functor.additive_of_preserves_binary_products I.modules
    have := algebraicInverseImage_epi uInv uPush adj I
    have : I.modules.PreservesHomology :=
      Functor.preservesHomology_of_preservesEpis_and_kernels I.modules
    intro P Q s hp hf hq hqf hs
    have := hs
    have hkP := isKFlat_inverseImage uInv uPush adj I P hp hf
    have hkQ := isKFlat_inverseImage uInv uPush adj I Q hq hqf
    have := scalarExtension_additive c
    let E := scalarExtension c
    have heobj (M) : E.obj M = changeOfRings c M := rfl
    have hemap {M N} (a : M ⟶ N) : E.map a = eqToHom (heobj M) ≫
        changeOfRingsHom c M a ≫ eqToHom (heobj N).symm := by
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    have ht := changeOfRings_kFlat_quasiIso c E heobj hemap
      ((I.modules.mapHomologicalComplex (ComplexShape.up ℤ)).map s) hkP hkQ
        (by infer_instance)
    let e : uStar ≅ I.modules ⋙ E := NatIso.ofComponents (fun M ↦ eqToIso (hobj M))
      (fun {M N} a ↦ by
        rw [hmap]
        simp only [eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl,
          Category.comp_id]
        rfl)
    let e' : T ≅ I.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        E.mapHomologicalComplex (ComplexShape.up ℤ) :=
      NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (I.modules ⋙ E))
          (ComplexShape.up ℤ)).symm
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e'.app P) (e'.app Q) (e'.hom.naturality s).symm)).2 ht
  let K : Set (HomotopyCategory A (ComplexShape.up ℤ)) :=
    {X | ∃ P : CochainComplex A ℤ, H.obj P = X ∧
      P.IsKFlatTensor ∧ ∀ n : ℤ, (P.X n).IsFlat}
  have hres : ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ (X' : HomotopyCategory A (ComplexShape.up ℤ)) (s : X' ⟶ X),
        X' ∈ K ∧ HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s := by
    intro X
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, p, hp, hf, hq, _⟩ := CochainComplex.exists_isKFlatResolution G
    exact ⟨H.obj P, H.map p, ⟨P, rfl, hp, hf⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hq⟩
  have hinv : ∀ (X X' : HomotopyCategory A (ComplexShape.up ℤ)) (s : X ⟶ X'),
      X ∈ K → X' ∈ K → HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s →
        IsIso (F.map s) := by
    intro X X' s hX hX' hs
    obtain ⟨P, rfl, hp, hf⟩ := hX
    obtain ⟨P', rfl, hp', hf'⟩ := hX'
    obtain ⟨s, rfl⟩ := H.map_surjective s
    have hq := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs
    have ht := hpres s hp hf hp' hf' hq
    change IsIso (DerivedCategory.Qh.map
      ((uStar.mapHomotopyCategory (ComplexShape.up ℤ)).map (H.map s)))
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff (T.map s)).2 ht)
  obtain ⟨_, LF, ε, hLF, hex, hε⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) F K hres hinv
  have hcomp (P : CochainComplex A ℤ) (hp : P.IsKFlatTensor)
      (hf : ∀ n : ℤ, (P.X n).IsFlat) : IsIso (ε.app (H.obj P)) :=
    hε (H.obj P) ⟨P, rfl, hp, hf⟩
  refine ⟨LF, ε, hLF, hex, hpres, hcomp, ?_⟩
  let α : ∀ {G P : CochainComplex A ℤ} (p : P ⟶ G),
      P.IsKFlatTensor → (∀ n : ℤ, (P.X n).IsFlat) → QuasiIso p →
        (LF.obj (DerivedCategory.Q.obj G) ≅ DerivedCategory.Q.obj (T.obj P)) :=
    fun {G P} p hp hf hq ↦ by
      letI := hq
      letI := hcomp P hp hf
      exact (asIso (LF.map (DerivedCategory.Q.map p))).symm ≪≫
        asIso (ε.app (H.obj P))
  have hα {G P : CochainComplex A ℤ} (p : P ⟶ G)
      (hp : P.IsKFlatTensor) (hf : ∀ n : ℤ, (P.X n).IsFlat) (hq : QuasiIso p) :
      (α p hp hf hq).hom = inv (LF.map (DerivedCategory.Q.map p)) ≫ ε.app (H.obj P) :=
    rfl
  have hnat {G G' P P' : CochainComplex A ℤ}
      (p : P ⟶ G) (p' : P' ⟶ G') (a : P ⟶ P') (b : G ⟶ G')
      (hp : P.IsKFlatTensor) (hf : ∀ n : ℤ, (P.X n).IsFlat) (hq : QuasiIso p)
      (hp' : P'.IsKFlatTensor) (hf' : ∀ n : ℤ, (P'.X n).IsFlat) (hq' : QuasiIso p')
      (hsq : p ≫ b = a ≫ p') :
      LF.map (DerivedCategory.Q.map b) ≫ (α p' hp' hf' hq').hom =
        (α p hp hf hq).hom ≫ DerivedCategory.Q.map (T.map a) := by
    have := hq
    have := hq'
    rw [hα p hp hf hq, hα p' hp' hf' hq']
    apply (cancel_epi (LF.map (DerivedCategory.Q.map p))).1
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    have hs : LF.map (DerivedCategory.Q.map p) ≫ LF.map (DerivedCategory.Q.map b) =
        LF.map (DerivedCategory.Q.map a) ≫ LF.map (DerivedCategory.Q.map p') := by
      simp only [← Functor.map_comp, hsq]
    rw [← Category.assoc, ← Category.assoc, hs]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact ε.naturality (H.map a)
  refine ⟨α, ?_, hnat, ?_, ?_, ?_⟩
  · intro G P p hp hf hq
    exact hα p hp hf hq
  · intro G P P' p p' a hp hf hq hp' hf' hq' ha
    have h := hnat p p' a (𝟙 G) hp hf hq hp' hf' hq' (by simpa using ha.symm)
    have hid : LF.map (DerivedCategory.Q.map (𝟙 G)) = 𝟙 _ :=
      (congrArg LF.map (DerivedCategory.Q.map_id G)).trans (LF.map_id _)
    rw [hid, Category.id_comp] at h
    change (α p hp hf hq).inv ≫ (α p' hp' hf' hq').hom = _
    rw [h, Iso.inv_hom_id_assoc]
  · intro G P p hp hf hq
    exact (α p hp hf hq).inv_hom_id
  · intro G P P' P'' p p' p'' hp hf hq hp' hf' hq' hp'' hf'' hq''
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

end SheafOfModules
