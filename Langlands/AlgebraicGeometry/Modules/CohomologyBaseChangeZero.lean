import Langlands.Cohomology.SupercuspidalExt.Reciprocity
import Langlands.AlgebraicGeometry.Modules.DerivedBaseChange
import Langlands.AlgebraicGeometry.Modules.PushforwardComparisonZero
import Langlands.AlgebraicGeometry.Modules.ScalarCohomologyBaseChange

/-! # Ordinary sections and degree-zero cohomology base change -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace Langlands.Cohomology.DerivedComparison

universe vC uC vD uD vE uE vF uF

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  {E' : Type uF} [Category.{vF} E'] [Abelian E']
  (Φ : C ⥤ E) [Φ.Additive] (P : E ⥤ E') [P.Additive]
  (T : C ⥤ D) [T.Additive] (Ψ : D ⥤ E') [Ψ.Additive]
  (e : Φ ⋙ P ≅ T ⋙ Ψ)
  [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  [P.PreservesHomology] [T.PreservesHomology] [T.PreservesInjectiveObjects]
  [PreservesFiniteLimits Φ] [PreservesFiniteLimits Ψ]

/-- In degree zero the exact-functor comparison is the ordinary comparison
through the canonical zeroth-derived identifications. -/
theorem rightDerivedCompIso_zero (X : C) :
    (rightDerivedCompIso Φ P T Ψ e 0).hom.app X =
      P.map (Φ.rightDerivedZeroIsoSelf.hom.app X) ≫ e.hom.app X ≫
        Ψ.rightDerivedZeroIsoSelf.inv.app (T.obj X) := by
  apply (cancel_epi (P.map (Φ.rightDerivedZeroIsoSelf.inv.app X))).1
  rw [← P.map_comp_assoc, Iso.inv_hom_id_app, P.map_id, Category.id_comp]
  simpa only [Functor.rightDerivedZeroIsoSelf_inv] using
      toRightDerivedZero_comp_rightDerivedCompIso Φ P T Ψ e X

end Langlands.Cohomology.DerivedComparison

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

universe u

section Restrict

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R)

/-- Restriction of the coefficient ring commutes with the canonical
degree-zero identifications. -/
theorem relativeCohomologyRestrictScalarsIso_zero (M : X.Modules) :
    (relativeCohomologyRestrictScalarsIso f 0).hom.app M =
      (ModuleCat.restrictScalars (structureRingHom f).hom).map
          ((cohomologyZeroIso X).hom.app M) ≫
        (relativeGlobalSectionsIso f).hom.app M ≫
          (relativeCohomologyZeroIso f).inv.app M := by
  change (Langlands.Cohomology.DerivedComparison.rightDerivedCompIso
      (globalSections X) (ModuleCat.restrictScalars (structureRingHom f).hom)
      (𝟭 _) (relativeGlobalSections f)
      (relativeGlobalSectionsIso f ≪≫ (Functor.leftUnitor _).symm) 0).hom.app M ≫
      𝟙 _ = _
  rw [Category.comp_id,
    Langlands.Cohomology.DerivedComparison.rightDerivedCompIso_zero]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.leftUnitor_inv_app]
  rfl

/-- The inverse restriction comparison has the corresponding ordinary
sections formula. -/
theorem relativeCohomologyRestrictScalarsIso_inv_zero (M : X.Modules) :
    (relativeCohomologyRestrictScalarsIso f 0).inv.app M =
      (relativeCohomologyZeroIso f).hom.app M ≫
        (relativeGlobalSectionsIso f).inv.app M ≫
          (ModuleCat.restrictScalars (structureRingHom f).hom).map
            ((cohomologyZeroIso X).inv.app M) := by
  apply (cancel_epi ((relativeCohomologyRestrictScalarsIso f 0).hom.app M)).1
  rw [Iso.hom_inv_id_app, relativeCohomologyRestrictScalarsIso_zero]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app]
  rfl

end Restrict

section BaseRing

variable {X : Scheme.{u}} {R R' : CommRingCat.{u}} (φ : R ⟶ R')
  (f : X ⟶ Spec R) (f' : X ⟶ Spec R')

/-- Base-ring change on degree-zero cohomology is base-ring change on
ordinary sections through the canonical identifications. -/
theorem relativeCohomologyBaseRingIso_zero
    (w : f = f' ≫ Spec.map φ) (M : X.Modules) :
    (relativeCohomologyBaseRingIso φ f f' w 0).hom.app M =
      (relativeCohomologyZeroIso f).hom.app M ≫
        (relativeGlobalSectionsBaseRingIso φ f f' w).inv.app M ≫
          (ModuleCat.restrictScalars φ.hom).map
            ((relativeCohomologyZeroIso f').inv.app M) := by
  let c := ModuleCat.restrictScalarsComp' φ.hom (structureRingHom f').hom
    (structureRingHom f).hom
    (by rw [structureRingHom_eq_comp φ f f' w, CommRingCat.hom_comp])
  have hc := c.hom.naturality ((cohomologyZeroIso X).inv.app M)
  simp only [Functor.comp_map] at hc
  simp only [relativeCohomologyBaseRingIso, relativeGlobalSectionsBaseRingIso,
    Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.associator_inv_app, Category.id_comp, Category.assoc]
  rw [relativeCohomologyRestrictScalarsIso_inv_zero,
    relativeCohomologyRestrictScalarsIso_zero]
  simp only [Functor.map_comp, Category.assoc]
  change _ ≫ _ ≫
      (ModuleCat.restrictScalars (structureRingHom f).hom).map
        ((cohomologyZeroIso X).inv.app M) ≫ c.hom.app _ ≫ _ = _
  rw [reassoc_of% hc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rfl

end BaseRing

section BaseChange

variable {X X' : Scheme.{u}} {R R' : CommRingCat.{u}}
  (φ : R ⟶ R') (f : X ⟶ Spec R) (f' : X' ⟶ Spec R')
  (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)

/-- The map on ordinary relative sections induced by the actual
pullback unit and the commuting square. -/
def sectionsBaseChangeMap (M : X.Modules) :
    (relativeGlobalSections f).obj M ⟶
      (ModuleCat.restrictScalars φ.hom).obj
        ((relativeGlobalSections f').obj ((Scheme.Modules.pullback g).obj M)) :=
  (relativeGlobalSections f).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) ≫
    (relativeGlobalSectionsCompIso g f).hom.app _ ≫
    (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w).inv.app _

/-- The scalar-linear adjunct of the ordinary relative sections map. -/
def scalarSectionsBaseChangeMap (M : X.Modules) :
    (ModuleCat.extendScalars φ.hom).obj ((relativeGlobalSections f).obj M) ⟶
      (relativeGlobalSections f').obj ((Scheme.Modules.pullback g).obj M) :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
    (sectionsBaseChangeMap φ f f' g w M)

@[simp]
lemma scalarSectionsBaseChangeMap_homEquiv (M : X.Modules) :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
        (scalarSectionsBaseChangeMap φ f f' g w M) =
      sectionsBaseChangeMap φ f f' g w M := by
  simp only [scalarSectionsBaseChangeMap, Equiv.apply_symm_apply]

/-- The ordinary sections map applies the actual sheaf pullback unit. -/
lemma sectionsBaseChangeMap_apply (M : X.Modules)
    (x : (relativeGlobalSections f).obj M) :
    sectionsBaseChangeMap φ f f' g w M x =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤ x := by
  rfl

/-- Ordinary base change is natural in the coefficient module. -/
@[reassoc]
lemma sectionsBaseChangeMap_naturality {M N : X.Modules} (a : M ⟶ N) :
    (relativeGlobalSections f).map a ≫ sectionsBaseChangeMap φ f f' g w N =
      sectionsBaseChangeMap φ f f' g w M ≫
        (ModuleCat.restrictScalars φ.hom).map
          ((relativeGlobalSections f').map ((Scheme.Modules.pullback g).map a)) := by
  ext x
  have h := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at h
  exact congrArg (fun k => k.app ⊤ (show Γ(M, ⊤) from x)) h

/-- Composing the scalar-linear map with the scalar unit recovers
the ordinary sections map. -/
@[reassoc]
lemma scalarSectionsBaseChangeMap_unit (M : X.Modules) :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app
        ((relativeGlobalSections f).obj M) ≫
        (ModuleCat.restrictScalars φ.hom).map
          (scalarSectionsBaseChangeMap φ f f' g w M) =
      sectionsBaseChangeMap φ f f' g w M := by
  simpa only [Adjunction.homEquiv_unit] using
    scalarSectionsBaseChangeMap_homEquiv φ f f' g w M

/-- The value on a tensor generator is the actual pullback unit on sections. -/
lemma scalarSectionsBaseChangeMap_one_tmul (M : X.Modules)
    (x : (relativeGlobalSections f).obj M) :
    scalarSectionsBaseChangeMap φ f f' g w M ((1 : R') ⊗ₜ[R,φ.hom] x) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤ x := by
  have h := congrArg (fun k => k x)
    (scalarSectionsBaseChangeMap_homEquiv φ f f' g w M)
  simpa only [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    sectionsBaseChangeMap_apply] using h

/-- Scalar-linear ordinary base change is natural in the coefficient module. -/
@[reassoc]
lemma scalarSectionsBaseChangeMap_naturality {M N : X.Modules} (a : M ⟶ N) :
    (ModuleCat.extendScalars φ.hom).map ((relativeGlobalSections f).map a) ≫
        scalarSectionsBaseChangeMap φ f f' g w N =
      scalarSectionsBaseChangeMap φ f f' g w M ≫
        (relativeGlobalSections f').map ((Scheme.Modules.pullback g).map a) := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    scalarSectionsBaseChangeMap_homEquiv, scalarSectionsBaseChangeMap_homEquiv]
  exact sectionsBaseChangeMap_naturality φ f f' g w a

/-- In degree zero the published semilinear cohomology map agrees with
the ordinary sections map through the canonical identifications. -/
theorem baseChangeMap_zero (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero
      ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M)))
    (hJ : ∀ J : X'.Modules, Injective J → ∀ q : ℕ,
      IsZero ((relativeCohomology f (q + 1)).obj ((Scheme.Modules.pushforward g).obj J))) :
    baseChangeMap φ f f' g w M hM hJ 0 =
      (relativeCohomologyZeroIso f).hom.app M ≫
        sectionsBaseChangeMap φ f f' g w M ≫
          (ModuleCat.restrictScalars φ.hom).map
            ((relativeCohomologyZeroIso f').inv.app _) := by
  have := isIso_pushforwardComparison g f _ hM hJ 0
  have hn := (relativeCohomologyZeroIso f).hom.naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  simp only [baseChangeMap, pushforwardComparison_zero,
    IsIso.inv_comp, NatIso.inv_inv_app,
    IsIso.inv_hom_id_assoc, Category.assoc,
    relativeCohomologyBaseRingIso_zero]
  rw [← Category.assoc]
  erw [hn]
  rfl

/-- In degree zero the published scalar-linear cohomology map agrees with
the scalar-linear ordinary sections map through the canonical identifications. -/
theorem scalarBaseChangeMap_zero (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero
      ((higherDirectImage g (q + 1)).obj ((Scheme.Modules.pullback g).obj M))) :
    scalarBaseChangeMap φ f f' g w M hM 0 =
      (ModuleCat.extendScalars φ.hom).map
          ((relativeCohomologyZeroIso f).hom.app M) ≫
        scalarSectionsBaseChangeMap φ f f' g w M ≫
          (relativeCohomologyZeroIso f').inv.app _ := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [scalarBaseChangeMap, Equiv.apply_symm_apply,
    scalarSectionsBaseChangeMap_homEquiv]
  exact baseChangeMap_zero φ f f' g w M hM _

end BaseChange

end Langlands.AlgebraicGeometry.Modules.DerivedSections
