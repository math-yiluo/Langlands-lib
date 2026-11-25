/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.GlobalSectionScalarExtension
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.AlgebraicGeometry.RingComplexSemilinearExtension
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Scalar extension from global sections on K-flat quasi-isomorphisms

Source: Stacks Project, Cohomology on Sites, Tags 06YS and 06YT; algebraization.tex,
Tag 099E, final paragraph.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace CategoryTheory

attribute [local instance] ringFamilyGlobalExtension_additive

private noncomputable def bottomModuleEquivalence
    {D : Type u} [SmallCategory D]
    (R : Sheaf (⊥ : GrothendieckTopology D) RingCat.{u}) :
    SheafOfModules.{u} R ≌ PresheafOfModules.{u} R.obj where
  functor := SheafOfModules.forget R
  inverse :=
    { obj := fun N ↦ ⟨N, Presheaf.isSheaf_bot _⟩
      map := fun g ↦ ⟨g⟩ }
  unitIso := NatIso.ofComponents (fun _ ↦ { hom := ⟨𝟙 _⟩, inv := ⟨𝟙 _⟩ })
  counitIso := Iso.refl _

/- The tensor-presheaf construction generalizes the proved private construction in
`WeilConjectures.CategoryTheory.PresheafChangeOfRingsAdjunction` from open sets to an
arbitrary small category. Keeping both ring presheaves explicit avoids expanding the
abstract pullback while elaborating the comparison. -/
section TensorPresheaf
variable {D : Type u} [SmallCategory D]
variable (R S : Dᵒᵖ ⥤ CommRingCat.{u})
variable (α : R ⟶ S)
local notation "a" => Functor.whiskerRight α (forget₂ CommRingCat RingCat)
local notation "push" => PresheafOfModules.pushforward
  (R := S ⋙ forget₂ CommRingCat RingCat) (S := R ⋙ forget₂ CommRingCat RingCat)
  (F := 𝟭 D) a
local notation "pull" => PresheafOfModules.pullback
  (R := S ⋙ forget₂ CommRingCat RingCat) (S := R ⋙ forget₂ CommRingCat RingCat)
  (F := 𝟭 D) a
local notation "adjP" => PresheafOfModules.pullbackPushforwardAdjunction
  (R := S ⋙ forget₂ CommRingCat RingCat) (S := R ⋙ forget₂ CommRingCat RingCat)
  (F := 𝟭 D) a
open scoped ChangeOfRings TensorProduct

local instance {M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    {U V : Dᵒᵖ} (i : U ⟶ V) :
    Module (R.obj V)
      ((ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map i).hom).obj
        (M.obj V)) :=
  inferInstanceAs (Module (R.obj V) (M.obj V))

private noncomputable def tensorRestriction (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    {U V : Dᵒᵖ} (i : U ⟶ V) :
    (ModuleCat.extendScalars (α.app U).hom).obj (M.obj U) ⟶
      (ModuleCat.restrictScalars (S.map i).hom).obj
        ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) := by
  let : Module (R.obj V) (S.obj V) :=
    Module.compHom (S.obj V) (α.app V).hom
  let T := (ModuleCat.restrictScalars (S.map i).hom).obj
    ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V))
  let h : M.obj U ⟶ (ModuleCat.restrictScalars (α.app U).hom).obj T :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (α.app U).hom).obj T)
      { toFun := fun m ↦ (1 : S.obj V) ⊗ₜ[R.obj V,
          (α.app V).hom] M.map i m
        map_add' := by
          intro m n
          rw [map_add, TensorProduct.tmul_add]
        map_smul' := by
          intro r m
          change (1 : S.obj V) ⊗ₜ[R.obj V, (α.app V).hom]
            M.map i (r • m) = S.map i (α.app U r) •
              ((1 : S.obj V) ⊗ₜ[R.obj V, (α.app V).hom] M.map i m)
          rw [M.map_smul]
          have hn : S.map i (α.app U r) =
              α.app V (R.map i r) :=
            ConcreteCategory.congr_hom (α.naturality i).symm r
          rw [hn]
          change (1 : S.obj V) ⊗ₜ[R.obj V]
            ((R.map i r) • (show M.obj V from M.map i m)) = _
          rw [TensorProduct.tmul_smul]
          rfl }
  exact ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    («R» := R.obj U) («S» := S.obj U) (α.app U).hom h

private theorem tensorRestriction_tmul (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    {U V : Dᵒᵖ} (i : U ⟶ V)
    (b : S.obj U) (m : M.obj U) :
    tensorRestriction R S α M i (b ⊗ₜ[R.obj U, (α.app U).hom] m) =
      S.map i b ⊗ₜ[R.obj V, (α.app V).hom] M.map i m := by
  let : Module (R.obj V) (S.obj V) :=
    Module.compHom (S.obj V) (α.app V).hom
  let T := (ModuleCat.restrictScalars (S.map i).hom).obj
    ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V))
  let : Module (R.obj U) T := Module.compHom T (α.app U).hom
  let : Module (R.obj U) (S.obj U) :=
    Module.compHom (S.obj U) (α.app U).hom
  unfold tensorRestriction
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  change S.map i b •
    ((1 : S.obj V) ⊗ₜ[R.obj V, (α.app V).hom] M.map i m) = _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

private noncomputable def tensorPresheaf (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    PresheafOfModules.{u} (S ⋙ forget₂ _ _) where
  obj U := (ModuleCat.extendScalars (α.app U).hom).obj (M.obj U)
  map i := tensorRestriction R S α M i
  map_id U := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    rw [tensorRestriction_tmul]
    simp
    rfl
  map_comp {U V W} i j := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    simp only [ModuleCat.comp_apply, tensorRestriction_tmul]
    change _ = tensorRestriction R S α M j _
    erw [tensorRestriction_tmul]
    simp
    rfl

private noncomputable def tensorToRestrict
    (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (N : PresheafOfModules.{u} (S ⋙ forget₂ _ _))
    (f : tensorPresheaf R S α M ⟶ N) : M ⟶ (PresheafOfModules.restrictScalars a).obj N where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
    (α.app U).hom (f.app U)
  naturality := by
    intro U V i
    ext m
    change f.app V ((1 : S.obj V) ⊗ₜ[R.obj V,
      (α.app V).hom] M.map i m) =
      N.map i (f.app U ((1 : S.obj U) ⊗ₜ[R.obj U,
        (α.app U).hom] m))
    rw [← PresheafOfModules.naturality_apply f i]
    change _ = f.app V (tensorRestriction R S α M i _)
    rw [tensorRestriction_tmul]
    simp

private noncomputable def tensorFromRestrict
    (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (N : PresheafOfModules.{u} (S ⋙ forget₂ _ _))
    (g : M ⟶ (PresheafOfModules.restrictScalars a).obj N) : tensorPresheaf R S α M ⟶ N where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    («R» := R.obj U) («S» := S.obj U) (α.app U).hom (g.app U)
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      («R» := R.obj V) («S» := S.obj V) (α.app V).hom (g.app V)
        (tensorRestriction R S α M i _) =
      N.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        («R» := R.obj U) («S» := S.obj U) (α.app U).hom (g.app U) _)
    rw [tensorRestriction_tmul]
    simp only [map_one]
    let : Module (R.obj V) (S.obj V) :=
      Module.compHom (S.obj V) (α.app V).hom
    let : Module (R.obj V) (N.obj V) :=
      Module.compHom (N.obj V) (α.app V).hom
    let : Module (R.obj U) (S.obj U) :=
      Module.compHom (S.obj U) (α.app U).hom
    let : Module (R.obj U) (N.obj U) :=
      Module.compHom (N.obj U) (α.app U).hom
    erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := R.obj V) («S» := S.obj V), TensorProduct.lift.tmul,
      ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := R.obj U) («S» := S.obj U), TensorProduct.lift.tmul]
    change (1 : S.obj V) • (show N.obj V from g.app V (M.map i m)) =
      N.map i ((1 : S.obj U) • (show N.obj U from g.app U m))
    simp only [one_smul]
    exact PresheafOfModules.naturality_apply g i m

private noncomputable def tensorHomEquiv
    (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (N : PresheafOfModules.{u} (S ⋙ forget₂ _ _)) :
    (tensorPresheaf R S α M ⟶ N) ≃ (M ⟶ (PresheafOfModules.restrictScalars a).obj N) where
  toFun := tensorToRestrict R S α M N
  invFun := tensorFromRestrict R S α M N
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (α.app U).hom).left_inv _
  right_inv g := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (α.app U).hom).right_inv _

private theorem tensorHomEquiv_symm_tmul
    (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (N : PresheafOfModules.{u} (S ⋙ forget₂ _ _))
    (g : M ⟶ (PresheafOfModules.restrictScalars a).obj N) (U : Dᵒᵖ)
    (b : S.obj U) (m : M.obj U) :
    ((tensorHomEquiv R S α M N).symm g).app U
      (b ⊗ₜ[R.obj U, (α.app U).hom] m) =
        b • (show N.obj U from g.app U m) := by
  let : Module (R.obj U) (S.obj U) :=
    Module.compHom (S.obj U) (α.app U).hom
  let : Module (R.obj U) (N.obj U) :=
    Module.compHom (N.obj U) (α.app U).hom
  change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    («R» := R.obj U) («S» := S.obj U) (α.app U).hom (g.app U) _ = _
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
    («R» := R.obj U) («S» := S.obj U), TensorProduct.lift.tmul]
  rfl

private noncomputable def tensorFunctor :
    PresheafOfModules.{u} (R ⋙ forget₂ _ _) ⥤
      PresheafOfModules.{u} (S ⋙ forget₂ _ _) :=
  Adjunction.leftAdjointOfEquiv (tensorHomEquiv R S α) (by intros; rfl)

private theorem tensorFunctor_map_tmul
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (g : M ⟶ N)
    (U : Dᵒᵖ) (b : S.obj U) (x : M.obj U) :
    ((tensorFunctor R S α).map g).app U (b ⊗ₜ[R.obj U, (α.app U).hom] x) =
      b ⊗ₜ[R.obj U, (α.app U).hom] (g.app U x) := by
  change ((tensorHomEquiv R S α M (tensorPresheaf R S α N)).symm
    (g ≫ tensorHomEquiv R S α N (tensorPresheaf R S α N) (𝟙 _))).app U _ = _
  rw [tensorHomEquiv_symm_tmul]
  change b • ((1 : S.obj U) ⊗ₜ[R.obj U, (α.app U).hom] (g.app U x)) = _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

private noncomputable def tensorAdjunction :
    tensorFunctor R S α ⊣ PresheafOfModules.restrictScalars a :=
  Adjunction.adjunctionOfEquivLeft (tensorHomEquiv R S α) (by intros; rfl)

private instance tensorFunctor_additive : (tensorFunctor R S α).Additive :=
  (tensorAdjunction R S α).left_adjoint_additive

private noncomputable def tensorPushAdjunction : tensorFunctor R S α ⊣ push := by
  change tensorFunctor R S α ⊣ PresheafOfModules.restrictScalars a
  exact tensorAdjunction R S α

private noncomputable def tensorPullbackIso : tensorFunctor R S α ≅ pull := by
  exact Adjunction.leftAdjointUniq (F := tensorFunctor R S α) (F' := pull) (G := push)
    (tensorPushAdjunction R S α) adjP

private instance tensorPullback_additive : (pull).Additive :=
  Functor.additive_of_iso (tensorPullbackIso R S α)

private theorem presheaf_quasiIso_of_evaluation
    {L M : CochainComplex (PresheafOfModules.{u} (S ⋙ forget₂ _ _)) ℤ}
    (q : L ⟶ M)
    (hq : ∀ U : Dᵒᵖ,
      QuasiIso (((PresheafOfModules.evaluation (S ⋙ forget₂ _ _) U).mapHomologicalComplex
        (.up ℤ)).map q)) : QuasiIso q := by
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology q
    (PresheafOfModules.toPresheaf (S ⋙ forget₂ _ _))).mp
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro U
  have := hq U
  exact HomologicalComplex.quasiIso_map_of_preservesHomology
    (((PresheafOfModules.evaluation (S ⋙ forget₂ _ _) U).mapHomologicalComplex
      (.up ℤ)).map q) (forget₂ (ModuleCat (S.obj U)) AddCommGrpCat)

end TensorPresheaf

/-- The explicit global-section scalar extension preserves a quasi-isomorphism
between K-flat complexes. No Čech models or augmentations are involved.
Source: Stacks Project, Cohomology on Sites, Tags 06YS and 06YT; algebraization.tex,
Tag 099E, final paragraph.
(auxiliary; not a blueprint node).

Proof: form the sectionwise tensor-presheaf functor along the global evaluation map.
Its explicit extension/restriction adjunction identifies it naturally with the chosen
presheaf pullback. At each site object X, the bottom-site sheafification unit identifies
its image of a constant complex with evaluation of the explicit one-point scalar
extension along A to O(X). The identifications commute with differentials and with alpha,
as checked on the generating tensors with first coordinate one. This scalar-extension
functor has definitionally the objects and maps of changeOfRings, so the existing
changeOfRings_kFlat_quasiIso theorem applies directly to the two K-flat hypotheses.
Exact evaluation on the bottom site preserves its quasi-isomorphism. Presheaf exactness
is objectwise, so the sectionwise conclusions assemble to a quasi-isomorphism of module
presheaf complexes. Naturality of the adjunction uniqueness isomorphism transports it
to the chosen pullback. Exact module sheafification gives ringFamilyGlobalExtension.
No flatness of O(X) over A is assumed. The same proof covers an empty site, zero rings
and zero complexes. -/
theorem ringFamilyGlobalExtension_quasiIso_of_kflat
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    {P Q : CochainComplex (RingSiteModules (ringFamilyGlobalRing O)) ℤ}
    (α : P ⟶ Q) (hP : P.IsKFlatIndependentCoefficients)
    (hQ : Q.IsKFlatIndependentCoefficients) (hα : QuasiIso α) :
    QuasiIso (((ringFamilyGlobalExtension O).mapHomologicalComplex (.up ℤ)).map α) := by
  let A := ringFamilyGlobalRing O
  let R := (Functor.const Cᵒᵖ).obj A
  let a := ringFamilyGlobalEvaluation O
  let β : R ⟶ O.obj :=
    { app X := CommRingCat.ofHom (a.app X).hom
      naturality := by
        intro X Y g
        ext x
        exact (x.property g).symm }
  let F := tensorFunctor R O.obj β
  let G := PresheafOfModules.pullback a
  have : G.Additive := ringFamilyGlobalPullback_additive O
  have : (ringFamilyConstantPresheaf O).Additive :=
    ringFamilyConstantPresheaf_additive O
  let T := (ringFamilyConstantPresheaf O).mapHomologicalComplex (.up ℤ)
  let q := (F.mapHomologicalComplex (.up ℤ)).map (T.map α)
  have hq : QuasiIso q := by
    apply presheaf_quasiIso_of_evaluation O.obj
    intro X
    let B := O.obj.obj X
    let φ : A →+* B := (a.app X).hom
    let V := SheafOfModules.forget
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf.{u} (↑B : Type u))) ⋙
      PresheafOfModules.evaluation _ (op ⟨PUnit.unit⟩)
    have : (SheafOfModules.forget
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf.{u} (↑B : Type u)))).IsEquivalence :=
      (bottomModuleEquivalence _).isEquivalence_functor
    let E := PresheafOfModules.evaluation (O.obj ⋙ forget₂ CommRingCat RingCat) X
    let v := ((ringComplexExtension φ).mapHomologicalComplex (.up ℤ)).map α
    have hv : QuasiIso v :=
      SheafOfModules.changeOfRings_kFlat_quasiIso (ringSiteMap φ)
        (ringComplexExtension φ) (fun _ ↦ rfl) (fun _ ↦ rfl) α hP hQ hα
    have hv' : QuasiIso ((V.mapHomologicalComplex (.up ℤ)).map v) := by infer_instance
    let z (K : CochainComplex (RingSiteModules A) ℤ) :
        (E.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj (T.obj K)) ≅
        (V.mapHomologicalComplex (.up ℤ)).obj (ringComplexExtensionComplex φ K) :=
      HomologicalComplex.Hom.isoOfComponents
        (fun n ↦ ringComplexExtensionSections φ (K.X n)) (by
          intro n k _
          apply ModuleCat.ExtendScalars.hom_ext
          intro x
          change ((ringComplexExtension φ).map (K.d n k)).val.app (op ⟨PUnit.unit⟩)
              ((ringComplexExtensionSections φ (K.X n)).hom _) =
            (ringComplexExtensionSections φ (K.X k)).hom
              (((F.map ((ringFamilyConstantPresheaf O).map (K.d n k))).app X) _)
          rw [tensorFunctor_map_tmul]
          exact ringComplexExtension_map_one_tmul φ (K.d n k) x)
    have hz : (E.mapHomologicalComplex (.up ℤ)).map q ≫ (z Q).hom =
        (z P).hom ≫ (V.mapHomologicalComplex (.up ℤ)).map v := by
      ext n : 1
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change (ringComplexExtensionSections φ (Q.X n)).hom
          (((F.map ((ringFamilyConstantPresheaf O).map (α.f n))).app X) _) =
        ((ringComplexExtension φ).map (α.f n)).val.app (op ⟨PUnit.unit⟩)
          ((ringComplexExtensionSections φ (P.X n)).hom _)
      rw [tensorFunctor_map_tmul]
      exact (ringComplexExtension_map_one_tmul φ (α.f n) x).symm
    have hc : QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map q ≫ (z Q).hom) := by
      rw [hz]
      infer_instance
    exact quasiIso_of_comp_right _ (z Q).hom
  let e := NatIso.mapHomologicalComplex (tensorPullbackIso R O.obj β) (.up ℤ)
  have hg : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map (T.map α)) := by
    have he : q ≫ e.hom.app (T.obj Q) = e.hom.app (T.obj P) ≫
        (G.mapHomologicalComplex (.up ℤ)).map (T.map α) :=
      e.hom.naturality (T.map α)
    have hc : QuasiIso (e.hom.app (T.obj P) ≫
        (G.mapHomologicalComplex (.up ℤ)).map (T.map α)) := by
      exact he ▸ (inferInstance : QuasiIso (q ≫ e.hom.app (T.obj Q)))
    exact quasiIso_of_comp_left (e.hom.app (T.obj P)) _
  let S := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  have : S.Additive := (PresheafOfModules.sheafificationAdjunction _).left_adjoint_additive
  exact HomologicalComplex.quasiIso_map_of_preservesHomology
    ((G.mapHomologicalComplex (.up ℤ)).map (T.map α)) S

end CategoryTheory
