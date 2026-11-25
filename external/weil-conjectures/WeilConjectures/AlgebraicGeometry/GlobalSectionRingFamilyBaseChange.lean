/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.GlobalSectionScalarExtension
public import WeilConjectures.AlgebraicGeometry.RingComplexSemilinearExtension
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.AlgebraicGeometry.RingComplexCechBaseChange

/-! # Sheafifying the sectionwise base-change comparison of a ring-complex family

Source: Stacks Project, algebraization.tex, Tags 099D(c), 099E.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u wA
open CategoryTheory AlgebraicGeometry Opposite
namespace CategoryTheory

private theorem transpose_complex_f
    {D E : Type*} [Category D] [Category E] [Preadditive D] [Preadditive E]
    {L : D ⥤ E} {V : E ⥤ D} (adj : L ⊣ V) [L.Additive] [V.Additive]
    {M : CochainComplex D ℤ} {N : CochainComplex E ℤ}
    (g : M ⟶ (V.mapHomologicalComplex (.up ℤ)).obj N) (n : ℤ) :
    (((adj.mapHomologicalComplex (.up ℤ)).homEquiv M N).symm g).f n =
      (adj.homEquiv (M.X n) (N.X n)).symm (g.f n) := by
  simp only [Adjunction.homEquiv_counit, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, Adjunction.mapHomologicalComplex_counit_app_f]

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

local instance tensorRestrictionModule (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
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

private theorem tensorPushAdjunction_symm_tmul
    (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (N : PresheafOfModules.{u} (S ⋙ forget₂ _ _))
    (g : M ⟶ (push).obj N) (U : Dᵒᵖ) (b : S.obj U) (x : M.obj U) :
    (((tensorPushAdjunction R S α).homEquiv M N).symm g).app U
      (b ⊗ₜ[R.obj U, (α.app U).hom] x) =
        b • (show N.obj U from g.app U x) := by
  simp only [tensorPushAdjunction, tensorAdjunction, Adjunction.adjunctionOfEquivLeft,
    id, Adjunction.mkOfHomEquiv_homEquiv]
  convert tensorHomEquiv_symm_tmul R S α M N g U b x using 1

private theorem tensorPullbackIso_transpose
    (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    (N : PresheafOfModules.{u} (S ⋙ forget₂ _ _)) (g : M ⟶ (push).obj N) :
    (tensorPullbackIso R S α).hom.app M ≫ ((adjP).homEquiv M N).symm g =
      ((tensorPushAdjunction R S α).homEquiv M N).symm g := by
  apply ((tensorPushAdjunction R S α).homEquiv M N).injective
  dsimp only [tensorPullbackIso]
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app,
    ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

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

attribute [local instance] ringFamilyConstantPresheaf_additive
  ringFamilyGlobalPushforward_additive ringFamilyGlobalPullback_additive
  ringFamilyGlobalExtension_additive

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})
variable (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
variable (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
variable (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections)
variable (P : CochainComplex (RingSiteModules (ringFamilyGlobalRing O)) ℤ)
variable (p : P ⟶ K (ringFamilyGlobalRing O) (ringFamilyGlobalIdeal O r f))

/-- The restricted comparison, before scalar extension, in one degree.
Source: Stacks Project, Tags 099D(a),(b), 099E.
(auxiliary; not a blueprint node). -/
noncomputable def ringFamilyGlobalRestrictedTerm (n : ℤ) :
    (ringFamilyConstantPresheaf O).obj (P.X n) ⟶
      (PresheafOfModules.pushforward (ringFamilyGlobalEvaluation O)).obj
        ((ringFamilyPresheafComplex O K ε m hm r f).X n) where
  app X := by
    change (P.X n).val.obj (op ⟨PUnit.unit⟩) ⟶
      (ModuleCat.restrictScalars ((ringFamilyGlobalEvaluation O).app X).hom).obj
        (((K (O.obj.obj X) (ringFamilySectionIdeal O r f X)).X n).val.obj
          (op ⟨PUnit.unit⟩))
    exact (ModuleCat.semilinearMapAddEquiv ((ringFamilyGlobalEvaluation O).app X).hom _ _)
      { toFun := fun x ↦ m _ _ ((ringFamilyGlobalEvaluation O).app X).hom
          (ringFamilyGlobalIdeal O r f) (ringFamilySectionIdeal O r f X)
          (ringFamilyGlobalIdeal_map O r f X) n ((p.f n).val.app (op ⟨PUnit.unit⟩) x)
        map_add' := by intro x y; rw [map_add, map_add]
        map_smul' := by intro a x; rw [map_smul, map_smulₛₗ]; rfl }
  naturality {X Y} a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change m _ _ ((ringFamilyGlobalEvaluation O).app Y).hom _ _
        (ringFamilyGlobalIdeal_map O r f Y) n ((p.f n).val.app _ x) =
      m _ _ (O.obj.map a).hom _ _ (ringFamilySectionIdeal_map O r f a) n
        (m _ _ ((ringFamilyGlobalEvaluation O).app X).hom _ _
          (ringFamilyGlobalIdeal_map O r f X) n ((p.f n).val.app _ x))
    have hφ : ((ringFamilyGlobalEvaluation O).app Y).hom =
        (O.obj.map a).hom.comp ((ringFamilyGlobalEvaluation O).app X).hom := by
      ext s
      exact (s.property a).symm
    generalize ringFamilyGlobalIdeal_map O r f Y = h
    revert h
    rw [hφ]
    intro h
    exact (hm.2.2.2 _ _ _ _ _ _ _ _ _ _ h n _).symm

/-- The semilinear comparison is a chain map into scalar restriction.
Source: Stacks Project, Tags 099D(a),(b), 099E.
(auxiliary; not a blueprint node). -/
noncomputable def ringFamilyGlobalRestrictedMap :
    ((ringFamilyConstantPresheaf O).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((PresheafOfModules.pushforward (ringFamilyGlobalEvaluation O)).mapHomologicalComplex
        (.up ℤ)).obj (ringFamilyPresheafComplex O K ε m hm r f) where
  f := ringFamilyGlobalRestrictedTerm O K ε m hm r f P p
  comm' n k _ := by
    ext X x
    have hp := ConcreteCategory.congr_hom
      (congrArg (fun z ↦ z.val.app (op ⟨PUnit.unit⟩)) (p.comm n k).symm) x
    change (p.f k).val.app _ ((P.d n k).val.app _ x) =
      ((K (ringFamilyGlobalRing O) (ringFamilyGlobalIdeal O r f)).d n k).val.app
        (op ⟨PUnit.unit⟩) ((p.f n).val.app _ x) at hp
    change ((K (O.obj.obj X) (ringFamilySectionIdeal O r f X)).d n k).val.app
        (op ⟨PUnit.unit⟩)
        (m _ _ _ _ _ (ringFamilyGlobalIdeal_map O r f X) n ((p.f n).val.app _ x)) =
      m _ _ _ _ _ (ringFamilyGlobalIdeal_map O r f X) k
        ((p.f k).val.app _ ((P.d n k).val.app _ x))
    rw [hp]
    exact (hm.1 _ _ _ _ _ (ringFamilyGlobalIdeal_map O r f X) n k _).symm

/-- Extend and sheafify the explicit restricted comparison by adjunction.
Source: Stacks Project, Tags 099D(c), 099E.
(auxiliary; not a blueprint node). -/
noncomputable def ringFamilyGlobalComparison :
    ringFamilyGlobalExtensionComplex O P ⟶ (ringFamilySheafModel O K ε m hm r f).1 := by
  let R := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let S := PresheafOfModules.sheafification (𝟙 R.obj)
  let : S.Additive := (PresheafOfModules.sheafificationAdjunction _).left_adjoint_additive
  let t := (((PresheafOfModules.pullbackPushforwardAdjunction
    (ringFamilyGlobalEvaluation O)).mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm
      (ringFamilyGlobalRestrictedMap O K ε m hm r f P p)
  exact (S.mapHomologicalComplex (.up ℤ)).map t

/-- The sectionwise normalized scalar-extension comparison is a quasi-isomorphism.
Source: Stacks Project, Tags 099D(c), 099E.
(auxiliary; not a blueprint node).
Proof: transport the global Cech model across p, apply the augmented base-change theorem,
and use the semilinear pure-tensor normalization and the augmentation clause of hm. -/
theorem ringFamilyGlobalSectionComparison_quasiIso
    [∀ A : CommRingCat.{u}, HasDerivedCategory.{wA} (RingSiteModules A)]
    (hK : ∀ (A : CommRingCat.{u}) (I : {I : Ideal A // I.FG}),
      RingComplexHasCechModel A I.val (K A I) (ε A I))
    (hp : QuasiIso p) (hflat : P.IsKFlatIndependentCoefficients) (X : Cᵒᵖ) :
    QuasiIso (ringComplexExtendAlong ((ringFamilyGlobalEvaluation O).app X).hom K m
      (ringFamilyGlobalIdeal O r f) (ringFamilySectionIdeal O r f X)
      (ringFamilyGlobalIdeal_map O r f X)
      (hm.1 _ _ _ _ _ (ringFamilyGlobalIdeal_map O r f X)) P p) := by
  let A := ringFamilyGlobalRing O
  let B := O.obj.obj X
  let I := ringFamilyGlobalIdeal O r f
  let L := ringFamilySectionIdeal O r f X
  let φ : A →+* B := ((ringFamilyGlobalEvaluation O).app X).hom
  have hP := ringComplexHasCechModel_of_quasiIso (ε A I) p hp (hK A I)
  have hk : P.IsKFlatTensor := hflat
  apply ringComplex_cech_baseChange_quasiIso A B φ I L
    (ringFamilyGlobalIdeal_map O r f X) P (K B L) (p ≫ ε A I) (ε B L) hP (hK B L) hk
  intro x
  erw [ringComplexExtendAlong_one_tmul]
  exact hm.2.1 A B φ I L (ringFamilyGlobalIdeal_map O r f X)
    ((p.f 0).val.app (op ⟨PUnit.unit⟩) x)

open scoped ChangeOfRings TensorProduct in
private theorem globalComparison_quasiIso
    [∀ A : CommRingCat.{u}, HasDerivedCategory.{wA} (RingSiteModules A)]
    (hK : ∀ (A : CommRingCat.{u}) (I : {I : Ideal A // I.FG}),
      RingComplexHasCechModel A I.val (K A I) (ε A I))
    (hp : QuasiIso p) (hflat : P.IsKFlatIndependentCoefficients) :
    QuasiIso (ringFamilyGlobalComparison O K ε m hm r f P p) := by
  let A := ringFamilyGlobalRing O
  let R := (Functor.const Cᵒᵖ).obj A
  let α : R ⟶ O.obj :=
    { app X := CommRingCat.ofHom ((ringFamilyGlobalEvaluation O).app X).hom
      naturality := by
        intro X Y g
        ext x
        exact (x.property g).symm }
  let a := ringFamilyGlobalEvaluation O
  let F := tensorFunctor R O.obj α
  let G := PresheafOfModules.pullback a
  have : G.Additive := ringFamilyGlobalPullback_additive O
  let T := (ringFamilyConstantPresheaf O).mapHomologicalComplex (.up ℤ)
  let M := ringFamilyPresheafComplex O K ε m hm r f
  let t : (G.mapHomologicalComplex (.up ℤ)).obj (T.obj P) ⟶ M :=
    (((PresheafOfModules.pullbackPushforwardAdjunction a).mapHomologicalComplex
      (.up ℤ)).homEquiv _ _).symm (ringFamilyGlobalRestrictedMap O K ε m hm r f P p)
  let e := (NatIso.mapHomologicalComplex (tensorPullbackIso R O.obj α) (.up ℤ)).app
    (T.obj P)
  have hq : QuasiIso (e.hom ≫ t) := by
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
    let v := ringComplexExtendAlong φ K m (ringFamilyGlobalIdeal O r f)
      (ringFamilySectionIdeal O r f X) (ringFamilyGlobalIdeal_map O r f X)
      (hm.1 _ _ _ _ _ (ringFamilyGlobalIdeal_map O r f X)) P p
    have hv : QuasiIso v :=
      ringFamilyGlobalSectionComparison_quasiIso O K ε m hm r f P p hK hp hflat X
    have hv' : QuasiIso ((V.mapHomologicalComplex (.up ℤ)).map v) := by infer_instance
    let z : (E.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj (T.obj P)) ≅
        (V.mapHomologicalComplex (.up ℤ)).obj (ringComplexExtensionComplex φ P) :=
      HomologicalComplex.Hom.isoOfComponents
        (fun n ↦ ringComplexExtensionSections φ (P.X n)) (by
          intro n k _
          apply ModuleCat.ExtendScalars.hom_ext
          intro x
          change ((ringComplexExtension φ).map (P.d n k)).val.app (op ⟨PUnit.unit⟩)
              ((ringComplexExtensionSections φ (P.X n)).hom _) =
            (ringComplexExtensionSections φ (P.X k)).hom
              (((F.map ((ringFamilyConstantPresheaf O).map (P.d n k))).app X) _)
          rw [tensorFunctor_map_tmul]
          exact ringComplexExtension_map_one_tmul φ (P.d n k) x)
    have hz : (E.mapHomologicalComplex (.up ℤ)).map (e.hom ≫ t) =
        z.hom ≫ (V.mapHomologicalComplex (.up ℤ)).map v := by
      ext n : 1
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change (((tensorPullbackIso R O.obj α).hom.app ((T.obj P).X n)) ≫
        t.f n).app X _ = _
      dsimp only [t]
      rw [transpose_complex_f]
      let Q := (ringFamilyConstantPresheaf O).obj (P.X n)
      let N : PresheafOfModules.{u} (O.obj ⋙ forget₂ CommRingCat RingCat) := M.X n
      let g : Q ⟶ (PresheafOfModules.pushforward
          (R := O.obj ⋙ forget₂ CommRingCat RingCat)
          (S := R ⋙ forget₂ CommRingCat RingCat) (F := 𝟭 C)
          (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).obj N :=
        ringFamilyGlobalRestrictedTerm O K ε m hm r f P p n
      change (((tensorPullbackIso R O.obj α).hom.app Q) ≫
        (((PresheafOfModules.pullbackPushforwardAdjunction
          (R := O.obj ⋙ forget₂ CommRingCat RingCat)
          (S := R ⋙ forget₂ CommRingCat RingCat) (F := 𝟭 C)
          (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).homEquiv Q N).symm g)).app
            X _ = _
      calc
        _ = ((((tensorPushAdjunction R O.obj α).homEquiv Q N).symm g).app X
            ((1 : O.obj.obj X) ⊗ₜ[R.obj X, (α.app X).hom] x)) :=
          congrArg (fun q ↦ q.app X ((1 : O.obj.obj X) ⊗ₜ[R.obj X, (α.app X).hom] x))
            (tensorPullbackIso_transpose R O.obj α Q N g)
        _ = g.app X x :=
          (tensorPushAdjunction_symm_tmul R O.obj α Q N g X 1 x).trans (one_smul _ _)
        _ = _ := (ringComplexExtendAlong_one_tmul φ K m
          (ringFamilyGlobalIdeal O r f) (ringFamilySectionIdeal O r f X)
          (ringFamilyGlobalIdeal_map O r f X)
          (hm.1 _ _ _ _ _ (ringFamilyGlobalIdeal_map O r f X)) P p n x).symm
    rw [hz]
    infer_instance
  have ht : QuasiIso t := (quasiIso_iff_comp_left e.hom t).mp hq
  let S := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  have : S.Additive := (PresheafOfModules.sheafificationAdjunction _).left_adjoint_additive
  exact HomologicalComplex.quasiIso_map_of_preservesHomology t S

private theorem globalUnit_transpose_apply (X : Cᵒᵖ) (x : ringFamilyGlobalRing O) :
    (((PresheafOfModules.pullbackPushforwardAdjunction
        (ringFamilyGlobalEvaluation O)).homEquiv _ _)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).homEquiv _ _)
          (ringFamilyGlobalExtensionUnit O))).app X x = x.val X := by
  unfold ringFamilyGlobalExtensionUnit
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

private theorem globalComparison_augmentation :
    ringFamilyGlobalComparison O K ε m hm r f P p ≫
        (ringFamilySheafModel O K ε m hm r f).2 =
      ringFamilyGlobalExtensionAugmentation O
        (p ≫ ε (ringFamilyGlobalRing O) (ringFamilyGlobalIdeal O r f)) := by
  let R := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let S := PresheafOfModules.sheafification (𝟙 R.obj)
  let adjS := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  have : S.Additive := adjS.left_adjoint_additive
  let adj := PresheafOfModules.pullbackPushforwardAdjunction (ringFamilyGlobalEvaluation O)
  let a := p ≫ ε (ringFamilyGlobalRing O) (ringFamilyGlobalIdeal O r f)
  apply HomologicalComplex.to_single_hom_ext
  change S.map _ ≫ ((adjS.homEquiv _ _).symm _) =
    S.map ((PresheafOfModules.pullback (ringFamilyGlobalEvaluation O)).map
      ((ringFamilyConstantPresheaf O).map (a.f 0))) ≫ ringFamilyGlobalExtensionUnit O
  apply (adjS.homEquiv _ _).injective
  rw [adjS.homEquiv_naturality_left, Equiv.apply_symm_apply,
    adjS.homEquiv_naturality_left]
  rw [transpose_complex_f]
  change ((adj.homEquiv _ _).symm
    (ringFamilyGlobalRestrictedTerm O K ε m hm r f P p 0)) ≫
      (ringFamilyPresheafAugmentation O K ε m hm r f).f 0 = _
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply,
    adj.homEquiv_naturality_left]
  ext X x
  change ringComplexAugmentationValue
      (ε (O.obj.obj X) (ringFamilySectionIdeal O r f X))
      (m _ _ ((ringFamilyGlobalEvaluation O).app X).hom _ _
        (ringFamilyGlobalIdeal_map O r f X) 0
          ((p.f 0).val.app (op ⟨PUnit.unit⟩) x)) =
    (((PresheafOfModules.pullbackPushforwardAdjunction
        (ringFamilyGlobalEvaluation O)).homEquiv _ _)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).homEquiv _ _)
          (ringFamilyGlobalExtensionUnit O))).app X
            ((a.f 0).val.app (op ⟨PUnit.unit⟩) x)
  rw [globalUnit_transpose_apply]
  exact hm.2.1 _ _ _ _ _ (ringFamilyGlobalIdeal_map O r f X)
    ((p.f 0).val.app (op ⟨PUnit.unit⟩) x)

/-- Base change from the global ring to all section rings assembles to an augmented
quasi-isomorphism after sheafification. Only sectionwise Cech models are used here;
there is no identification with the tensor Cech complex of sheaves.

Source: Stacks Project, algebraization.tex, Tag 099D(c) and Tag 099E, final paragraph.
(auxiliary; not a blueprint node).

Proof: put A = Gamma(O), I = (f_1,...,f_r), and phi_V : A to O(V) for evaluation.
Evaluation takes I to the ideal generated by the values f_i(V). Compose p with the
specified semilinear map of K for phi_V. The chain equation in hm makes this a semilinear
chain map. Extend it by b tensor x mapping to b times m(phi_V)(p(x)). The composition
equation in hm, evaluated on the pure tensors, proves that these maps commute with
restriction, so they assemble to a morphism of O-module presheaf complexes. The identity
and composition laws include all identity restrictions. The augmentation equation in hm
says on pure tensors that its composite with the target augmentation is multiplication
followed by the extension of p composed with epsilon. Transport hK at A backwards across
p by ringComplexHasCechModel_of_quasiIso. Apply ringComplex_cech_baseChange_quasiIso to
this model, hK at O(V), and the extended map; its pure-tensor normalization is precisely
the augmentation equation just verified. Each evaluated map is a quasi-isomorphism.
Exactness is objectwise in module presheaves, and module sheafification is exact, so the
assembled sheaf map is a quasi-isomorphism. By the two adjunctions, the source is exactly
ringFamilyGlobalExtensionComplex O P. Naturality of adjoint transposition identifies its
augmentation with ringFamilyGlobalExtensionAugmentation O (p composed with epsilon).
The argument needs no point of the site; on the empty site it is vacuous. An empty list,
zero or repeated generators, and zero rings use the same ideal-map and tensor formulas. -/
theorem ringFamilyGlobalExtension_to_family
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [∀ A : CommRingCat.{u}, HasDerivedCategory.{wA} (RingSiteModules A)]
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (hK : ∀ (A : CommRingCat.{u}) (I : {I : Ideal A // I.FG}),
      RingComplexHasCechModel A I.val (K A I) (ε A I))
    (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (P : CochainComplex (RingSiteModules (ringFamilyGlobalRing O)) ℤ)
    (p : P ⟶ K (ringFamilyGlobalRing O) (ringFamilyGlobalIdeal O r f))
    (hp : QuasiIso p) (hflat : P.IsKFlatIndependentCoefficients) :
    QuasiIso (ringFamilyGlobalComparison O K ε m hm r f P p) ∧
      ringFamilyGlobalComparison O K ε m hm r f P p ≫
        (ringFamilySheafModel O K ε m hm r f).2 =
        ringFamilyGlobalExtensionAugmentation O
          (p ≫ ε (ringFamilyGlobalRing O) (ringFamilyGlobalIdeal O r f)) := by
  exact ⟨globalComparison_quasiIso O K ε m hm r f P p hK hp hflat,
    globalComparison_augmentation O K ε m hm r f P p⟩

end CategoryTheory
