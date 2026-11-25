/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianCounitCocycleDefinitions
import WeilConjectures.AlgebraicGeometry.AbelianExtSectionsCocycleNormalization
import WeilConjectures.AlgebraicGeometry.TerminalSourceSectionsEvaluation
import WeilConjectures.CategoryTheory.ExactFunctorResolutionCocycle

/-! # The injective-resolution cocycle calculation used by the abelian counit

Source: Stacks Project, Tags 01F7 and 06XR.
(blueprint: new-abelian-injective-counit-cocycle)

The remaining calculation is the canonical representative computation for two
actual abelian injective resolutions. It is separated from the parent theorem
so that source replacement and arbitrary acyclic-resolution comparison remain
independent arguments.
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
attribute [local instance] AlgebraicGeometry.Scheme.Modules.instAddCommGroupH
attribute [local irreducible] siteSectionsObjIso extRightDerivedHomObjIso
attribute [local irreducible] Functor.rightDerivedObjIsoOfResolution
attribute [local irreducible] InjectiveResolution.isoRightDerivedObj
local instance injective_cocycle_pushforward_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (abelianPushforward f).Additive :=
  ⟨by intros; ext U x; rfl⟩

private theorem constantSheafAdj_eval
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') (k : T' ⟶ T)
    (A : AddCommGrpCat.{u}) (N : Sheaf J AddCommGrpCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (a : (constantSheaf J AddCommGrpCat.{u}).obj A ⟶ N) :
    (constantSheafAdj J AddCommGrpCat.{u} hT).homEquiv A N a ≫ N.obj.map k.op =
      (constantSheafAdj J AddCommGrpCat.{u} hT').homEquiv A N a := by
  have hformula {S : C} (hS : IsTerminal S) :
      (constantSheafAdj J AddCommGrpCat.{u} hS).homEquiv A N a =
        (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op S) ≫ a.hom.app (op S) := by
    rw [Adjunction.homEquiv_unit]
    simp [constantSheafAdj, Adjunction.comp]
  rw [hformula hT, hformula hT', Category.assoc, ← a.hom.naturality, ← Category.assoc]
  have h := (toSheafify J ((Functor.const Cᵒᵖ).obj A)).naturality k.op
  simpa using congrArg (fun t ↦ t ≫ a.hom.app (op T')) h.symm

private theorem zariski_section_adjunction_transfer {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (N : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (b : (invImage f).obj M ⟶ N)
    (a : (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ M) :
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ N ((constIso f).inv ≫ (invImage f).map a ≫ b) =
    (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ M a ≫
        ((abelianAdjunction f).homEquiv M N b).hom.app (op ⊤) ≫
        N.obj.map (eqToHom (by simp) : op (f ⁻¹ᵁ (⊤ : Y.Opens)) ⟶ op (⊤ : X.Opens)) := by
  let adjY := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    isTerminalTop
  let adjX := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    (T := (Opens.map f.base).obj (⊤ : Y.Opens)) isTerminalTop
  let adj := abelianAdjunction f
  let e := (Opens.map f.base).sheafPushforwardContinuousCompSheafSectionsObjIso
    AddCommGrpCat.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    (op (⊤ : Y.Opens))
  let adjC := (adjY.comp adj).ofNatIsoRight e
  have hh : adjX.homEquiv _ N
      ((Adjunction.leftAdjointUniq adjC adjX).inv.app _ ≫ (invImage f).map a ≫ b) =
      adjC.homEquiv _ N ((invImage f).map a ≫ b) := by
    rw [Adjunction.leftAdjointUniq_inv_app, adjX.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, adjC.homEquiv_apply]
    rfl
  change adjX.homEquiv _ N ((constIso f).inv ≫ (invImage f).map a ≫ b) = _ at hh
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hh
  change adjX.homEquiv _ N ((constIso f).inv ≫ (invImage f).map a ≫ b) =
    adjY.homEquiv _ _ (adj.homEquiv _ _ ((invImage f).map a ≫ b)) ≫ e.hom.app N at hh
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at hh
  let k : (⊤ : X.Opens) ⟶ (Opens.map f.base).obj (⊤ : Y.Opens) := eqToHom (by simp)
  have hs := congrArg (fun t ↦ t ≫ N.obj.map k.op) hh
  erw [constantSheafAdj_eval (Opens.grothendieckTopology X)
    isTerminalTop isTerminalTop k _ N
      ((constIso f).inv ≫ (invImage f).map a ≫ b)] at hs
  have hk : k.op =
      (eqToHom (by simp) : op (f ⁻¹ᵁ (⊤ : Y.Opens)) ⟶ op (⊤ : X.Opens)) :=
    Subsingleton.elim _ _
  rw [hk] at hs
  rw [adjY.homEquiv_naturality_right] at hs
  change (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ N ((constIso f).inv ≫ (invImage f).map a ≫ b) =
    adjY.homEquiv _ M a ≫
      ((adj.homEquiv M N) b).hom.app (op ⊤) ≫
      N.obj.map (eqToHom (by simp) : op (f ⁻¹ᵁ (⊤ : Y.Opens)) ⟶ op (⊤ : X.Opens)) at hs
  exact hs

private theorem zariski_section_transfer_s {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (N : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (b : (invImage f).obj M ⟶ N)
    (a : (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ M)
    (s : abelianPushforward f ⋙ abelianSections Y ≅ abelianSections X)
    (hs : ∀ G, s.hom.app G = G.obj.map
      (eqToHom (by simp) : op (f ⁻¹ᵁ (⊤ : Y.Opens)) ⟶ op (⊤ : X.Opens))) :
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ N ((constIso f).inv ≫ (invImage f).map a ≫ b) =
    (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ M a ≫
        ((abelianAdjunction f).homEquiv M N b).hom.app (op ⊤) ≫ s.hom.app N := by
  rw [hs]
  exact zariski_section_adjunction_transfer f M N b a

private theorem ext_inverse_image_coefficient {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (N : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (I : InjectiveResolution M) (R : InjectiveResolution N)
    (c : (invImage f).obj M ⟶ N)
    (L : ((invImage f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ R.cocomplex)
    (hL : (invImage f).map (I.ι.f 0) ≫ L.f 0 = c ≫ R.ι.f 0)
    (p : ℕ)
    (a : (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I.cocomplex.X p)
    (ha : a ≫ I.cocomplex.d p (p + 1) = 0) :
    ∃ hb : ((constIso f).inv ≫ (invImage f).map a ≫ L.f p) ≫
        R.cocomplex.d p (p + 1) = 0,
      Sheaf.H.map c p (Sheaf.H.mapFunctor (invImage f) (constIso f).symm M p
        (I.extMk a (p + 1) rfl ha)) =
      R.extMk ((constIso f).inv ≫ (invImage f).map a ≫ L.f p) (p + 1) rfl hb := by
  have hb : ((invImage f).map a ≫ L.f p) ≫ R.cocomplex.d p (p + 1) = 0 := by
    rw [Category.assoc, L.comm p (p + 1)]
    change (invImage f).map a ≫ (invImage f).map (I.cocomplex.d p (p + 1)) ≫
      L.f (p + 1) = 0
    rw [← Category.assoc, ← Functor.map_comp, ha, Functor.map_zero, zero_comp]
  have hc : ((constIso f).inv ≫ (invImage f).map a ≫ L.f p) ≫
      R.cocomplex.d p (p + 1) = 0 := by
    simp only [Category.assoc, hb, comp_zero]
  refine ⟨hc, ?_⟩
  have he := exactFunctor_resolution_cocycle
    (invImage f) c I R L hL p a ha hb
  rw [Sheaf.H.mapFunctor_apply, Sheaf.H.map_apply,
    Abelian.Ext.comp_assoc_of_third_deg_zero, he]
  exact (R.mk₀_comp_extMk ((invImage f).map a ≫ L.f p)
    (p + 1) rfl hb (constIso f).inv)


private theorem injective_resolution_constant_cocycle (X : Scheme.{u})
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (I : InjectiveResolution
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F)) (p : ℕ)
    (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I.cocomplex.X p)
    (ha : a ≫ I.cocomplex.d p (p + 1) = 0)
    (z : (((abelianSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).cycles p)
    (hz : (((abelianSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).iCycles p z =
      AddCommGrpCat.uliftZMultiplesAddEquiv _
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).homAddEquiv _ (I.cocomplex.X p) a)) :
    (abelianInjectiveResolutionIso X F I p).hom (I.extMk a (p + 1) rfl ha) =
      (((abelianSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ p z := by
  have ha' : ((terminalSourceIso X).hom ≫ a) ≫ I.cocomplex.d p (p + 1) = 0 := by
    rw [Category.assoc, ha, comp_zero]
  have hz' : (((abelianSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).iCycles p z =
      (sectionsIso (Opens.grothendieckTopology X) ⊤).hom.app (I.cocomplex.X p)
        ((terminalSourceIso X).hom ≫ a) := by
    rw [terminal_source_sections_evaluation]
    exact hz
  have h := canonical_site_sections_cocycle (Opens.grothendieckTopology X) ⊤ _ I p
    ((terminalSourceIso X).hom ≫ a) ha' z hz'
  delta abelianInjectiveResolutionIso abelianExtSectionsIso
  simp only [Iso.trans_hom, Category.assoc]
  change ((siteSectionsObjIso (Opens.grothendieckTopology X) ⊤ _ p).hom ≫
    (I.isoRightDerivedObj (abelianSections X) p).hom)
      ((Abelian.Ext.mk₀ (terminalSourceIso X).hom).comp
        (I.extMk a (p + 1) rfl ha) (zero_add p)) = _
  rw [I.mk₀_comp_extMk]
  exact h

/-- Inverse image and coefficients on Ext agree with the adjoint section chain map.
Source: Stacks Project, Tags 01F7, 01F8, 01F9 and 06XR.
(blueprint: new-abelian-injective-counit-cocycle)

Proof: Lift a section-homology class to a cycle. The constant-sheaf adjunction
and evaluation of its integer generator turn that cycle into a closed Hom
cocycle. The fixed Ext-to-sections normalization identifies its Ext class.
Apply exactFunctor_resolution_cocycle and precompose the constant-source
isomorphism. The explicit Zariski constant-sheaf adjunction and the prescribed
top-open restriction identify the transferred cocycle with the section chain
map. The target normalization and naturality of the homology projection finish
the calculation. The argument includes degree zero and empty schemes. -/
theorem abelian_injective_counit_cocycle_calculation
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (I : InjectiveResolution
      ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).obj A))
    (c : (invImage f).obj
      ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).obj A) ⟶
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F))
    (R : InjectiveResolution
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F))
    (L : ((invImage f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ R.cocomplex)
    (hL : (invImage f).map (I.ι.f 0) ≫ L.f 0 = c ≫ R.ι.f 0)
    (s : abelianPushforward f ⋙ abelianSections Y ≅
      abelianSections X)
    (hs : ∀ G, s.hom.app G = G.obj.map
      (eqToHom (by simp) : op (f ⁻¹ᵁ (⊤ : Y.Opens)) ⟶ op (⊤ : X.Opens)))
    (p : ℕ) (x : H A p) :
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) p).map
      (((abelianSections Y).mapHomologicalComplex (.up ℕ)).map
        ((NatTrans.mapHomologicalComplex (abelianAdjunction f).unit (.up ℕ)).app
          I.cocomplex ≫
          ((abelianPushforward f).mapHomologicalComplex (.up ℕ)).map L) ≫
        (NatTrans.mapHomologicalComplex s.hom (.up ℕ)).app R.cocomplex))
      ((abelianInjectiveResolutionIso Y A I p).hom x) =
    (abelianInjectiveResolutionIso X F R p).hom
      (Sheaf.H.map c p (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
        ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).obj A) p x)) := by
  let K := ((abelianSections Y).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let B := ((abelianSections X).mapHomologicalComplex (.up ℕ)).obj R.cocomplex
  let t : K ⟶ B := ((abelianSections Y).mapHomologicalComplex (.up ℕ)).map
    ((NatTrans.mapHomologicalComplex (abelianAdjunction f).unit (.up ℕ)).app I.cocomplex ≫
      ((abelianPushforward f).mapHomologicalComplex (.up ℕ)).map L) ≫
      (NatTrans.mapHomologicalComplex s.hom (.up ℕ)).app R.cocomplex
  let eY := fun n ↦ ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    isTerminalTop).homAddEquiv _ (I.cocomplex.X n)).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  let a := fun z : K.cycles p ↦ (eY p).symm (K.iCycles p z)
  have ha : ∀ z, a z ≫ I.cocomplex.d p (p + 1) = 0 := by
    intro z
    apply (eY (p + 1)).injective
    change AddCommGrpCat.uliftZMultiplesAddEquiv _
      (((constantSheafAdj _ _ _).homAddEquiv _ _) (a z ≫ I.cocomplex.d p (p + 1))) = _
    simp only [Adjunction.homAddEquiv_apply]
    rw [Adjunction.homEquiv_naturality_right]
    change (K.d p (p + 1)) (eY p (a z)) = _
    rw [AddEquiv.apply_symm_apply]
    have h := ConcreteCategory.congr_hom (K.iCycles_d p (p + 1)) z
    simpa only [ConcreteCategory.comp_apply, map_zero, AddCommGrpCat.zero_apply] using h
  let repr := fun z ↦ I.extMk (a z) (p + 1) rfl (ha z)
  apply homology_transfer_of_cycle_representatives K B t p
    (abelianInjectiveResolutionIso Y A I p).hom
    ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)
    (abelianInjectiveResolutionIso X F R p).hom
    (fun y ↦ Sheaf.H.map c p (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
      ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).obj A) p y)) repr
    (fun z ↦ injective_resolution_constant_cocycle Y A I p (a z) (ha z) z
      ((eY p).apply_symm_apply _).symm) ?_ x
  intro z
  have hzrep : K.iCycles p z = eY p (a z) := ((eY p).apply_symm_apply _).symm
  obtain ⟨ha', ht⟩ := ext_inverse_image_coefficient f _ _ I R c L hL p (a z) (ha z)
  let a' := (constIso f).inv ≫ (invImage f).map (a z) ≫ L.f p
  have hrep : B.iCycles p (HomologicalComplex.cyclesMap t p z) =
      AddCommGrpCat.uliftZMultiplesAddEquiv _
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).homAddEquiv _ (R.cocomplex.X p) a') := by
    have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i t p) z
    simp only [ConcreteCategory.comp_apply] at h
    rw [h]
    change _ = AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        isTerminalTop).homEquiv _ (R.cocomplex.X p) a')
    rw [zariski_section_transfer_s f _ _ (L.f p) (a z) s hs]
    change (t.f p) (K.iCycles p z) = (s.hom.app (R.cocomplex.X p))
      (((abelianAdjunction f).homEquiv _ _ (L.f p)).hom.app (op ⊤) (eY p (a z)))
    rw [AddEquiv.apply_symm_apply]
    rfl
  dsimp only [repr]
  rw [ht]
  exact injective_resolution_constant_cocycle X F R p a' ha'
    (HomologicalComplex.cyclesMap t p z) hrep

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
