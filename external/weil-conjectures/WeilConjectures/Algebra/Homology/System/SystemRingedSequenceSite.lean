/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # The ringed sequence site of an arbitrary coefficient system

Source: Zheng, Construction 4.1; Stacks 03DA, 03DB and 06YS.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z zv t
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- The sequence site is essentially small in the coefficient universe.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
instance systemSequenceEssentiallySmall : EssentiallySmall.{w} (ℕ × C) :=
  EssentiallySmall.mk'
    ((AsSmall.equiv : ℕ ≌ AsSmall.{w} ℕ).prod (equivSmallModel.{w} C))

private theorem sequence_sheaf_of_slices
    (P : (ℕ × C)ᵒᵖ ⥤ Type t)
    (hP : ∀ n : ℕ, Presieve.IsSheaf J ((Prod.sectR n C).op ⋙ P)) :
    Presieve.IsSheaf (coefficientSequenceTopology J) P := by
  intro X S hS x hx
  let xv : Presieve.FamilyOfElements ((Prod.sectR X.1 C).op ⋙ P)
      (S.functorPullback (Prod.sectR X.1 C)).arrows :=
    fun Y f hf ↦ x ((Prod.sectR X.1 C).map f) hf
  have hxv : xv.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ he
    exact hx ((Prod.sectR X.1 C).map g₁) ((Prod.sectR X.1 C).map g₂)
      hf₁ hf₂ (by simpa only [← Functor.map_comp] using
        (congrArg (fun f ↦ (Prod.sectR X.1 C).map f) he))
  obtain ⟨a, ha, hua⟩ := hP X.1 _ hS xv hxv
  refine ⟨a, ?_, ?_⟩
  · intro Y f hf
    apply ((hP Y.1).isSeparated _ (J.pullback_stable f.2 hS)).ext
    intro Z g hg
    let v : (X.1, Z) ⟶ X := (Prod.sectR X.1 C).map (g ≫ f.2)
    let k : (Y.1, Z) ⟶ (X.1, Z) := Prod.mkHom f.1 (𝟙 Z)
    have hv : S v := hg
    have he : k ≫ v = (Prod.sectR Y.1 C).map g ≫ f := by
      ext <;> simp [k, v]
    have hc := hx k ((Prod.sectR Y.1 C).map g) hv hf he
    have hag := congrArg (P.map k.op) (ha (g ≫ f.2) hv)
    change P.map ((Prod.sectR Y.1 C).map g).op (P.map f.op a) = _
    erw [← P.map_comp_apply, ← op_comp, ← he]
    have hp : P.map (k ≫ v).op a = P.map k.op (P.map v.op a) := by
      rw [op_comp, P.map_comp]
      rfl
    exact hp.trans (hag.trans hc)
  · intro b hb
    apply hua b
    intro Y f hf
    exact hb ((Prod.sectR X.1 C).map f) hf

private theorem sequence_uncurry_slice {D : Type z} [Category.{zv} D]
    (F : ℕᵒᵖ ⥤ Cᵒᵖ ⥤ D) (n : ℕ) :
    (Prod.sectR n C).op ⋙ (prodOpEquiv (C := ℕ) (D := C)).functor ⋙
      Functor.uncurry.obj F = F.obj (op n) := by
  apply CategoryTheory.Functor.ext
    (F := (Prod.sectR n C).op ⋙ (prodOpEquiv (C := ℕ) (D := C)).functor ⋙
      Functor.uncurry.obj F) (G := F.obj (op n)) (fun _ ↦ rfl) ?_
  intro X Y f
  change (F.map (𝟙 (op n))).app X ≫ (F.obj (op n)).map f = _
  rw [F.map_id]
  simp

/-- The coefficient ring on the product category, with the actual iterated maps of B.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def systemSequenceRingPresheaf : (ℕ × C)ᵒᵖ ⥤ CommRingCat.{w} :=
  (prodOpEquiv (C := ℕ) (D := C)).functor ⋙
    Functor.uncurry.obj (B ⋙ sheafToPresheaf J CommRingCat.{w})

/-- Vertical covers glue in each ring sheaf B_n.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site).
Proof: restrict a covering to its vertical slice and glue in B_n. Separatedness
on the pulled-back covering verifies compatibility with the horizontal maps. -/
theorem systemSequenceRingPresheaf_isSheaf :
    Presheaf.IsSheaf (coefficientSequenceTopology J) (systemSequenceRingPresheaf B) := by
  intro A
  apply sequence_sheaf_of_slices
  intro n
  dsimp only [systemSequenceRingPresheaf]
  rw [← Functor.assoc, sequence_uncurry_slice]
  exact (B.obj (op n)).property A

/-- The sheaf of rings whose restriction to level n is B_n.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def systemSequenceRing : Sheaf (coefficientSequenceTopology J) CommRingCat.{w} :=
  ⟨systemSequenceRingPresheaf B, systemSequenceRingPresheaf_isSheaf B⟩

/-- Forgetting commutativity preserves sheaves on the essentially small sequence site.
Source: Stacks 03CZ (blueprint: lem-pur-system-ringed-sequence-site).
Proof: transport the limit-preserving forgetful functor from a small model of the site
in the coefficient universe. -/
instance systemSequenceCommRingCompose :
    (coefficientSequenceTopology J).HasSheafCompose
      (forget₂ CommRingCat.{w} RingCat.{w}) :=
  (equivSmallModel.{w} (ℕ × C)).hasSheafCompose (coefficientSequenceTopology J)
    ((equivSmallModel.{w} (ℕ × C)).inverse.inducedTopology (coefficientSequenceTopology J))
    (forget₂ CommRingCat.{w} RingCat.{w})

/-- Module sheaves on the actual ringed sequence site.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
abbrev systemSequenceModules := ringedSiteModules.{w}
  (derivedChangeRingIndependentCoefficients.{w}
    (coefficientSequenceTopology J) (systemSequenceRing B))

/-- Forgetting scalar structures turns a strict system into a sequence of abelian presheaves.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def systemAbelianPresheafSequence (M : StrictRingSystem B) :
    ℕᵒᵖ ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj n := (M.level n.unop).val.presheaf
  map {n m} h :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        ((M.transition (leOfHom h.unop)).val.app U).hom.toAddMonoidHom
      naturality := by
        intro U V f
        ext x
        exact PresheafOfModules.naturality_apply (M.transition (leOfHom h.unop)).val f x }
  map_id n := by
    ext U x
    exact M.identity n.unop U x
  map_comp {n m l} f g := by
    ext U x
    exact M.compose (leOfHom g.unop) (leOfHom f.unop) U x

/-- The abelian presheaf underlying the associated sheaf on the sequence site.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def systemSequenceAbelianPresheaf (M : StrictRingSystem B) :
    (ℕ × C)ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (prodOpEquiv (C := ℕ) (D := C)).functor ⋙
    Functor.uncurry.obj (systemAbelianPresheafSequence B M)

/-- The associated module presheaf, using the strict transition and vertical restriction.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def systemSequenceModulePresheaf (M : StrictRingSystem B) :
    PresheafOfModules.{w} (derivedChangeRingIndependentCoefficients.{w}
      (coefficientSequenceTopology J) (systemSequenceRing B)).obj where
  obj X := (M.level X.unop.1).val.obj (op X.unop.2)
  map {X Y} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars
      ((derivedChangeRingIndependentCoefficients.{w} (coefficientSequenceTopology J)
        (systemSequenceRing B)).obj.map f).hom).obj
          ((M.level Y.unop.1).val.obj (op Y.unop.2)))
    { toFun := (systemSequenceAbelianPresheaf B M).map f
      map_add' := by intros; exact map_add _ _ _
      map_smul' := by
        intro c x
        let : Module ((B.obj (op Y.unop.1)).obj.obj (op Y.unop.2))
            ((ModuleCat.restrictScalars
              ((derivedChangeRingIndependentCoefficients J (B.obj (op Y.unop.1))).obj.map
                f.unop.2.op).hom).obj
              ((M.level Y.unop.1).val.obj (op Y.unop.2))) :=
          inferInstanceAs (Module ((B.obj (op Y.unop.1)).obj.obj (op Y.unop.2))
            ((M.level Y.unop.1).val.obj (op Y.unop.2)))
        change (M.level Y.unop.1).val.map f.unop.2.op
          ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) (c • x)) = _
        rw [map_smul]
        change (M.level Y.unop.1).val.map f.unop.2.op
          ((B.map f.unop.1.op).hom.app (op X.unop.2) c •
            (show (M.level Y.unop.1).val.obj (op X.unop.2) from
              (M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) x)) =
          (B.obj (op Y.unop.1)).obj.map f.unop.2.op
            ((B.map f.unop.1.op).hom.app (op X.unop.2) c) •
              ((M.level Y.unop.1).val.map f.unop.2.op
                ((M.transition (leOfHom f.unop.1)).val.app (op X.unop.2) x))
        erw [PresheafOfModules.map_smul]
        rfl }
  map_id X := by
    ext x
    exact CategoryTheory.congr_fun ((systemSequenceAbelianPresheaf B M).map_id X) x
  map_comp {X Y Z} f g := by
    ext x
    exact CategoryTheory.congr_fun ((systemSequenceAbelianPresheaf B M).map_comp f g) x

private theorem systemSequenceModulePresheaf_underlying (M : StrictRingSystem B) :
    (systemSequenceModulePresheaf B M).presheaf = systemSequenceAbelianPresheaf B M := by
  apply CategoryTheory.Functor.ext
    (F := (systemSequenceModulePresheaf B M).presheaf)
    (G := systemSequenceAbelianPresheaf B M) (fun _ ↦ rfl) ?_
  intro X Y f
  ext x
  rfl

/-- The associated module presheaf satisfies descent.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site).
Proof: its underlying abelian presheaf is the uncurrying of the component presheaves;
each vertical slice is a sheaf, so the vertical-slice criterion applies. -/
theorem systemSequenceModulePresheaf_isSheaf (M : StrictRingSystem B) :
    Presheaf.IsSheaf (coefficientSequenceTopology J)
      (systemSequenceModulePresheaf B M).presheaf := by
  rw [systemSequenceModulePresheaf_underlying]
  intro A
  apply sequence_sheaf_of_slices
  intro n
  dsimp only [systemSequenceAbelianPresheaf]
  rw [← Functor.assoc, sequence_uncurry_slice]
  exact (M.level n).isSheaf A

/-- Associate a sheaf of modules on the sequence site to a strict semilinear system.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def strictSystemToSequence (M : StrictRingSystem B) : systemSequenceModules B :=
  ⟨systemSequenceModulePresheaf B M, systemSequenceModulePresheaf_isSheaf B M⟩

/-- The passage to sequence-site sheaves is functorial, with unchanged component maps.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def strictSystemToSequenceFunctor : StrictRingSystem B ⥤ systemSequenceModules B where
  obj := strictSystemToSequence B
  map {M N} f := ⟨{
    app := fun X ↦ (f.app X.unop.1).val.app (op X.unop.2)
    naturality := by
      intro X Y g
      ext x
      change (f.app Y.unop.1).val.app (op Y.unop.2)
          ((M.level Y.unop.1).val.map g.unop.2.op
            ((M.transition (leOfHom g.unop.1)).val.app (op X.unop.2) x)) =
        (N.level Y.unop.1).val.map g.unop.2.op
          ((N.transition (leOfHom g.unop.1)).val.app (op X.unop.2)
            ((f.app X.unop.1).val.app (op X.unop.2) x))
      rw [PresheafOfModules.naturality_apply (f.app Y.unop.1).val]
      exact congrArg ((N.level Y.unop.1).val.map g.unop.2.op)
        (congrArg (fun t ↦ t.val.app (op X.unop.2) x)
          (f.comm (leOfHom g.unop.1))).symm }⟩

/-- The vertical inclusion is continuous for the sequence topology.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site).
Proof: covering is defined on a vertical slice. For cover preservation, the pullback
of a pushed-forward sieve contains the original sieve. The cover-lifting compatibility
condition follows by factoring any two arrows through their vertical components. -/
instance systemSequenceEvaluationContinuous (n : ℕ) :
    (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J) := by
  apply Functor.isContinuous_of_coverPreserving
  · constructor
    intro G Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ he
    have he' : f₁.2 ≫ g₁ = f₂.2 ≫ g₂ := congrArg Prod.snd he
    have hx' := hx f₁.2 f₂.2 hg₁ hg₂ he'
    let q : X ⟶ (n, X.2) := Prod.mkHom f₁.1 (𝟙 _)
    have e₁ : q ≫ (Prod.sectR n C).map f₁.2 = f₁ := by
      ext <;> simp [q]
    have e₂ : q ≫ (Prod.sectR n C).map f₂.2 = f₂ := by
      apply Prod.hom_ext
      · exact Subsingleton.elim _ _
      · simp [q]
    rw [← e₁, ← e₂, op_comp, op_comp, G.obj.map_comp, G.obj.map_comp]
    exact congrArg (G.obj.map q.op) hx'
  · constructor
    intro U S hS
    change (S.functorPushforward (Prod.sectR n C)).functorPullback (Prod.sectR n C) ∈ J U
    exact J.superset_covering (Sieve.le_functorPushforward_pullback _ S) hS

/-- The structural coefficient map of a vertical slice is the identity on sections.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def systemSequenceVerticalRingMap (n : ℕ) :
    derivedChangeRingIndependentCoefficients J (B.obj (op n)) ⟶
      ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{w}
        J (coefficientSequenceTopology J)).obj
          (derivedChangeRingIndependentCoefficients.{w}
            (coefficientSequenceTopology J) (systemSequenceRing B)) where
  hom :=
    { app := fun U ↦ 𝟙 _
      naturality := by
        intro U V f
        ext x
        change (B.obj (op n)).obj.map f x =
          (B.obj (op n)).obj.map f (((B.map (𝟙 (op n))).hom.app U) x)
        rw [B.map_id]
        rfl }

/-- Actual restriction of a module sheaf to a vertical slice.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def systemSequenceEvaluation (n : ℕ) : systemSequenceModules B ⥤ systemLevel B n :=
  SheafOfModules.pushforward (F := Prod.sectR n C) (systemSequenceVerticalRingMap B n)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Horizontal restriction of the sequence ring is the specified coefficient map.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site).
Proof: the vertical component is an identity, so functoriality removes it. -/
theorem systemSequenceRing_horizontal {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) :
    (derivedChangeRingIndependentCoefficients.{w}
      (coefficientSequenceTopology J) (systemSequenceRing B)).obj.map
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op =
      (forget₂ CommRingCat.{w} RingCat.{w}).map ((B.map (homOfLE h).op).hom.app U) := by
  change (forget₂ CommRingCat.{w} RingCat.{w}).map
    (((B.map (homOfLE h).op).hom.app U) ≫ (B.obj (op m)).obj.map (𝟙 U)) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A horizontal section map, viewed as a linear map after restriction of scalars.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def sequenceSystemTransitionApp (N : systemSequenceModules B) {m n : ℕ} (h : m ≤ n)
    (U : Cᵒᵖ) :
    ((systemSequenceEvaluation B n).obj N).val.obj U ⟶
      ((systemRestriction B h).obj ((systemSequenceEvaluation B m).obj N)).val.obj U :=
  ModuleCat.ofHom
    (Y := ((systemRestriction B h).obj ((systemSequenceEvaluation B m).obj N)).val.obj U)
    { toFun := N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
      map_add' := by intros; exact map_add _ _ _
      map_smul' := by
        intro c x
        have hh := N.val.map_smul (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op c x
        have hc := congrArg (fun g ↦ g c) (systemSequenceRing_horizontal B h U)
        rw [hc] at hh
        exact hh }

/-- The horizontal section maps of a sequence-site sheaf form its strict transitions.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def sequenceSystemTransition (N : systemSequenceModules B) {m n : ℕ} (h : m ≤ n) :
    (systemSequenceEvaluation B n).obj N ⟶
      (systemRestriction B h).obj ((systemSequenceEvaluation B m).obj N) where
  val :=
    { app := sequenceSystemTransitionApp B N h
      naturality := by
        intro U V f
        ext x
        change N.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op
            (N.val.map (Prod.mkHom (𝟙 n) f.unop).op x) =
          N.val.map (Prod.mkHom (𝟙 m) f.unop).op
            (N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)
        have he : (Prod.mkHom (𝟙 n) f.unop).op ≫
            (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op =
          (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op ≫
            (Prod.mkHom (𝟙 m) f.unop).op := by
          apply Quiver.Hom.unop_inj
          apply Prod.hom_ext
          · exact Subsingleton.elim _ _
          · simp
        exact (N.val.map_comp_apply (Prod.mkHom (𝟙 n) f.unop).op
          (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x).symm.trans
          ((N.val.congr_map_apply he x).trans
            (N.val.map_comp_apply (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
              (Prod.mkHom (𝟙 m) f.unop).op x)) }

/-- The vertical evaluations and horizontal maps of a sequence sheaf form a strict system.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def sequenceToStrictSystem (N : systemSequenceModules B) : StrictRingSystem B where
  level n := (systemSequenceEvaluation B n).obj N
  transition h := sequenceSystemTransition B N h
  identity n U x := by
    change N.val.map (Prod.mkHom (𝟙 n) (𝟙 U.unop)).op x = x
    have hi : (Prod.mkHom (𝟙 n) (𝟙 U.unop)).op = 𝟙 (op (n, U.unop)) := rfl
    rw [hi, N.val.map_id]
    rfl
  compose {l m n} h k U x := by
    change N.val.map (Prod.mkHom (homOfLE (h.trans k)) (𝟙 U.unop)).op x =
      N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
        (N.val.map (Prod.mkHom (homOfLE k) (𝟙 U.unop)).op x)
    have he : (Prod.mkHom (homOfLE (h.trans k)) (𝟙 U.unop)).op =
        (Prod.mkHom (homOfLE k) (𝟙 U.unop)).op ≫
          (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op := by
      apply Quiver.Hom.unop_inj
      apply Prod.hom_ext
      · exact Subsingleton.elim _ _
      · simp
    exact (N.val.congr_map_apply he x).trans
      (N.val.map_comp_apply (Prod.mkHom (homOfLE k) (𝟙 U.unop)).op
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)

/-- Restrict sequence-site sheaves and their maps to all vertical slices.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def sequenceToStrictSystemFunctor : systemSequenceModules B ⥤ StrictRingSystem B where
  obj := sequenceToStrictSystem B
  map {M N} f :=
    { app := fun n ↦ (systemSequenceEvaluation B n).map f
      comm := by
        intro m n h
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        ext x
        change N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
            (f.val.app (op (n, U.unop)) x) =
          f.val.app (op (m, U.unop))
            (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)
        exact (PresheafOfModules.naturality_apply f.val
          (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x).symm }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- On a vertical slice the round trip has the identity section isomorphism.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def strictSystemSequenceUnitLevel (M : StrictRingSystem B) (n : ℕ) :
    M.level n ≅ (sequenceToStrictSystem B (strictSystemToSequence B M)).level n :=
  (fullyFaithfulForget _).preimageIso (PresheafOfModules.isoMk
    (fun U ↦ Iso.refl _) (by
      intro U V f
      ext x
      change (M.level n).val.map f x =
        (M.level n).val.map f ((M.transition (Nat.le_refl n)).val.app U x)
      exact congrArg (fun y : (M.level n).val.obj U ↦ (M.level n).val.map f y)
        (M.identity n U x).symm))

/-- The round trip from strict systems is naturally the identity on every section.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def strictSystemSequenceUnit :
    𝟭 (StrictRingSystem B) ≅ strictSystemToSequenceFunctor B ⋙ sequenceToStrictSystemFunctor B :=
  NatIso.ofComponents (fun M ↦
    { hom :=
        { app := fun n ↦ (strictSystemSequenceUnitLevel B M n).hom
          comm := by
            intro m n h
            apply SheafOfModules.hom_ext
            apply PresheafOfModules.hom_ext
            intro U
            ext x
            change (M.level m).val.map (𝟙 U)
                ((M.transition h).val.app U x) = (M.transition h).val.app U x
            rw [PresheafOfModules.map_id]
            rfl }
      inv :=
        { app := fun n ↦ (strictSystemSequenceUnitLevel B M n).inv
          comm := by
            intro m n h
            apply SheafOfModules.hom_ext
            apply PresheafOfModules.hom_ext
            intro U
            ext x
            change (M.transition h).val.app U x =
              (M.level m).val.map (𝟙 U) ((M.transition h).val.app U x)
            rw [PresheafOfModules.map_id]
            rfl }
      hom_inv_id := by
        apply strictRingSystem_hom_ext B
        intro n
        exact (strictSystemSequenceUnitLevel B M n).hom_inv_id
      inv_hom_id := by
        apply strictRingSystem_hom_ext B
        intro n
        exact (strictSystemSequenceUnitLevel B M n).inv_hom_id })
    (by
      intro M N f
      apply strictRingSystem_hom_ext B
      intro n
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      ext x
      rfl)

/-- Reassembling the vertical slices preserves every section of a sequence sheaf.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site). -/
def strictSystemSequenceCounit :
    sequenceToStrictSystemFunctor B ⋙ strictSystemToSequenceFunctor B ≅
      𝟭 (systemSequenceModules B) :=
  NatIso.ofComponents (fun N ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun X ↦ Iso.refl _) (by
      intro X Y f
      ext x
      change N.val.map (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op
          (N.val.map (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op x) = N.val.map f x
      have he : (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op ≫
          (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op = f := by
        apply Quiver.Hom.unop_inj
        apply Prod.hom_ext
        · simp
        · simp
      exact (N.val.map_comp_apply
        (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op
        (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op x).symm.trans
          (N.val.congr_map_apply he x)))) (by
    intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    ext x
    rfl)

/-- Strict semilinear systems are exactly module sheaves on the ringed sequence site.
Source: Zheng 4.1 (blueprint: lem-pur-system-ringed-sequence-site).
Proof: restrict to vertical slices and recover transitions from horizontal arrows;
reassembly is the identity on sections, maps and scalar multiplication. -/
def strictSystemSequenceEquivalence : StrictRingSystem B ≌ systemSequenceModules B where
  functor := strictSystemToSequenceFunctor B
  inverse := sequenceToStrictSystemFunctor B
  unitIso := strictSystemSequenceUnit B
  counitIso := strictSystemSequenceCounit B
  functor_unitIso_comp M := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    ext x
    rfl

end SheafOfModules
