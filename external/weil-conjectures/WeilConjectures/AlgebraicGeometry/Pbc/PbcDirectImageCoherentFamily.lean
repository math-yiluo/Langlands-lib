/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcDescentInterfaces
import WeilConjectures.AlgebraicGeometry.Pbc.PbcDirectImageFamilyExact
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import all WeilConjectures.CategoryTheory.StageSystem.CommonStageCalculus

/-! # Normalized direct-image coefficient families
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u v u' v' u'' v''
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.StageSystem
section LocalizationCoherence
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {I : Type w} [Preorder I]
  {A : I → Type u} [∀ i, Category.{v} (A i)]
  {B : I → Type u'} [∀ i, Category.{v'} (B i)]
  {C : I → Type u''} [∀ i, Category.{v''} (C i)]
  {S₀ : StageSystem A} {S : StageSystem B} {T : StageSystem C}

private theorem coherence_of_heq
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (Φ₀ : A₀ ⥤ B₀) (Φ₁ : A₁ ⥤ B₁) (Φ₂ : A₂ ⥤ B₂)
    {U₀₁ U₀₁' : A₀ ⥤ A₁} {U₁₂ U₁₂' : A₁ ⥤ A₂} {U₀₂ U₀₂' : A₀ ⥤ A₂}
    {V₀₁ V₀₁' : B₀ ⥤ B₁} {V₁₂ V₁₂' : B₁ ⥤ B₂} {V₀₂ V₀₂' : B₀ ⥤ B₂}
    (eU₀₁ : U₀₁ = U₀₁') (eU₁₂ : U₁₂ = U₁₂') (eU₀₂ : U₀₂ = U₀₂')
    (eV₀₁ : V₀₁ = V₀₁') (eV₁₂ : V₁₂ = V₁₂') (eV₀₂ : V₀₂ = V₀₂')
    (β₀₁ : Φ₀ ⋙ V₀₁ ≅ U₀₁ ⋙ Φ₁) (β₁₂ : Φ₁ ⋙ V₁₂ ≅ U₁₂ ⋙ Φ₂)
    (β₀₂ : Φ₀ ⋙ V₀₂ ≅ U₀₂ ⋙ Φ₂)
    (β₀₁' : Φ₀ ⋙ V₀₁' ≅ U₀₁' ⋙ Φ₁) (β₁₂' : Φ₁ ⋙ V₁₂' ≅ U₁₂' ⋙ Φ₂)
    (β₀₂' : Φ₀ ⋙ V₀₂' ≅ U₀₂' ⋙ Φ₂)
    (αU : U₀₁ ⋙ U₁₂ ≅ U₀₂) (αU' : U₀₁' ⋙ U₁₂' ≅ U₀₂')
    (αV : V₀₁ ⋙ V₁₂ ≅ V₀₂) (αV' : V₀₁' ⋙ V₁₂' ≅ V₀₂')
    (h₀₁ : ∀ K, HEq (β₀₁.hom.app K) (β₀₁'.hom.app K))
    (h₁₂ : ∀ K, HEq (β₁₂.hom.app K) (β₁₂'.hom.app K))
    (h₀₂ : ∀ K, HEq (β₀₂.hom.app K) (β₀₂'.hom.app K))
    (hαU : ∀ K, HEq (αU.hom.app K) (αU'.hom.app K))
    (hαV : ∀ K, HEq (αV.hom.app K) (αV'.hom.app K))
    (hc : ∀ K, V₁₂'.map (β₀₁'.hom.app K) ≫ β₁₂'.hom.app (U₀₁'.obj K) ≫
      Φ₂.map (αU'.hom.app K) = αV'.hom.app (Φ₀.obj K) ≫ β₀₂'.hom.app K) :
    ∀ K, V₁₂.map (β₀₁.hom.app K) ≫ β₁₂.hom.app (U₀₁.obj K) ≫
      Φ₂.map (αU.hom.app K) = αV.hom.app (Φ₀.obj K) ≫ β₀₂.hom.app K := by
  subst U₀₁'
  subst U₁₂'
  subst U₀₂'
  subst V₀₁'
  subst V₁₂'
  subst V₀₂'
  intro K
  rw [eq_of_heq (h₀₁ K), eq_of_heq (h₁₂ _), eq_of_heq (h₀₂ K),
    eq_of_heq (hαU K), eq_of_heq (hαV _)]
  exact hc K

@[irreducible] private def conjugateIso {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (Φ : A ⥤ C) (Ψ : B ⥤ D) {U U' : A ⥤ B} {V V' : C ⥤ D}
    (eU : U = U') (eV : V = V') (b : Φ ⋙ V' ≅ U' ⋙ Ψ) :
    Φ ⋙ V ≅ U ⋙ Ψ :=
  Functor.isoWhiskerLeft Φ (eqToIso eV) ≪≫ b ≪≫
    Functor.isoWhiskerRight (eqToIso eU).symm Ψ

private theorem conjugateIso_heq {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (Φ : A ⥤ C) (Ψ : B ⥤ D) {U U' : A ⥤ B} {V V' : C ⥤ D}
    (eU : U = U') (eV : V = V') (b : Φ ⋙ V' ≅ U' ⋙ Ψ) (K : A) :
    HEq ((conjugateIso Φ Ψ eU eV b).hom.app K) (b.hom.app K) := by
  subst U'
  subst V'
  unfold conjugateIso
  apply heq_of_eq
  simp

private theorem conjugateIso_exists {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (Φ : A ⥤ C) (Ψ : B ⥤ D) {U U' : A ⥤ B} {V V' : C ⥤ D}
    (eU : U = U') (eV : V = V') (b : Φ ⋙ V' ≅ U' ⋙ Ψ) :
    ∃ c : Φ ⋙ V ≅ U ⋙ Ψ, ∀ K, HEq (c.hom.app K) (b.hom.app K) :=
  ⟨conjugateIso Φ Ψ eU eV b, conjugateIso_heq Φ Ψ eU eV b⟩

private theorem fullMap_heq
    {A B : Type*} [Category A] [Category B] (P : ObjectProperty A)
    (Q : P.FullSubcategory ⥤ B) {K L K' L' : P.FullSubcategory}
    (hK : K.obj = K'.obj) (hL : L.obj = L'.obj)
    (f : K.obj ⟶ L.obj) (g : K'.obj ⟶ L'.obj) (h : HEq f g) :
    HEq (Q.map (ObjectProperty.homMk f)) (Q.map (ObjectProperty.homMk g)) := by
  have eK : K = K' := by cases K; cases K'; cases hK; rfl
  have eL : L = L' := by cases L; cases L'; cases hL; rfl
  subst K'
  subst L'
  cases eq_of_heq h
  rfl

private def conjugateFamily (R : Morphism S₀ T) (φ : ∀ i, A i ⥤ C i)
    (d : ∀ i, φ i ≅ R.Φ i) : Morphism S₀ T where
  Φ := φ
  β {i j} h := Functor.isoWhiskerRight (d i) (T.T h) ≪≫ R.β h ≪≫
    Functor.isoWhiskerLeft (S₀.T h) (d j).symm
  coh {i j k} h k' X := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    have hn := (d k).inv.naturality ((S₀.assoc h k').hom.app X)
    dsimp only [Functor.comp_obj] at hn
    rw [← hn]
    erw [(T.T k').map_id, Category.id_comp]
    rw [reassoc_of% (R.coh h k' X)]
    rw [← (T.assoc h k').hom.naturality_assoc ((d i).hom.app X)]
    rfl

private theorem reflectFamilyCoherence
    (Q : Morphism S₀ S) (φ : ∀ i, B i ⥤ C i)
    (b : ∀ {i j} (h : i ≤ j), φ i ⋙ T.T h ≅ S.T h ⋙ φ j)
    (r : ∀ {i j} (h : i ≤ j),
      (Q.Φ i ⋙ φ i) ⋙ T.T h ≅ S₀.T h ⋙ (Q.Φ j ⋙ φ j))
    (hr : ∀ {i j k} (h : i ≤ j) (h' : j ≤ k) (X : A i),
      (T.T h').map ((r h).hom.app X) ≫
          (r h').hom.app ((S₀.T h).obj X) ≫
            (Q.Φ k ⋙ φ k).map ((S₀.assoc h h').hom.app X) =
        (T.assoc h h').hom.app ((Q.Φ i ⋙ φ i).obj X) ≫
          (r (h.trans h')).hom.app X)
    (hb : ∀ {i j} (h : i ≤ j) (X : A i),
      (b h).hom.app ((Q.Φ i).obj X) ≫ (φ j).map ((Q.β h).hom.app X) =
        (r h).hom.app X)
    (hsurj : ∀ i (Y : B i), ∃ X, (Q.Φ i).obj X = Y)
    {i j k} (h : i ≤ j) (h' : j ≤ k) (Y : B i) :
    (T.T h').map ((b h).hom.app Y) ≫
        (b h').hom.app ((S.T h).obj Y) ≫ (φ k).map ((S.assoc h h').hom.app Y) =
      (T.assoc h h').hom.app ((φ i).obj Y) ≫ (b (h.trans h')).hom.app Y := by
  obtain ⟨X, rfl⟩ := hsurj i Y
  apply (cancel_mono ((φ k).map ((Q.β (h.trans h')).hom.app X))).1
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp, ← Q.coh h h' X]
  simp only [CategoryTheory.Functor.map_comp]
  have hn := (b h').hom.naturality ((Q.β h).hom.app X)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn]
  rw [← CategoryTheory.Functor.map_comp_assoc, hb h X,
    reassoc_of% (hb h' ((S₀.T h).obj X)), hb (h.trans h') X]
  exact hr h h' X

@[irreducible] private def localizeBeta
    (Q : Morphism S₀ S) (W : ∀ i, MorphismProperty (A i))
    [∀ i, (Q.Φ i).IsLocalization (W i)]
    (R : Morphism S₀ T) (φ : ∀ i, B i ⥤ C i)
    (d : ∀ i, Q.Φ i ⋙ φ i ≅ R.Φ i)
    {i j} (h : i ≤ j) : φ i ⋙ T.T h ≅ S.T h ⋙ φ j := by
  let R' := conjugateFamily R (fun i ↦ Q.Φ i ⋙ φ i) d
  let e {i j} (h : i ≤ j) :
      Q.Φ i ⋙ (φ i ⋙ T.T h) ≅ Q.Φ i ⋙ (S.T h ⋙ φ j) :=
    (Functor.associator _ _ _).symm ≪≫ R'.β h ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Q.β h).symm (φ j) ≪≫ Functor.associator _ _ _
  let b {i j} (h : i ≤ j) : φ i ⋙ T.T h ≅ S.T h ⋙ φ j :=
    (Localization.fullyFaithfulWhiskeringLeft (Q.Φ i) (W i) _).preimageIso (e h)
  exact b h

private theorem localizeBeta_spec
    (Q : Morphism S₀ S) (W : ∀ i, MorphismProperty (A i))
    [∀ i, (Q.Φ i).IsLocalization (W i)]
    (R : Morphism S₀ T) (φ : ∀ i, B i ⥤ C i)
    (d : ∀ i, Q.Φ i ⋙ φ i ≅ R.Φ i)
    {i j} (h : i ≤ j) (X : A i) :
    (localizeBeta Q W R φ d h).hom.app ((Q.Φ i).obj X) ≫
        (φ j).map ((Q.β h).hom.app X) =
      ((conjugateFamily R (fun i ↦ Q.Φ i ⋙ φ i) d).β h).hom.app X := by
  unfold localizeBeta
  let R' := conjugateFamily R (fun i ↦ Q.Φ i ⋙ φ i) d
  let e {i j} (h : i ≤ j) :
      Q.Φ i ⋙ (φ i ⋙ T.T h) ≅ Q.Φ i ⋙ (S.T h ⋙ φ j) :=
    (Functor.associator _ _ _).symm ≪≫ R'.β h ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Q.β h).symm (φ j) ≪≫ Functor.associator _ _ _
  let b {i j} (h : i ≤ j) : φ i ⋙ T.T h ≅ S.T h ⋙ φ j :=
    (Localization.fullyFaithfulWhiskeringLeft (Q.Φ i) (W i) _).preimageIso (e h)
  change (b h).hom.app ((Q.Φ i).obj X) ≫
    (φ j).map ((Q.β h).hom.app X) = (R'.β h).hom.app X
  have he := congr_app
    ((Localization.fullyFaithfulWhiskeringLeft (Q.Φ i) (W i) _).map_preimage
      (e h).hom) X
  change (b h).hom.app ((Q.Φ i).obj X) = (e h).hom.app X at he
  rw [he]
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Category.comp_id, Category.assoc,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  erw [Category.comp_id, Category.comp_id]

private theorem localizeBeta_normalized
    {D : I → Type*} [∀ i, Category (D i)] {U : StageSystem D}
    (Q : Morphism S₀ S) (W : ∀ i, MorphismProperty (A i))
    [∀ i, (Q.Φ i).IsLocalization (W i)]
    (R : Morphism S₀ U) (Q' : Morphism U T) (φ : ∀ i, B i ⥤ C i)
    (d : ∀ i, Q.Φ i ⋙ φ i ≅ R.Φ i ⋙ Q'.Φ i)
    {i j} (h : i ≤ j) (X : A i) :
    (Q'.β h).inv.app ((R.Φ i).obj X) ≫
      (T.T h).map ((d i).inv.app X) ≫
      (localizeBeta Q W (R.comp Q') φ d h).hom.app ((Q.Φ i).obj X) ≫
      (φ j).map ((Q.β h).hom.app X) ≫ (d j).hom.app ((S₀.T h).obj X) =
        (Q'.Φ j).map ((R.β h).hom.app X) := by
  rw [reassoc_of% (localizeBeta_spec Q W (R.comp Q') φ d h X)]
  dsimp only [conjugateFamily, Morphism.comp, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id, Category.assoc,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(T.T h).map_id, Category.id_comp, Category.comp_id, Iso.inv_hom_id_app_assoc]

private theorem strip_identities {D C : Type*} [Category D] [Category C]
    (V : C ⥤ D) {X : C} {L N P : D}
    (f : L ⟶ V.obj X) (g : V.obj X ⟶ N) (k : N ⟶ P) (z : L ⟶ P)
    (h : f ≫ V.map (𝟙 X) ≫ g ≫ k ≫ 𝟙 P = z) : f ≫ g ≫ k = z := by
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.assoc] using h

private theorem refl_conjugate {D₀ D₁ C₀ C₁ : Type*}
    [Category D₀] [Category D₁] [Category C₀] [Category C₁]
    {F : D₀ ⥤ C₀} {G : D₁ ⥤ C₁} {U : D₀ ⥤ D₁} {V : C₀ ⥤ C₁}
    (b : F ⋙ V ≅ U ⋙ G) (eF : F = F) (eG : G = G) :
    Functor.isoWhiskerRight (eqToIso eF).symm V ≪≫ b ≪≫
      Functor.isoWhiskerLeft U (eqToIso eG) = b := by
  have hF : eqToIso eF = Iso.refl F := rfl
  have hG : eqToIso eG = Iso.refl G := rfl
  rw [hF, hG]
  simp

private abbrev localizeFamily
    (Q : Morphism S₀ S) (W : ∀ i, MorphismProperty (A i))
    [∀ i, (Q.Φ i).IsLocalization (W i)]
    (R : Morphism S₀ T) (φ : ∀ i, B i ⥤ C i)
    (d : ∀ i, Q.Φ i ⋙ φ i ≅ R.Φ i)
    (hsurj : ∀ i (Y : B i), ∃ X, (Q.Φ i).obj X = Y) : Morphism S T := by
  let R' := conjugateFamily R (fun i ↦ Q.Φ i ⋙ φ i) d
  refine { Φ := φ, β := localizeBeta Q W R φ d, coh := ?_ }
  intro i j k h h' Y
  exact reflectFamilyCoherence Q φ (localizeBeta Q W R φ d) R'.β R'.coh
    (fun {_ _} h X ↦ localizeBeta_spec Q W R φ d h X) hsurj h h' Y

end LocalizationCoherence
end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

section OperationAssembly
attribute [local irreducible] pbcScalarCoefficientMap completedAdicDerivedChange
  pbcDerivedScalarAdjunction CategoryTheory.Functor.rightDerivedFunctor
  completedModuleDirectImage
variable {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ (n : WithBot ℕ∞))]
  [iS : Fact (∀ t : S, IsUnit (l : S.presheaf.stalk t))]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ambientTensor_eq (T : Scheme.{u}) [IsNoetherian T]
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcAmbientScalarExtension l Ω T h =
      pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) T := by
  unfold pbcAmbientScalarExtension pbcEmbeddingAmbientTensor
  rw [pbcStageCoefficientMap_eq l Ω T h]

omit [IsAlgClosure ℚ_[l] Ω] in
private theorem finiteInclusion_comp {E F G : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (k : F ≤ G) :
    (pbcFiniteFieldInclusion.{u} l Ω k).comp (pbcFiniteFieldInclusion l Ω h) =
      pbcFiniteFieldInclusion l Ω (h.trans k) := by
  ext x
  change (Shrink.algEquiv (Padic l) G.val).symm
      (IntermediateField.inclusion k
        ((Shrink.algEquiv (Padic l) F.val)
          ((Shrink.algEquiv (Padic l) F.val).symm
            (IntermediateField.inclusion h ((Shrink.algEquiv (Padic l) E.val) x))))) =
    (Shrink.algEquiv (Padic l) G.val).symm
      (IntermediateField.inclusion (h.trans k) ((Shrink.algEquiv (Padic l) E.val) x))
  rw [AlgEquiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reductionNormalization_heq {V : Scheme.{u}}
    {R₁ R₂ R₃ : Sheaf (ProEt.topology V) CommRingCat.{u + 1}}
    {φ φ' : R₁ ⟶ R₂} {ψ ψ' : R₂ ⟶ R₃} {χ χ' : R₁ ⟶ R₃}
    (h : φ ≫ ψ = χ) (h' : φ' ≫ ψ' = χ')
    (eφ : φ = φ') (eψ : ψ = ψ') (eχ : χ = χ')
    (K : DerivedCategory (pbcModules V R₁)) :
    HEq ((Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction φ)
      (pbcDerivedScalarAdjunction ψ) (pbcDerivedScalarAdjunction χ)
      (pbcDerivedRestrictComp φ ψ χ h)).hom.app K)
      ((pbcReductionNormalization φ' ψ' χ' h' K).hom) := by
  subst φ'
  subst ψ'
  subst χ'
  apply heq_of_eq
  dsimp [pbcReductionNormalization, pbcReductionNormalizationHom, pbcReductionTransition]
  simp only [Adjunction.leftAdjointCompIso_hom_app,
    Adjunction.homEquiv_counit, CategoryTheory.Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ambientAssociator_raw (T : Scheme.{u}) [IsNoetherian T]
    {E F G : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) (k : F ≤ G)
    (K : pbcAmbientStage l Ω T E) :
    HEq ((pbcAmbientScalarAssociator l Ω T h k).hom.app K)
      ((pbcAmbientScalarComp l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h)
        (pbcFiniteFieldInclusion l Ω k) T).hom.app K) := by
  unfold pbcAmbientScalarAssociator pbcAmbientScalarComp
  simp only [NatIso.ofComponents_hom_app]
  apply reductionNormalization_heq
  · exact pbcStageCoefficientMap_eq l Ω T h
  · exact pbcStageCoefficientMap_eq l Ω T k
  · exact (pbcStageCoefficientMap_eq l Ω T (h.trans k)).trans
      (congrArg (fun j ↦ pbcScalarCoefficientMap l
        (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω G) j T)
        (finiteInclusion_comp l Ω h k).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ambientPushComparison_exists {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S]
    (f : T ⟶ S) {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    ∃ c : pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω S h ≅
      pbcAmbientScalarExtension l Ω T h ⋙
        pbcActualDerivedPush f (pbcStageDatum.{u} l Ω F), ∀ K, HEq (c.hom.app K)
      ((pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f).hom.app K) :=
  StageSystem.conjugateIso_exists
    (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E))
    (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω F))
    (ambientTensor_eq l Ω T h) (ambientTensor_eq l Ω S h)
    (pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
      (pbcFiniteFieldInclusion l Ω h) f)

private def ambientPushComparison {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S]
    (f : T ⟶ S) {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E) ⋙
        pbcAmbientScalarExtension l Ω S h ≅
      pbcAmbientScalarExtension l Ω T h ⋙
        pbcActualDerivedPush f (pbcStageDatum.{u} l Ω F) :=
  (ambientPushComparison_exists l Ω f h).choose

private theorem ambientPushComparison_heq {V W : Scheme.{u}}
    [IsNoetherian V] [IsNoetherian W] (f : V ⟶ W)
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (K : pbcAmbientStage l Ω V E) :
    HEq ((ambientPushComparison l Ω f h).hom.app K)
      ((pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f).hom.app K) :=
  (ambientPushComparison_exists l Ω f h).choose_spec K

private abbrev ambientStageSystem (T : Scheme.{u}) [IsNoetherian T] :
    StageSystem (fun E : Padic.FiniteCoefficientFields l Ω ↦ pbcAmbientStage l Ω T E) where
  T h := pbcAmbientScalarExtension l Ω T h
  assoc h k := pbcAmbientScalarAssociator l Ω T h k
  cocycle h k j K := pbcAmbientScalarAssociator_cocycle l Ω T h k j K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ambientTensor_comp_eq (V : Scheme.{u}) [IsNoetherian V]
    {E F G : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) (k : F ≤ G) :
    pbcAmbientScalarExtension l Ω V (h.trans k) =
      pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω G)
        ((pbcFiniteFieldInclusion l Ω k).comp (pbcFiniteFieldInclusion l Ω h)) V :=
  (ambientTensor_eq l Ω V (h.trans k)).trans
    (congrArg (fun j ↦ pbcEmbeddingAmbientTensor l
      (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω G) j V)
      (finiteInclusion_comp l Ω h k).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev ambientPushFamily {V W : Scheme.{u}} [IsNoetherian V] [IsNoetherian W]
    (f : V ⟶ W) :
    StageSystem.Morphism (ambientStageSystem l Ω V) (ambientStageSystem l Ω W) where
  Φ E := pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)
  β h := ambientPushComparison l Ω f h
  coh {E F G} h k K := by
    have hb (M : pbcAmbientStage l Ω V E) :
        HEq ((ambientPushComparison l Ω f (h.trans k)).hom.app M)
          ((pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω G)
            ((pbcFiniteFieldInclusion l Ω k).comp (pbcFiniteFieldInclusion l Ω h))
            f).hom.app M) := by
      rw [finiteInclusion_comp l Ω h k]
      exact ambientPushComparison_heq l Ω f (h.trans k) M
    exact StageSystem.coherence_of_heq
      (A₀ := pbcAmbientStage l Ω V E) (A₁ := pbcAmbientStage l Ω V F)
      (A₂ := pbcAmbientStage l Ω V G) (B₀ := pbcAmbientStage l Ω W E)
      (B₁ := pbcAmbientStage l Ω W F) (B₂ := pbcAmbientStage l Ω W G)
      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E))
      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω F))
      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω G))
      (ambientTensor_eq l Ω V h) (ambientTensor_eq l Ω V k)
      (ambientTensor_comp_eq l Ω V h k)
      (ambientTensor_eq l Ω W h) (ambientTensor_eq l Ω W k)
      (ambientTensor_comp_eq l Ω W h k)
      (ambientPushComparison l Ω f h) (ambientPushComparison l Ω f k)
      (ambientPushComparison l Ω f (h.trans k))
      (pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f)
      (pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω F)
        (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω k) f)
      (pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω G)
        ((pbcFiniteFieldInclusion l Ω k).comp (pbcFiniteFieldInclusion l Ω h)) f)
      (pbcAmbientScalarAssociator l Ω V h k)
      (pbcAmbientScalarComp l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h)
        (pbcFiniteFieldInclusion l Ω k) V)
      (pbcAmbientScalarAssociator l Ω W h k)
      (pbcAmbientScalarComp l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteField.{u} l Ω G) (pbcFiniteFieldInclusion l Ω h)
        (pbcFiniteFieldInclusion l Ω k) W)
      (ambientPushComparison_heq l Ω f h) (ambientPushComparison_heq l Ω f k) hb
      (ambientAssociator_raw l Ω V h k) (ambientAssociator_raw l Ω W h k)
      (fun M ↦ pbcScalarDirectImage_coefficients l
        (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) f (pbcFiniteField.{u} l Ω G)
        (pbcFiniteFieldInclusion l Ω k) M) K

private abbrev integralStageSystem (T : Scheme.{u}) [IsNoetherian T]
    (hdim : ∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))
    (hinv : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) :
    StageSystem (fun E : Padic.FiniteCoefficientFields l Ω ↦ pbcIntegralStage l Ω T E) where
  T h := pbcIntegralScalarExtension l Ω T hdim hinv h
  assoc h k := pbcIntegralScalarAssociator l Ω T hdim hinv h k
  cocycle h k j K := pbcIntegralScalarAssociator_cocycle l Ω T hdim hinv h k j K

private abbrev stageLocalizationFamily (T : Scheme.{u}) [IsNoetherian T]
    (hdim : ∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))
    (hinv : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) :
    StageSystem.Morphism (integralStageSystem l Ω T hdim hinv)
      (pbcScalarSystem l Ω T hdim hinv) where
  Φ E := pbcStageLocalization l Ω T E
  β h := pbcScalarIntegralComparison l Ω T hdim hinv h
  coh h k K := (pbcScalarAssociator_normalization l Ω T hdim hinv h k K).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev restrictAmbientFamily
    (A : StageSystem.Morphism (ambientStageSystem l Ω T) (ambientStageSystem l Ω S))
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω T E),
      PbcIsBoundedConstructibleComplete S (pbcStageDatum.{u} l Ω E)
        ((A.Φ E).obj K.obj)) :
    StageSystem.Morphism (integralStageSystem l Ω T dT.out iT.out)
      (integralStageSystem l Ω S dS.out iS.out) where
  Φ E := pbcConditionalIntegral (pbcStageDatum.{u} l Ω E) (A.Φ E) (pres E)
  β h := NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ ((A.β h).app K.obj)) (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact (A.β h).hom.naturality f.hom)
  coh h k K := by
    apply ObjectProperty.hom_ext
    change (pbcAmbientScalarExtension l Ω S k).map ((A.β h).hom.app K.obj) ≫
        (A.β k).hom.app ((pbcAmbientScalarExtension l Ω T h).obj K.obj) ≫
          (A.Φ _).map (((pbcIntegralScalarAssociator l Ω T dT.out iT.out h k).hom.app
            K).hom) =
      ((pbcIntegralScalarAssociator l Ω S dS.out iS.out h k).hom.app
        ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω _) (A.Φ _) (pres _)).obj K)).hom ≫
          (A.β (h.trans k)).hom.app K.obj
    dsimp only [pbcConditionalIntegral, ObjectProperty.lift, Functor.comp_obj,
      ObjectProperty.ι_obj]
    rw [pbcIntegralScalarAssociator_hom, pbcIntegralScalarAssociator_hom]
    simpa only [ambientStageSystem, pbcConditionalIntegral, ObjectProperty.lift,
      Functor.comp_obj, ObjectProperty.ι_obj] using A.coh h k K.obj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private abbrev rationalizeIntegralFamily
    (A : StageSystem.Morphism (integralStageSystem l Ω T dT.out iT.out)
      (integralStageSystem l Ω S dS.out iS.out))
    [∀ E, (A.Φ E).Additive]
    [∀ E, (A.Φ E).Linear (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))] :
    StageSystem.Morphism (pbcScalarSystem l Ω T dT.out iT.out)
      (pbcScalarSystem l Ω S dS.out iS.out) := by
  let Q := stageLocalizationFamily l Ω T dT.out iT.out
  let Q' := stageLocalizationFamily l Ω S dS.out iS.out
  let W (E : Padic.FiniteCoefficientFields l Ω) :=
    pbcStageDenominators l Ω T dT.out iT.out E
  have (E : Padic.FiniteCoefficientFields l Ω) : (Q.Φ E).IsLocalization (W E) :=
    pbcStageLocalization_isLocalization l Ω T dT.out iT.out E
  let φ (E : Padic.FiniteCoefficientFields l Ω) :=
    ScalarLocalization.transport (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
      (pbcStageUniformizer.{u} l Ω E) (A.Φ E)
  exact StageSystem.localizeFamily Q W (A.comp Q') φ (fun E ↦ Iso.refl _)
    (fun E K ↦ ⟨K.obj, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rationalizeIntegralFamily_beta
    (A : StageSystem.Morphism (integralStageSystem l Ω T dT.out iT.out)
      (integralStageSystem l Ω S dS.out iS.out))
    [∀ E, (A.Φ E).Additive]
    [∀ E, (A.Φ E).Linear (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))]
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (K : pbcIntegralStage l Ω T E) :
    (pbcScalarIntegralComparison l Ω S dS.out iS.out h).inv.app ((A.Φ E).obj K) ≫
      ((rationalizeIntegralFamily l Ω A).β h).hom.app (ScalarLocalization.mk K) ≫
        (ScalarLocalization.transport (PbcIntegralRing l (pbcFiniteField.{u} l Ω F))
          (pbcStageUniformizer.{u} l Ω F) (A.Φ F)).map
          ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom.app K) =
      (pbcStageLocalization l Ω S F).map ((A.β h).hom.app K) := by
  let Q := stageLocalizationFamily l Ω T dT.out iT.out
  let Q' := stageLocalizationFamily l Ω S dS.out iS.out
  let W (E : Padic.FiniteCoefficientFields l Ω) :=
    pbcStageDenominators l Ω T dT.out iT.out E
  have (E : Padic.FiniteCoefficientFields l Ω) : (Q.Φ E).IsLocalization (W E) :=
    pbcStageLocalization_isLocalization l Ω T dT.out iT.out E
  let φ (E : Padic.FiniteCoefficientFields l Ω) :=
    ScalarLocalization.transport (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
      (pbcStageUniformizer.{u} l Ω E) (A.Φ E)
  have hc := StageSystem.localizeBeta_normalized Q W A Q' φ (fun E ↦ Iso.refl _) h K
  exact StageSystem.strip_identities ((pbcScalarSystem l Ω S dS.out iS.out).T h)
    ((pbcScalarIntegralComparison l Ω S dS.out iS.out h).inv.app ((A.Φ E).obj K))
    _ _ _ hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private def rationalPushFamily (f : T ⟶ S)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω T E),
      PbcIsBoundedConstructibleComplete S (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj)) :
    StageSystem.Morphism (pbcScalarSystem l Ω T dT.out iT.out)
      (pbcScalarSystem l Ω S dS.out iS.out) := by
  let A := restrictAmbientFamily l Ω (ambientPushFamily l Ω f) pres
  have : ∀ E, (A.Φ E).Additive := fun E ↦
    inferInstanceAs ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (pres E)).Additive)
  have : ∀ E, (A.Φ E).Linear (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) := fun E ↦
    inferInstanceAs ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (pres E)).Linear
        (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)))
  exact rationalizeIntegralFamily l Ω A

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rationalPushFamily_phi (f : T ⟶ S)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω T E),
      PbcIsBoundedConstructibleComplete S (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    (rationalPushFamily l Ω f pres).Φ E = pbcDescentDirectImage l Ω f pres E := by
  unfold rationalPushFamily
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rationalPushFamily_betaSpec (f : T ⟶ S)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω T E),
      PbcIsBoundedConstructibleComplete S (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj)) :
    PbcDirectImageBetaSpec l Ω f pres (rationalPushFamily l Ω f pres) := by
  unfold rationalPushFamily
  intro E F h eE eF K
  let A := restrictAmbientFamily l Ω (ambientPushFamily l Ω f) pres
  have : ∀ E, (A.Φ E).Additive := fun E ↦
    inferInstanceAs ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (pres E)).Additive)
  have : ∀ E, (A.Φ E).Linear (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) := fun E ↦
    inferInstanceAs ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (pres E)).Linear
        (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)))
  have hi := StageSystem.refl_conjugate ((rationalizeIntegralFamily l Ω A).β h) eE eF
  have hc := congrArg (fun b ↦
    (pbcScalarIntegralComparison l Ω S dS.out iS.out h).inv.app
      ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
        (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (pres E)).obj K) ≫
      b.hom.app (ScalarLocalization.mk K) ≫
      (pbcDescentDirectImage l Ω f pres F).map
        ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom.app K)) hi
  have hb := rationalizeIntegralFamily_beta l Ω A h K
  have hr := (pbcScalarDirectImage_rational l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) f
    dT.out dS.out iT.out iS.out (pres E) (pres F)).exists.choose_spec
      (ScalarLocalization.mk K)
  apply (heq_of_eq hc).trans
  apply (heq_of_eq hb).trans
  apply HEq.trans ?_ hr.symm
  refine StageSystem.fullMap_heq _ _ ?_ ?_ _ _
    (ambientPushComparison_heq l Ω f h K.obj)
  · exact congrArg (fun Z ↦ Z.obj
      ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
      (ambientTensor_eq l Ω S h)
  · exact congrArg (fun Z ↦
      (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω F)).obj (Z.obj K.obj))
      (ambientTensor_eq l Ω T h)

end OperationAssembly

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]

/-- The actual rationalized direct-image operations form a coherent exact family,
with the prescribed normalized scalar comparisons at every pair of stages. -/
theorem pbcDirectImageCoherentFamily (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj)) :
    ∃ F : StageSystem.CoherentExactMorphism
      (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out),
      (∀ E : Padic.FiniteCoefficientFields l Ω,
        F.base.Φ E = pbcDescentDirectImage l Ω f pres E) ∧
      PbcDirectImageBetaSpec l Ω f pres F.base := by
  let R := rationalPushFamily l Ω f pres
  have hR : ∀ E : Padic.FiniteCoefficientFields l Ω,
      R.Φ E = pbcDescentDirectImage l Ω f pres E :=
    rationalPushFamily_phi l Ω f pres
  have bR : PbcDirectImageBetaSpec l Ω f pres R :=
    rationalPushFamily_betaSpec l Ω f pres
  obtain ⟨C, hC⟩ := pbcDirectImageFamilyExact l Ω f pres R hR bR
  refine ⟨C, ?_, ?_⟩
  · simpa only [hC] using hR
  · rw [hC]
    exact bR

end AlgebraicGeometry.Scheme
