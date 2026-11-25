/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.ConstantKoszulQuotientAugmentationIsIso

/-! # Comparison of strict Koszul and quotient completion

Source: Stacks Project, proetale.tex, Tag 099M (lemma-naive-completion).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard completed strictLimit
  quotientPresentation

set_option synthInstance.maxSize 2048

private theorem tensorUnit_natural (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {X Y : Cx O} (f : X ⟶ Y) (m : ℕᵒᵖ) :
    f ≫ ringedKoszulTensorUnitComponent O r s Y m =
      ringedKoszulTensorUnitComponent O r s X m ≫
        ((ringedKoszulTensorTower O r s).map f).app m := by
  let : IsGrothendieckAbelian.{u} (Mod O) := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  have hu : f ≫ (ringedKoszulRightUnitIso O Y).inv =
      (ringedKoszulRightUnitIso O X).inv ≫
        ((ringedKoszulTensor O).map f).app (ringedSiteRingComplex O) := by
    exact MonoidalCategory.rightUnitor_inv_naturality f
  change f ≫ (ringedKoszulRightUnitIso O Y).inv ≫
      ((ringedKoszulTensor O).obj Y).map (ringedKoszulDualUnit O r s m.unop) =
    ((ringedKoszulRightUnitIso O X).inv ≫
      ((ringedKoszulTensor O).obj X).map (ringedKoszulDualUnit O r s m.unop)) ≫
        ((ringedKoszulTensor O).map f).app _
  rw [← Category.assoc, hu, Category.assoc,
    ← ((ringedKoszulTensor O).map f).naturality, Category.assoc]

private theorem koszulLimitUnit_natural (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {X Y : Cx O} (f : X ⟶ Y) :
    f ≫ ringedKoszulLimitUnit O r s Y =
      ringedKoszulLimitUnit O r s X ≫
        (ordinaryLimit O).map ((ringedKoszulTensorTowerFunctor O r s).map f) := by
  apply HomologicalComplex.hom_ext
  intro q
  change f.f q ≫ ringedKoszulLimitUnitF O r s Y q =
    ringedKoszulLimitUnitF O r s X q ≫
      limMap (((ringedKoszulTensorTowerFunctor O r s).map f).f q)
  apply limit.hom_ext
  intro m
  simp only [Category.assoc]
  erw [limMap_π]
  simp only [← Category.assoc]
  dsimp only [ringedKoszulLimitUnitF]
  erw [limit.lift_π, Category.assoc, limit.lift_π]
  dsimp only [ringedKoszulTensorUnitCone]
  exact congrArg (fun g ↦ g.f q) (tensorUnit_natural J O r s f m)

private theorem koszulUnitOnComplex_natural (b : Bool) (r : ℕ) (a : Fin r → A)
    (K : KoszulPresentation J A I b r a)
    {X Y : Cx (coefficients J A I b)} (f : X ⟶ Y) :
    (Q (coefficients J A I b)).map f ≫ K.unitOnComplex Y =
      K.unitOnComplex X ≫ K.completion.map ((Q (coefficients J A I b)).map f) := by
  let O := coefficients J A I b
  let G := ringedKoszulTensorTowerFunctor O r
    (fun i ↦ algebraSection (baseMap J A I b) (a i))
  have hunit := koszulLimitUnit_natural J O r
    (fun i ↦ algebraSection (baseMap J A I b) (a i)) f
  have hγ := K.comparison.naturality (G.map f)
  have hκ := K.tensorFactors.inv.naturality f
  change (Q O).map ((ordinaryLimit O).map (G.map f)) ≫ K.comparison.app (G.obj Y) =
    K.comparison.app (G.obj X) ≫ K.inverseLimit.map ((TQ O).map (G.map f)) at hγ
  change (TQ O).map (G.map f) ≫ K.tensorFactors.inv.app Y =
    K.tensorFactors.inv.app X ≫ K.tensorTower.map ((Q O).map f) at hκ
  dsimp only [RingedKoszulLimitPresentation.unitOnComplex,
    RingedKoszulLimitPresentation.completion, Functor.comp_map]
  rw [← (Q O).map_comp_assoc, hunit, (Q O).map_comp_assoc]
  change (Q O).map (ringedKoszulLimitUnit O r _ X) ≫
      (Q O).map ((ordinaryLimit O).map (G.map f)) ≫ K.comparison.app (G.obj Y) ≫
        K.inverseLimit.map (K.tensorFactors.inv.app Y) = _
  erw [reassoc_of% hγ, ← K.inverseLimit.map_comp, hκ, K.inverseLimit.map_comp]
  simp only [Category.assoc]
  rfl

/-- Assemble a comparison from computations on a resolving class. Keeping the
coefficient category abstract avoids unfolding sheaf and chosen-localization data
throughout this categorical calculation. -/
private theorem compareComputations
    {M : Type*} [Category M] [Abelian M] [HasDerivedCategory M]
    {B E : Type*} [Category B] [Category E]
    (G T : CochainComplex M ℤ ⥤ B) (qT : B ⥤ E)
    (U : B ⥤ CochainComplex M ℤ)
    (KT LT : DerivedCategory M ⥤ E) (KL RL : E ⥤ DerivedCategory M)
    (κ₀ : DerivedCategory.Q ⋙ KT ≅ G ⋙ qT) (ρ : KL ≅ RL)
    (δ : U ⋙ DerivedCategory.Q ⟶ qT ⋙ KL)
    (γ : U ⋙ DerivedCategory.Q ⟶ qT ⋙ RL)
    (hρ : ∀ Z, δ.app Z ≫ ρ.hom.app (qT.obj Z) = γ.app Z)
    (β₀ : DerivedCategory.Q ⋙ LT ⟶ T ⋙ qT)
    (η : 𝟭 (DerivedCategory M) ⟶ LT ⋙ RL)
    (ν : ∀ X : CochainComplex M ℤ,
      DerivedCategory.Q.obj X ⟶ (KT ⋙ KL).obj (DerivedCategory.Q.obj X))
    (u : ∀ X : CochainComplex M ℤ, X ⟶ U.obj (G.obj X))
    (v : ∀ X : CochainComplex M ℤ, X ⟶ U.obj (T.obj X))
    (hν : ∀ X, ν X = DerivedCategory.Q.map (u X) ≫ δ.app (G.obj X) ≫
      KL.map (κ₀.inv.app X))
    (hnat : ∀ {X Y : CochainComplex M ℤ} (f : X ⟶ Y),
      DerivedCategory.Q.map f ≫ ν Y = ν X ≫ (KT ⋙ KL).map (DerivedCategory.Q.map f))
    (α : G ⟶ T) (hunit : ∀ X, u X ≫ U.map (α.app X) = v X)
    (S : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (P : CochainComplex M ℤ) (f : P ⟶ X), S P ∧ QuasiIso f)
    (hβ₀ : ∀ X, S X → IsIso (β₀.app X))
    (hα : ∀ X, S X → IsIso (RL.map (qT.map (α.app X))))
    (hη : ∀ X, S X → η.app (DerivedCategory.Q.obj X) ≫ RL.map (β₀.app X) =
      DerivedCategory.Q.map (v X) ≫ γ.app (T.obj X)) :
    ∃ e : KT ⋙ KL ≅ LT ⋙ RL,
      ∀ X : CochainComplex M ℤ, ν X ≫ e.hom.app (DerivedCategory.Q.obj X) =
        η.app (DerivedCategory.Q.obj X) := by
  let κ : DerivedCategory.Q ⋙ KT ⋙ KL ≅ G ⋙ qT ⋙ RL :=
    (Functor.associator DerivedCategory.Q KT KL).symm ≪≫
      Functor.isoWhiskerRight κ₀ KL ≪≫ Functor.associator G qT KL ≪≫
        Functor.isoWhiskerLeft G (Functor.isoWhiskerLeft qT ρ)
  let c : DerivedCategory.Q ⋙ KT ⋙ KL ⟶ T ⋙ qT ⋙ RL :=
    κ.hom ≫ Functor.whiskerRight (Functor.whiskerRight α qT) RL
  let β : DerivedCategory.Q ⋙ LT ⋙ RL ⟶ T ⋙ qT ⋙ RL :=
    Functor.whiskerRight β₀ RL
  have hc (X : CochainComplex M ℤ) (hX : S X) : IsIso (c.app X) := by
    have := hα X hX
    change IsIso (κ.hom.app X ≫ RL.map (qT.map (α.app X)))
    infer_instance
  have hβ (X : CochainComplex M ℤ) (hX : S X) : IsIso (β.app X) := by
    have := hβ₀ X hX
    exact inferInstanceAs (IsIso (RL.map (β₀.app X)))
  obtain ⟨e, he⟩ := resolving_comparison_iso (KT ⋙ KL) (LT ⋙ RL)
    (T ⋙ qT ⋙ RL) S hres c β hc hβ
  have hmodel (X : CochainComplex M ℤ) (hX : S X) :
      ν X ≫ e.hom.app (DerivedCategory.Q.obj X) = η.app (DerivedCategory.Q.obj X) := by
    have := hβ X hX
    apply (cancel_mono (β.app X)).1
    rw [Category.assoc, he X hX]
    change ν X ≫ c.app X = η.app (DerivedCategory.Q.obj X) ≫ RL.map (β₀.app X)
    rw [hη X hX]
    have hκ : ν X ≫ κ.hom.app X =
        DerivedCategory.Q.map (u X) ≫ γ.app (G.obj X) := by
      rw [hν]
      dsimp only [κ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.associator_inv_app, Functor.associator_hom_app,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app]
      simp only [Category.id_comp, Category.assoc]
      rw [← KL.map_comp_assoc, κ₀.inv_hom_id_app]
      erw [KL.map_id, Category.id_comp, hρ]
    change ν X ≫ (κ.hom.app X ≫ RL.map (qT.map (α.app X))) = _
    rw [← Category.assoc, hκ, Category.assoc]
    have hn := γ.naturality (α.app X)
    change DerivedCategory.Q.map (U.map (α.app X)) ≫ γ.app (T.obj X) =
      γ.app (G.obj X) ≫ RL.map (qT.map (α.app X)) at hn
    rw [← hn, ← DerivedCategory.Q.map_comp_assoc, hunit X]
  refine ⟨e, ?_⟩
  intro X
  obtain ⟨P, f, hP, hf⟩ := hres X
  have : QuasiIso f := hf
  apply (cancel_epi (DerivedCategory.Q.map f)).1
  rw [← Category.assoc, hnat, Category.assoc, e.hom.naturality,
    ← Category.assoc, hmodel P hP]
  exact (η.naturality (DerivedCategory.Q.map f)).symm

/-- For any presentation of the specified strict Koszul tower, its derived limit agrees
with quotient completion, carrying the degree-zero unit to the quotient augmentation.

Source: Stacks Project, proetale.tex, Tag 099M (lemma-naive-completion), with the
flat completed-coefficient extension of sites-modules.tex, Tag 093M.
(auxiliary; not a blueprint node).

Proof: use the exterior basis to identify the dual of the positive tensor Koszul complex
with the negative Koszul complex on the same ordered generators. The diagonal power
transition is multiplication by a_i on the negative-degree factor and identity in degree
zero. The degree-zero augmentation therefore commutes strictly with the transitions and
with the coaugmentation from the ring. The Noetherian Koszul augmentation theorem says
that its cone tower is pro-zero, including the empty generating list. Apply exact constant
module realization, followed by extension to the chosen coefficient sheaf. This extension
is flat: it is the identity for constant coefficients, and is flat by Tag 093M for completed
coefficients. Its quotient is the specified finite coefficient sheaf. Tensor with a
flat-term K-flat representative P. The flat-constant tensor pro-zero theorem and the total
right derived strict-limit theorem invert the resulting augmented tower map. The quotient
presentation comparison computes the quotient tower on P; the Koszul presentation
factorization computes its strict tensor tower. Uniqueness of the total derived limit
identifies the two limit functors, independently of the supplied Koszul presentation.
The construction commutes with maps between K-flat representatives. Resolving-class
localization therefore descends these comparisons to a natural isomorphism on the derived
category. The strict coaugmentation square and the defining normalization of the quotient
presentation give the displayed equality of units on K-flat models, and essential
surjectivity of their localization gives it on every derived object. -/
theorem koszulQuotientComparison [IsNoetherianRing A] (b : Bool) (r : ℕ)
    (a : Fin r → A) (ha : Ideal.span (Set.range a) = I)
    (K : KoszulPresentation J A I b r a) :
    ∃ e : koszulCompletion J A I K ≅ completion J A I b,
      ∀ M : D (coefficients J A I b), koszulUnit J A I K M ≫ e.hom.app M =
        (completionUnit J A I b).app M  := by
  let O := coefficients J A I b
  let G := ringedKoszulTensorTowerFunctor O r
    (fun i ↦ algebraSection (baseMap J A I b) (a i))
  let T := (reductionTower J A I b).mapHomologicalComplex (.up ℤ)
  let L := rlim O
  let γ := limitComparison O
  let WT := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod O) (.up ℤ)
  let R := quotientPresentation J A I b
  have hL : L.IsRightDerivedFunctor γ WT := (strictLimit O).universal
  have hK : K.inverseLimit.IsRightDerivedFunctor K.comparison WT := K.isRightDerived
  let ρ : K.inverseLimit ≅ L :=
    Functor.rightDerivedUnique K.inverseLimit L K.comparison γ WT
  have hρ (Z : CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ) :
      K.comparison.app Z ≫ ρ.hom.app ((TQ O).obj Z) = γ.app Z := by
    change K.comparison.app Z ≫
      (Functor.rightDerivedNatTrans K.inverseLimit L K.comparison γ WT
        (𝟙 (ordinaryLimit O ⋙ Q O))).app ((TQ O).obj Z) = γ.app Z
    exact (Functor.rightDerivedNatTrans_app K.inverseLimit L K.comparison γ WT
      (𝟙 (ordinaryLimit O ⋙ Q O)) Z).trans (Category.id_comp _)
  obtain ⟨α, hα⟩ := koszulQuotientAugmentation J A I b r a ha
  let S (P : Cx O) := P.IsKFlatTensor ∧
    ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)
  obtain ⟨e, he⟩ := compareComputations G T (TQ O) (ordinaryLimit O)
    K.tensorTower R.tower K.inverseLimit L K.tensorFactors ρ K.comparison γ hρ
    R.comparison R.unit (fun P ↦ K.unitOnComplex P)
    (fun P ↦ ringedKoszulLimitUnit O r
      (fun i ↦ algebraSection (baseMap J A I b) (a i)) P)
    (ordinaryUnit J A I b) (fun _ ↦ rfl)
    (fun {_ _} f ↦ koszulUnitOnComplex_natural J A I b r a K f)
    α hα.1 S (module_flat_kFlat_resolution (J := J))
    (fun P hP ↦ R.laws.2.1 P hP.1 hP.2)
    (fun P hP ↦ koszulQuotientAugmentation_isIso J A I b r a ha α hα P hP.1 hP.2)
    (fun P hP ↦ R.laws.2.2 P hP.1 hP.2)
  refine ⟨e, ?_⟩
  intro M
  let j := (Q O).objObjPreimageIso M
  change (j.inv ≫ K.unitOnComplex ((Q O).objPreimage M) ≫
      K.completion.map j.hom) ≫ e.hom.app M = _
  erw [Category.assoc, Category.assoc, e.hom.naturality]
  erw [← Category.assoc (K.unitOnComplex _) _ _, he]
  change j.inv ≫ R.unit.app _ ≫ (R.tower ⋙ L).map j.hom = R.unit.app M
  have hn := R.unit.naturality j.hom
  change j.hom ≫ R.unit.app M =
    R.unit.app ((Q O).obj ((Q O).objPreimage M)) ≫ (R.tower ⋙ L).map j.hom at hn
  erw [← hn, ← Category.assoc, j.inv_hom_id, Category.id_comp]

end CategoryTheory.ConstantCompletion
