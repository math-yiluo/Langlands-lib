/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdRawLocalization.FdRawLocalizationScalarData
import WeilConjectures.FourierTransform.FdRawLocalization.FdRawNormalizedComparisonShift

/-! # Descent of the fixed integral scalar comparison

Source: trace-definition coefficient-category sentence, raw localization steps 1--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FdRawLocalization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)

attribute [local irreducible] HasDerivedCategory.standard
  FdOrdinaryScalarTransport.complex FdOrdinaryScalarTransport.completion
  fdCoefficientTransportFactors pbcIntegralDatum completedAdicChangeData
  integralDetailedCoefficientComparison sfRationalTriangulationDatum
  sfRationalScalarExtension
  pbcScalarCommShift pbcRationalHasShift
  ScalarLocalization.composition ScalarLocalization.category

attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift
  pbcFiniteField pbcFiniteFieldField pbcFiniteFieldAlgebra

private theorem map_heq_of_heq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X X' Y Y' : C} (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (hf : f ≍ f') : F.map f ≍ F.map f' := by
  subst hX hY
  cases hf
  rfl

private theorem app_heq_of_eq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ⟶ G) {X X' : C} (h : X = X') : α.app X ≍ α.app X' := by
  subst h
  rfl

/-- The abstract three-field cocycle descent. -/
private theorem abstract_cocycle
    {AE AL AM BE BL BM CE CL CM DE DL DM : Type*}
    [Category AE] [Category AL] [Category AM] [Category BE] [Category BL] [Category BM]
    [Category CE] [Category CL] [Category CM] [Category DE] [Category DL] [Category DM]
    (QE : AE ⥤ BE) (QL : AL ⥤ BL) (QM : AM ⥤ BM)
    (Sh : BE ⥤ BL) (Sk : BL ⥤ BM) (Shk : BE ⥤ BM)
    (Vh : AE ⥤ AL) (Vk : AL ⥤ AM) (Vhk : AE ⥤ AM)
    (JE : BE ⥤ DE) (JL : BL ⥤ DL) (JM : BM ⥤ DM)
    (IE : AE ⥤ CE) (IL : AL ⥤ CL) (IM : AM ⥤ CM)
    (PE : CE ⥤ DE) (PL : CL ⥤ DL) (PM : CM ⥤ DM)
    (Ch : CE ⥤ CL) (Ck : CL ⥤ CM) (Chk : CE ⥤ CM)
    (Th : DE ⥤ DL) (Tk : DL ⥤ DM) (Thk : DE ⥤ DM)
    (hSh : QE ⋙ Sh = Vh ⋙ QL) (hSk : QL ⋙ Sk = Vk ⋙ QM) (hShk : QE ⋙ Shk = Vhk ⋙ QM)
    (hJE : QE ⋙ JE = IE ⋙ PE) (hJL : QL ⋙ JL = IL ⋙ PL) (hJM : QM ⋙ JM = IM ⋙ PM)
    (bh : IE ⋙ Ch ≅ Vh ⋙ IL) (bk : IL ⋙ Ck ≅ Vk ⋙ IM) (bhk : IE ⋙ Chk ≅ Vhk ⋙ IM)
    (ch : PE ⋙ Th ≅ Ch ⋙ PL) (ck : PL ⋙ Tk ≅ Ck ⋙ PM) (chk : PE ⋙ Thk ≅ Chk ⋙ PM)
    (jh : Sh ⋙ JL ≅ JE ⋙ Th) (jk : Sk ⋙ JM ≅ JL ⋙ Tk) (jhk : Shk ⋙ JM ≅ JE ⋙ Thk)
    (hjh : ∀ K K', K' ≍ QE.obj K →
      jh.hom.app K' ≍ PL.map (bh.inv.app K) ≫ ch.inv.app (IE.obj K))
    (hjk : ∀ K K', K' ≍ QL.obj K →
      jk.hom.app K' ≍ PM.map (bk.inv.app K) ≫ ck.inv.app (IL.obj K))
    (hjhk : ∀ K K', K' ≍ QE.obj K →
      jhk.hom.app K' ≍ PM.map (bhk.inv.app K) ≫ chk.inv.app (IE.obj K))
    (β : Ch ⋙ Ck ≅ Chk) (α : Th ⋙ Tk ≅ Thk)
    (hα : ∀ X, α.hom.app (PE.obj X) = Tk.map (ch.hom.app X) ≫ ck.hom.app (Ch.obj X) ≫
      PM.map (β.hom.app X) ≫ chk.inv.app X)
    (γ : Vh ⋙ Vk ≅ Vhk) (a : Sh ⋙ Sk ≅ Shk)
    (ha : ∀ K, a.hom.app (QE.obj K) ≍ QM.map (γ.hom.app K))
    (hcocycle : ∀ K, bk.inv.app (Vh.obj K) ≫ Ck.map (bh.inv.app K) ≫ β.hom.app (IE.obj K) =
      IM.map (γ.hom.app K) ≫ bhk.inv.app K)
    (K : AE) :
    jk.hom.app (Sh.obj (QE.obj K)) ≫ Tk.map (jh.hom.app (QE.obj K)) ≫
        α.hom.app (JE.obj (QE.obj K)) =
      JM.map (a.hom.app (QE.obj K)) ≫ jhk.hom.app (QE.obj K) := by
  have e1 : Sh.obj (QE.obj K) = QL.obj (Vh.obj K) := Functor.congr_obj hSh K
  have e2 : Sk.obj (QL.obj (Vh.obj K)) = QM.obj (Vk.obj (Vh.obj K)) :=
    Functor.congr_obj hSk (Vh.obj K)
  have e3 : Shk.obj (QE.obj K) = QM.obj (Vhk.obj K) := Functor.congr_obj hShk K
  have e4 : JE.obj (QE.obj K) = PE.obj (IE.obj K) := Functor.congr_obj hJE K
  have e5 : JL.obj (QL.obj (Vh.obj K)) = PL.obj (IL.obj (Vh.obj K)) :=
    Functor.congr_obj hJL (Vh.obj K)
  have e6 : ∀ X, JM.obj (QM.obj X) = PM.obj (IM.obj X) := Functor.congr_obj hJM
  have h1 := hjk (Vh.obj K) _ (heq_of_eq e1)
  have o0 : JM.obj (Sk.obj (Sh.obj (QE.obj K))) = PM.obj (IM.obj (Vk.obj (Vh.obj K))) := by
    rw [e1, e2, e6]
  have o1 : Tk.obj (JL.obj (Sh.obj (QE.obj K))) = Tk.obj (PL.obj (IL.obj (Vh.obj K))) := by
    rw [e1, e5]
  have o2 : Tk.obj (Th.obj (JE.obj (QE.obj K))) = Tk.obj (Th.obj (PE.obj (IE.obj K))) := by
    rw [e4]
  have o3 : Thk.obj (JE.obj (QE.obj K)) = Thk.obj (PE.obj (IE.obj K)) := by rw [e4]
  have o4 : JM.obj (Shk.obj (QE.obj K)) = PM.obj (IM.obj (Vhk.obj K)) := by rw [e3, e6]
  have h2 := map_heq_of_heq Tk ((congrArg JL.obj e1).trans e5) (congrArg Th.obj e4)
    (hjh K _ HEq.rfl)
  have h3 := app_heq_of_eq α.hom e4
  have hl := heq_comp o0 o1 o3 h1 (heq_comp o1 o2 o3 h2 h3)
  have h4 := (map_heq_of_heq JM ((congrArg Sk.obj e1).trans e2) e3 (ha K)).trans
    (Functor.hcongr_hom hJM (γ.hom.app K))
  have h5 := hjhk K _ HEq.rfl
  have hr := heq_comp o0 o4 o3 h4 h5
  refine eq_of_heq (hl.trans (HEq.trans (heq_of_eq ?_) hr.symm))
  rw [hα]
  simp only [Functor.comp_obj, Functor.comp_map, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc Tk (ch.inv.app (IE.obj K)), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := ck.inv.naturality (bh.inv.app K)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn.symm]
  rw [Iso.inv_hom_id_app_assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Category.assoc, hcocycle, CategoryTheory.Functor.map_comp_assoc]

/-- The abstract unit descent. -/
private theorem abstract_unit
    {AE BE CE DE : Type*} [Category AE] [Category BE] [Category CE] [Category DE]
    (QE : AE ⥤ BE) (Sr : BE ⥤ BE) (Vr : AE ⥤ AE) (JE : BE ⥤ DE) (IE : AE ⥤ CE)
    (PE : CE ⥤ DE) (Cr : CE ⥤ CE) (Tr : DE ⥤ DE)
    (hS : QE ⋙ Sr = Vr ⋙ QE) (hJE : QE ⋙ JE = IE ⋙ PE) (hT : Tr = 𝟭 DE)
    (br : IE ⋙ Cr ≅ Vr ⋙ IE) (cr : PE ⋙ Tr ≅ Cr ⋙ PE) (jr : Sr ⋙ JE ≅ JE ⋙ Tr)
    (hjr : ∀ K K', K' ≍ QE.obj K →
      jr.hom.app K' ≍ PE.map (br.inv.app K) ≫ cr.inv.app (IE.obj K))
    (ε : Cr ≅ 𝟭 CE)
    (hc : cr ≍ (Functor.rightUnitor PE ≪≫ (Functor.leftUnitor PE).symm ≪≫
      Functor.isoWhiskerRight ε.symm PE))
    (u : Sr ≅ 𝟭 BE) (υ : Vr ≅ 𝟭 AE)
    (hu : ∀ K, u.hom.app (QE.obj K) ≍ QE.map (υ.hom.app K))
    (hunit : ∀ K, br.inv.app K ≫ ε.hom.app (IE.obj K) = IE.map (υ.hom.app K))
    (K : AE) :
    jr.hom.app (QE.obj K) ≍ JE.map (u.hom.app (QE.obj K)) := by
  subst hT
  cases hc
  refine (hjr K _ HEq.rfl).trans ?_
  have e1 : Sr.obj (QE.obj K) = QE.obj (Vr.obj K) := Functor.congr_obj hS K
  refine HEq.trans (heq_of_eq ?_) ((Functor.hcongr_hom hJE (υ.hom.app K)).symm.trans
    (map_heq_of_heq JE e1.symm rfl (hu K).symm))
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.comp_map, Category.comp_id]
  erw [Category.comp_id]
  rw [← CategoryTheory.Functor.map_comp, hunit]

/-- Components of heterogeneously equal isomorphisms, with explicit endpoint equalities. -/
private theorem map_app_heq_of_iso_heq {C D D' : Type*} [Category C] [Category D] [Category D']
    {F F' G G' : C ⥤ D} (hF : F = F') (hG : G = G') (a : F ≅ G) (a' : F' ≅ G')
    (h : a ≍ a') (Q : D ⥤ D') (X : C) : Q.map (a.hom.app X) ≍ Q.map (a'.hom.app X) := by
  subst hF hG
  cases h
  rfl

private theorem app_heq_of_iso_heq {C D : Type*} [Category C] [Category D]
    {F F' G G' : C ⥤ D} (hF : F = F') (hG : G = G') (a : F ≅ G) (a' : F' ≅ G')
    (h : a ≍ a') (X : C) : a.hom.app X ≍ a'.hom.app X := by
  subst hF hG
  cases h
  rfl

private theorem trans_eqToIso_heq {C D : Type*} [Category C] [Category D] {F G G' : C ⥤ D}
    (a : F ≅ G) (h : G = G') : (a ≪≫ eqToIso h) ≍ a := by
  subst h
  simp

private theorem eqToIso_trans_heq {C D : Type*} [Category C] [Category D] {F F' G : C ⥤ D}
    (h : F = F') (a : F' ≅ G) : (eqToIso h ≪≫ a) ≍ a := by
  subst h
  simp

section Generic

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (Y : Scheme.{u})

private theorem scalarAssociator_heq
    (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M) (k : E →ₐ[ℚ_[l]] M) (hk : j.comp ι = k) :
    GeneralAlgebraicallyClosedCoefficients.scalarAssociator l E L M ι j k hk Y ≍
      sfRationalScalarComp l E L ι Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j := by
  rw [GeneralAlgebraicallyClosedCoefficients.scalarAssociator]
  exact trans_eqToIso_heq _ _

private theorem scalarComp_app_heq (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M)
    (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarComp l E L ι Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app K ≍
      (sfRationalConstructibleLocalization l M Y).map
        ((sfIntegralScalarComp l E L ι Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
          M j).hom.app K.obj) :=
  (sfRationalScalarComp_existsUnique l E L ι Y 0 _ M j).exists.choose_spec _

private theorem scalarUnit_app_heq (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarUnit l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K ≍
      (sfRationalConstructibleLocalization l E Y).map
        ((sfIntegralScalarUnit l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K.obj) :=
  (sfRationalScalarUnit_existsUnique l E Y 0 _).exists.choose_spec _

end Generic

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem assoc_heq {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) :
    assoc l Ω T h k ≍ sfRationalScalarComp l _ _
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω E L h) T 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) _
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω L M k) :=
  (GeneralAlgebraicallyClosedCoefficients.associator_existsUnique l Ω T E L M h
    k).exists.choose_spec.trans (scalarAssociator_heq l _ _ _ T _ _ _ _)

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem integralAssoc_heq {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (k : L ≤ M) :
    integralAssoc l Ω T h k ≍ sfIntegralScalarComp l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω M)
        (pbcFiniteFieldInclusion l Ω k) := by
  unfold integralAssoc
  exact trans_eqToIso_heq _ _

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
/-- Congruence across two presentations of the same coefficient fields. The stage side uses
the `Coefficient` models and `coefficientInclusion`, the integral side the `pbcFiniteField`
models and `pbcFiniteFieldInclusion`; these agree definitionally, but asking the kernel to
compare them inside the components of the scalar comparisons times out. Here only the fields,
their instances and the inclusions are compared. -/
private theorem coefficient_congr_heq₃.{v}
    {β : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] (_ : FiniteDimensional ℚ_[l] E)
      (L : Type u) [Field L] [Algebra ℚ_[l] L] (_ : FiniteDimensional ℚ_[l] L)
      (M : Type u) [Field M] [Algebra ℚ_[l] M] (_ : FiniteDimensional ℚ_[l] M),
      (E →ₐ[ℚ_[l]] L) → (L →ₐ[ℚ_[l]] M) → sfIntegralConstructibleCategory l E T → Sort v}
    (F : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] (dE : FiniteDimensional ℚ_[l] E)
      (L : Type u) [Field L] [Algebra ℚ_[l] L] (dL : FiniteDimensional ℚ_[l] L)
      (M : Type u) [Field M] [Algebra ℚ_[l] M] (dM : FiniteDimensional ℚ_[l] M)
      (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M) (K : sfIntegralConstructibleCategory l E T),
      β E dE L dL M dM ι j K)
    {E₁ E₂ L₁ L₂ M₁ M₂ : Type u} (fE₁ : Field E₁) (fE₂ : Field E₂) (aE₁ : Algebra ℚ_[l] E₁)
    (aE₂ : Algebra ℚ_[l] E₂) (dE₁ : FiniteDimensional ℚ_[l] E₁)
    (dE₂ : FiniteDimensional ℚ_[l] E₂)
    (fL₁ : Field L₁) (fL₂ : Field L₂) (aL₁ : Algebra ℚ_[l] L₁)
    (aL₂ : Algebra ℚ_[l] L₂) (dL₁ : FiniteDimensional ℚ_[l] L₁)
    (dL₂ : FiniteDimensional ℚ_[l] L₂)
    (fM₁ : Field M₁) (fM₂ : Field M₂) (aM₁ : Algebra ℚ_[l] M₁)
    (aM₂ : Algebra ℚ_[l] M₂) (dM₁ : FiniteDimensional ℚ_[l] M₁)
    (dM₂ : FiniteDimensional ℚ_[l] M₂)
    (ι₁ : E₁ →ₐ[ℚ_[l]] L₁) (ι₂ : E₂ →ₐ[ℚ_[l]] L₂) (j₁ : L₁ →ₐ[ℚ_[l]] M₁)
    (j₂ : L₂ →ₐ[ℚ_[l]] M₂) (K₁ : sfIntegralConstructibleCategory l E₁ T)
    (K₂ : sfIntegralConstructibleCategory l E₂ T)
    (hE : E₁ = E₂) (hfE : fE₁ ≍ fE₂) (haE : aE₁ ≍ aE₂)
    (hL : L₁ = L₂) (hfL : fL₁ ≍ fL₂) (haL : aL₁ ≍ aL₂)
    (hM : M₁ = M₂) (hfM : fM₁ ≍ fM₂) (haM : aM₁ ≍ aM₂)
    (hι : ι₁ ≍ ι₂) (hj : j₁ ≍ j₂) (hK : K₁ ≍ K₂) :
    F E₁ dE₁ L₁ dL₁ M₁ dM₁ ι₁ j₁ K₁ ≍ F E₂ dE₂ L₂ dL₂ M₂ dM₂ ι₂ j₂ K₂ := by
  subst hE hL hM
  cases hfE
  cases haE
  cases hfL
  cases haL
  cases hfM
  cases haM
  cases hι
  cases hj
  cases hK
  rfl

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem assoc_app_heq₁ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (k : L ≤ M) (X : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :
    (assoc l Ω T h k).hom.app X ≍ (sfRationalScalarComp l _ _
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω E L h) T 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) _
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω L M k)).hom.app X :=
  app_heq_of_iso_heq rfl (congrArg (sfRationalScalarExtension l _ T 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) _)
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k)).symm _ _
    (assoc_heq l Ω T h k) X

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem integralAssoc_app_heq {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (k : L ≤ M) (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    (QS l Ω T M).map ((integralAssoc l Ω T h k).hom.app K) ≍
      (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω M) T).map
        ((sfIntegralScalarComp l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω M)
        (pbcFiniteFieldInclusion l Ω k)).hom.app K) :=
  map_app_heq_of_iso_heq rfl (congrArg (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω M) · T)
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k)).symm _ _
    (integralAssoc_heq l Ω T h k)
    (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω M) T) K

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem integralComp_bridge {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (k : L ≤ M) (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    (sfRationalConstructibleLocalization l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M)
      T).map ((sfIntegralScalarComp l _ _
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω E L h) T 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) _
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω L M k)).hom.app
          ((QS l Ω T E).obj K).obj) ≍
    (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω M) T).map
        ((sfIntegralScalarComp l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω M)
        (pbcFiniteFieldInclusion l Ω k)).hom.app K) :=
  coefficient_congr_heq₃ l T (fun E _ _ _ L _ _ _ M _ _ _ ι j K ↦
    (sfRationalConstructibleLocalization l M T).map ((sfIntegralScalarComp l E L ι T 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app K))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl
    rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
/-- The framework associator on a localized integral object is the localized `integralAssoc`. -/
private theorem assoc_app_heq {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (k : L ≤ M) (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    (assoc l Ω T h k).hom.app ((QS l Ω T E).obj K) ≍
      (QS l Ω T M).map ((integralAssoc l Ω T h k).hom.app K) :=
  (assoc_app_heq₁ l Ω T h k _).trans ((scalarComp_app_heq l _ _ _ T _ _ _).trans
    ((integralComp_bridge l Ω T h k K).trans (integralAssoc_app_heq l Ω T h k K).symm))

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem unit_heq (E : Padic.FiniteCoefficientFields l Ω) :
    unit l Ω T E ≍ sfRationalScalarUnit l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      T 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) := by
  rw [unit, GeneralAlgebraicallyClosedCoefficients.unitor]
  exact eqToIso_trans_heq _ _

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem unit_app_heq₁ (E : Padic.FiniteCoefficientFields l Ω)
    (X : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :
    (unit l Ω T E).hom.app X ≍ (sfRationalScalarUnit l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) T 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app X :=
  app_heq_of_iso_heq (congrArg (sfRationalScalarExtension l _ T 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) _)
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E)) rfl _ _
    (unit_heq l Ω T E) X

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem integralUnit_heq (E : Padic.FiniteCoefficientFields l Ω) :
    integralUnit l Ω T E ≍ sfIntegralScalarUnit l (pbcFiniteField.{u} l Ω E) T 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) := by
  unfold integralUnit
  exact eqToIso_trans_heq _ _

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem integralUnit_app_heq (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    (QS l Ω T E).map ((integralUnit l Ω T E).hom.app K) ≍
      (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).map
        ((sfIntegralScalarUnit l (pbcFiniteField.{u} l Ω E) T 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K) :=
  map_app_heq_of_iso_heq (congrArg (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω E) · T)
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E)) rfl _ _
    (integralUnit_heq l Ω T E)
    (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T) K

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem coefficient_congr_heq₁.{v}
    {β : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] (_ : FiniteDimensional ℚ_[l] E),
      sfIntegralConstructibleCategory l E T → Sort v}
    (F : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] (dE : FiniteDimensional ℚ_[l] E)
      (K : sfIntegralConstructibleCategory l E T), β E dE K)
    {E₁ E₂ : Type u} (fE₁ : Field E₁) (fE₂ : Field E₂) (aE₁ : Algebra ℚ_[l] E₁)
    (aE₂ : Algebra ℚ_[l] E₂) (dE₁ : FiniteDimensional ℚ_[l] E₁)
    (dE₂ : FiniteDimensional ℚ_[l] E₂)
    (K₁ : sfIntegralConstructibleCategory l E₁ T)
    (K₂ : sfIntegralConstructibleCategory l E₂ T)
    (hE : E₁ = E₂) (hfE : fE₁ ≍ fE₂) (haE : aE₁ ≍ aE₂) (hK : K₁ ≍ K₂) :
    F E₁ dE₁ K₁ ≍ F E₂ dE₂ K₂ := by
  subst hE
  cases hfE
  cases haE
  cases hK
  rfl

omit [IsAlgClosure ℚ_[l] Ω] [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem integralUnit_bridge (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    (sfRationalConstructibleLocalization l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      T).map ((sfIntegralScalarUnit l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
        T 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app ((QS l Ω T E).obj K).obj) ≍
    (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).map
        ((sfIntegralScalarUnit l (pbcFiniteField.{u} l Ω E) T 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K) :=
  coefficient_congr_heq₁ l T (fun E _ _ _ K ↦
    (sfRationalConstructibleLocalization l E T).map ((sfIntegralScalarUnit l E T 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K))
    _ _ _ _ _ _ _ _ rfl HEq.rfl HEq.rfl HEq.rfl

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
/-- The framework unit on a localized integral object is the localized `integralUnit`. -/
private theorem unit_app_heq (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    (unit l Ω T E).hom.app ((QS l Ω T E).obj K) ≍
      (QS l Ω T E).map ((integralUnit l Ω T E).hom.app K) :=
  (unit_app_heq₁ l Ω T E _).trans ((scalarUnit_app_heq l _ T _).trans
    ((integralUnit_bridge l Ω T E K).trans (integralUnit_app_heq l Ω T E K).symm))

section Generic

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (Y : Scheme.{u})

private theorem scalarComp_leftUnit (ι : E →ₐ[ℚ_[l]] E) (hι : ι = AlgHom.id ℚ_[l] E)
    (j : E →ₐ[ℚ_[l]] L) (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarComp l E E ι Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L j).hom.app K ≍
      (sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L j).map
        ((sfRationalScalarUnit l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K) := by
  subst hι
  exact heq_of_eq ((sfRationalScalar_coherence l E L j Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L (AlgHom.id ℚ_[l] L)).1 K)

private theorem scalarComp_rightUnit (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] L)
    (hj : j = AlgHom.id ℚ_[l] L)
    (F : sfRationalConstructibleCategory l E Y ⥤ sfRationalConstructibleCategory l L Y)
    (hF : F = sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι)
    (K : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarComp l E L ι Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L j).hom.app K ≍
      (sfRationalScalarUnit l L Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
        (F.obj K) := by
  subst hj hF
  exact heq_of_eq ((sfRationalScalar_coherence l E L ι Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L (AlgHom.id ℚ_[l] L)).2.1 K)

end Generic

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
/-- Left unit law for the framework associator. -/
private theorem assoc_leftUnit {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :
    (assoc l Ω T (le_refl E) h).hom.app K = (scalar l Ω T h).map ((unit l Ω T E).hom.app K) :=
  eq_of_heq ((assoc_app_heq₁ l Ω T (le_refl E) h K).trans
    ((scalarComp_leftUnit l _ _ T _
      ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E) _ K).trans
    (map_app_heq_of_iso_heq (congrArg (sfRationalScalarExtension l _ T 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) _)
      ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E)) rfl _ _
      (unit_heq l Ω T E) (scalar l Ω T h) K).symm))

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem assoc_rightUnit_comp {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :
    (assoc l Ω T h (le_refl L)).hom.app K ≍ (sfRationalScalarComp l _ _
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω E L h) T 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) _
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω L L (le_refl L))).hom.app K :=
  assoc_app_heq₁ l Ω T h (le_refl L) K

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem scalarComp_rightUnit_unit {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :
    (sfRationalScalarComp l _ _
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω E L h) T 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) _
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω L L (le_refl L))).hom.app K ≍
    (sfRationalScalarUnit l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) T 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app ((scalar l Ω T h).obj K) :=
  scalarComp_rightUnit l _ _ T _ _
      ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 L) (scalar l Ω T h) rfl K

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
private theorem assoc_rightUnit_heq {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :
    (assoc l Ω T h (le_refl L)).hom.app K ≍ (unit l Ω T L).hom.app ((scalar l Ω T h).obj K) :=
  (assoc_rightUnit_comp l Ω T h K).trans ((scalarComp_rightUnit_unit l Ω T h K).trans
    (unit_app_heq₁ l Ω T L _).symm)

omit [AlgebraicGeometry.IsNoetherian T] dT iT in
/-- Right unit law for the framework associator. -/
private theorem assoc_rightUnit {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :
    (assoc l Ω T h (le_refl L)).hom.app K = (unit l Ω T L).hom.app ((scalar l Ω T h).obj K) :=
  eq_of_heq (assoc_rightUnit_heq l Ω T h K)


/-- Integral cocycle and unit equations descend for a component-normalized comparison.
Source: raw localization scalar-descent steps 2 and 3
(blueprint: lem-fd-raw-normalized-comparison-coherence).

Proof: Every raw rational object is the image of its underlying integral object.
Evaluate the desired three-field identity on that object and substitute hcomponents
for each comparison. Naturality of pbcScalarIntegralComparison moves the localized
inverse b component through the PBC scalar functor. The defining normalization of
pbcScalarAssociator cancels its adjacent integral comparisons and identifies the
remaining associator with Q of pbcIntegralScalarAssociator. The framework associator
is sfRationalScalarComp followed by coefficient-inclusion equality transport; its
normalization identifies it with Q of integralAssoc. The stage tensor formula moves
this last map through J. What remains is Q applied to hcocycle, followed by the same
invertible scalar comparison on both sides; preservation of composition gives the
equality. At equal fields the PBC transition is literally the identity. Its integral
comparison is the localization of the actual integral unit, so hunit gives the
identity value after the framework unit normalization. Finally specialize the
three-field identity to an identity inclusion in the first and second position.
The balanced-tensor left and right unit equations for sfRationalScalarComp, including
the coefficient-inclusion equality transports, turn those two specializations into
the displayed unit equations. These normalizations retain the actual completeness
map. All arguments include repeated fields, zero objects, and the empty scheme. -/
theorem rawNormalizedComparisonCoherence
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (hcocycle : ∀ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      (b k).inv.app ((U l Ω T h).obj K) ≫
        (C l Ω T k).map ((b h).inv.app K) ≫
        (pbcIntegralScalarAssociator l Ω T dT.out iT.out h k).hom.app
          ((I l Ω T stage E).obj K) =
      (I l Ω T stage M).map ((integralAssoc l Ω T h k).hom.app K) ≫
        (b (h.trans k)).inv.app K)
    (hunit : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      (b (le_refl E)).inv.app K ≫
        (pbcIntegralScalarUnit l Ω T dT.out iT.out E).hom.app ((I l Ω T stage E).obj K) =
      (I l Ω T stage E).map ((integralUnit l Ω T E).hom.app K))
    (family : RationalFamily l Ω T stage)
    (j : RawComparison l Ω T stage family)
    (hcomponents : (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
        (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
        HEq ((j h).hom.app K')
          ((pbcStageLocalization l Ω T L).map ((b h).inv.app K) ≫
            (pbcScalarIntegralComparison l Ω T dT.out iT.out h).inv.app
              ((I l Ω T stage E).obj K)))) :
    (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq ((j (le_refl E)).hom.app K)
          ((J l Ω T stage family E).map
            ((unit l Ω T E).hom.app K))) ∧
      (∀ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (j k).hom.app ((scalar l Ω T h).obj K) ≫
          ((P l Ω T).T k).map ((j h).hom.app K) ≫
          ((P l Ω T).assoc h k).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family M).map ((assoc l Ω T h k).hom.app K) ≫
          (j (h.trans k)).hom.app K) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (j h).hom.app ((scalar l Ω T (le_refl E)).obj K) ≫
          ((P l Ω T).T h).map ((j (le_refl E)).hom.app K) ≫
          ((P l Ω T).assoc (le_refl E) h).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family L).map ((scalar l Ω T h).map
          ((unit l Ω T E).hom.app K)) ≫
          (j h).hom.app K) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (j (le_refl L)).hom.app ((scalar l Ω T h).obj K) ≫
          ((P l Ω T).T (le_refl L)).map ((j h).hom.app K) ≫
          ((P l Ω T).assoc h (le_refl L)).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family L).map
          ((unit l Ω T L).hom.app
            ((scalar l Ω T h).obj K)) ≫ (j h).hom.app K) := by
  have hess : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
      ∃ K₀ : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T,
        K = (QS l Ω T E).obj K₀ :=
    fun E K ↦ ⟨(K.obj : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T), rfl⟩
  have hcoc : ∀ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
      (j k).hom.app ((scalar l Ω T h).obj K) ≫
          ((P l Ω T).T k).map ((j h).hom.app K) ≫
          ((P l Ω T).assoc h k).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family M).map ((assoc l Ω T h k).hom.app K) ≫
          (j (h.trans k)).hom.app K := by
    intro E L M h k K
    obtain ⟨K₀, rfl⟩ := hess E K
    exact abstract_cocycle (QS l Ω T E) (QS l Ω T L) (QS l Ω T M) (scalar l Ω T h)
      (scalar l Ω T k) (scalar l Ω T (h.trans k)) (U l Ω T h) (U l Ω T k) (U l Ω T (h.trans k))
      (J l Ω T stage family E) (J l Ω T stage family L) (J l Ω T stage family M)
      (I l Ω T stage E) (I l Ω T stage L) (I l Ω T stage M) (pbcStageLocalization l Ω T E)
      (pbcStageLocalization l Ω T L) (pbcStageLocalization l Ω T M) (C l Ω T h) (C l Ω T k)
      (C l Ω T (h.trans k)) ((P l Ω T).T h) ((P l Ω T).T k) ((P l Ω T).T (h.trans k))
      (scalarFactors' l Ω T h) (scalarFactors' l Ω T k) (scalarFactors' l Ω T (h.trans k))
      (stageFactorsJ l Ω T stage family E) (stageFactorsJ l Ω T stage family L)
      (stageFactorsJ l Ω T stage family M) (b h) (b k) (b (h.trans k))
      (pbcScalarIntegralComparison l Ω T dT.out iT.out h)
      (pbcScalarIntegralComparison l Ω T dT.out iT.out k)
      (pbcScalarIntegralComparison l Ω T dT.out iT.out (h.trans k)) (j h) (j k) (j (h.trans k))
      (fun K K' hK ↦ hcomponents h K K' hK) (fun K K' hK ↦ hcomponents k K K' hK)
      (fun K K' hK ↦ hcomponents (h.trans k) K K' hK)
      (pbcIntegralScalarAssociator l Ω T dT.out iT.out h k) ((P l Ω T).assoc h k)
      (pbcScalarAssociator_exists l Ω T dT.out iT.out h k).exists.choose_spec
      (integralAssoc l Ω T h k) (assoc l Ω T h k) (assoc_app_heq l Ω T h k) (hcocycle h k) K₀
  refine ⟨?_, @hcoc, ?_, ?_⟩
  · intro E K
    obtain ⟨K₀, rfl⟩ := hess E K
    exact abstract_unit (QS l Ω T E) (scalar l Ω T (le_refl E)) (U l Ω T (le_refl E))
      (J l Ω T stage family E) (I l Ω T stage E) (pbcStageLocalization l Ω T E)
      (C l Ω T (le_refl E)) ((P l Ω T).T (le_refl E)) (scalarFactors' l Ω T (le_refl E))
      (stageFactorsJ l Ω T stage family E)
      (pbcScalarSystem_units l Ω T dT.out iT.out (le_refl E)).1 (b (le_refl E))
      (pbcScalarIntegralComparison l Ω T dT.out iT.out (le_refl E)) (j (le_refl E))
      (fun K K' hK ↦ hcomponents (le_refl E) K K' hK) (pbcIntegralScalarUnit l Ω T dT.out iT.out E)
      ((pbcScalarIntegralComparison_exists l Ω T dT.out iT.out (le_refl E)).exists.choose_spec.1
        rfl)
      (unit l Ω T E) (integralUnit l Ω T E) (unit_app_heq l Ω T E) (hunit E) K₀
  · intro E L h K
    rw [← assoc_leftUnit l Ω T h K]
    exact hcoc (le_refl E) h K
  · intro E L h K
    rw [← assoc_rightUnit l Ω T h K]
    exact hcoc h (le_refl L) K

end WeilConjectures.FdRawLocalization
