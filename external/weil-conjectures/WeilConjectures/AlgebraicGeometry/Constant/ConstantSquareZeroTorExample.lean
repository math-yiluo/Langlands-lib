/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import Mathlib.Topology.Instances.ZMod
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import all WeilConjectures.AlgebraicGeometry.PullbackFiniteConstantLocalModel
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.Double
public import Mathlib.Order.CompletePartialOrder

/-! # The constant square-zero residue and its two-term truncation example -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits
open scoped CategoryTheory.Obj MonoidalCategory ZeroObject
open MonoidalCategory Opposite

universe w v u

namespace CategoryTheory.SquareZeroInternal

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{w} C]

private def chain (n : ℕ) (hsq : (n • (𝟙 (𝟙_ C))) ≫ (n • (𝟙 (𝟙_ C))) = 0) :
    ChainComplex C ℕ :=
  ChainComplex.of (fun _ ↦ 𝟙_ C) (fun _ ↦ n • 𝟙 _) (fun _ ↦ hsq)

private theorem chain_d (n : ℕ) (hsq) (i : ℕ) :
    (chain (C := C) n hsq).d (i + 1) i = n • (𝟙 (𝟙_ C)) := by
  exact ChainComplex.of_d (fun _ : ℕ ↦ 𝟙_ C) (fun _ ↦ n • (𝟙 (𝟙_ C))) i

private noncomputable def augmentation (n : ℕ) (hsq) :
    chain (C := C) n hsq ⟶ (ChainComplex.single₀ C).obj (cokernel (n • (𝟙 (𝟙_ C)))) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨cokernel.π _, by rw [chain_d, cokernel.condition]⟩

private theorem augmentation_quasiIso (n : ℕ) (hsq)
    (hex : (ShortComplex.mk (n • (𝟙 (𝟙_ C))) (n • (𝟙 (𝟙_ C))) hsq).Exact) :
    QuasiIso (augmentation (C := C) n hsq) := by
  constructor
  intro i
  cases i with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
        ⟨ShortComplex.exact_of_g_is_cokernel
          (ShortComplex.mk _ _ (cokernel.condition (n • (𝟙 (𝟙_ C)))))
          (cokernelIsCokernel _), inferInstance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [chain, ChainComplex.of.d, HomologicalComplex.shortComplexFunctor'])
        (by simp [augmentation])
    all_goals rfl
  | succ i =>
    rw [quasiIsoAt_iff_exactAt']
    · rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp)]
      change (ShortComplex.mk _ _ _).Exact
      simpa only [chain_d] using hex
    · exact ChainComplex.exactAt_succ_single_obj _ _

private theorem residue_annihilated (n : ℕ) :
    n • (𝟙 (cokernel (n • (𝟙 (𝟙_ C))))) = 0 := by
  apply (cancel_epi (cokernel.π (n • (𝟙 (𝟙_ C))))).1
  simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
    Category.comp_id, Category.id_comp, comp_zero] using
    cokernel.condition (n • (𝟙 (𝟙_ C)))

private theorem residue_tensor_zero (n : ℕ) :
    (n • (𝟙 (𝟙_ C))) ▷ cokernel (n • (𝟙 (𝟙_ C))) = 0 := by
  let F := cokernel (n • (𝟙 (𝟙_ C)))
  change (tensorRight F).map (n • (𝟙 (𝟙_ C))) = 0
  rw [Functor.map_nsmul, Functor.map_id]
  apply (cancel_mono (λ_ F).hom).1
  have h := congrArg (fun f ↦ (λ_ F).hom ≫ f) (residue_annihilated (C := C) n)
  simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
    Category.comp_id, Category.id_comp, comp_zero, zero_comp, F] using h

private theorem not_finite_tor (n : ℕ) (hsq)
    (hex : (ShortComplex.mk (n • (𝟙 (𝟙_ C))) (n • (𝟙 (𝟙_ C))) hsq).Exact)
    (hnz : ¬ IsZero (cokernel (n • (𝟙 (𝟙_ C))))) :
    ¬ DerivedCategory.finiteTorAmplitude C
      ((DerivedCategory.singleFunctor C 0).obj (cokernel (n • (𝟙 (𝟙_ C))))) := by
  let F := cokernel (n • (𝟙 (𝟙_ C)))
  let P := chain (C := C) n hsq
  let L : CochainComplex C ℤ := P.extend ComplexShape.embeddingDownNat
  have : QuasiIso (augmentation (C := C) n hsq) := augmentation_quasiIso n hsq hex
  let π : L ⟶ (CochainComplex.singleFunctor C 0).obj F :=
    (ComplexShape.embeddingDownNat.extendFunctor C).map (augmentation n hsq) ≫
      (HomologicalComplex.extendSingleIso _ _ _ _ (by simp)).hom
  have : QuasiIso π := by
    change QuasiIso (HomologicalComplex.extendMap (augmentation n hsq)
      ComplexShape.embeddingDownNat ≫ _)
    infer_instance
  have hflat (i : ℤ) : ObjectProperty.flat (L.X i) := by
    by_cases hi : i ≤ 0
    · obtain ⟨j, rfl⟩ := Int.exists_eq_neg_ofNat hi
      exact ObjectProperty.prop_of_iso _ (HomologicalComplex.extendXIso P
        ComplexShape.embeddingDownNat (by simp : -(j : ℤ) = -(j : ℤ))).symm
        (by
          change ObjectProperty.flat (𝟙_ C)
          exact ObjectProperty.flat_of_tensorIso (λ_ (𝟙_ C)))
    · exact ObjectProperty.flat_of_isZero (L.isZero_of_isStrictlyLE 0 i (by omega))
  have hk := CochainComplex.kFlat_of_isStrictlyLE_of_flat L 0 hflat
  let e : DerivedCategory.Q.obj L ≅ (DerivedCategory.singleFunctor C 0).obj F :=
    asIso (DerivedCategory.Q.map π) ≪≫ (DerivedCategory.singleFunctorIsoCompQ C 0).symm.app F
  let T : CochainComplex C ℤ := ((tensorRight F).mapHomologicalComplex (.up ℤ)).obj L
  have hd (i j : ℤ) : T.d i j = 0 := by
    change (tensorRight F).map (L.d i j) = 0
    by_cases hi : i ≤ 0
    · by_cases hj : j ≤ 0
      · obtain ⟨a, rfl⟩ := Int.exists_eq_neg_ofNat hi
        obtain ⟨b, rfl⟩ := Int.exists_eq_neg_ofNat hj
        change (tensorRight F).map ((P.extend ComplexShape.embeddingDownNat).d (-a) (-b)) = 0
        rw [HomologicalComplex.extend_d_eq P ComplexShape.embeddingDownNat
          (i := a) (j := b) (i' := -(a : ℤ)) (j' := -(b : ℤ)) rfl rfl,
          Functor.map_comp, Functor.map_comp]
        have hz : (tensorRight F).map (P.d a b) = 0 := by
          by_cases h : a = b + 1
          · subst a
            rw [chain_d]
            exact residue_tensor_zero n
          · rw [show P.d a b = 0 from by
              change ChainComplex.of.d (fun _ : ℕ ↦ 𝟙_ C)
                (fun _ ↦ n • (𝟙 (𝟙_ C))) a b = 0
              exact ChainComplex.of_d_ne (fun _ : ℕ ↦ 𝟙_ C)
                (fun _ ↦ n • (𝟙 (𝟙_ C))) h, Functor.map_zero]
        rw [hz, zero_comp, comp_zero]
      · exact ((tensorRight F).map_isZero
          (L.isZero_of_isStrictlyLE 0 j (by omega))).eq_of_tgt _ _
    · exact ((tensorRight F).map_isZero
        (L.isZero_of_isStrictlyLE 0 i (by omega))).eq_of_src _ _
  let et : (DerivedCategory.singleFunctor C 0).obj F ⊗
      (DerivedCategory.singleFunctor C 0).obj F ≅ DerivedCategory.Q.obj T :=
    tensorIso e.symm (Iso.refl _) ≪≫ DerivedCategory.QObjTensorSingleFunctorObjIso L hk F
  intro ⟨a, b, hab⟩
  obtain ⟨q, hq⟩ := exists_nat_gt (-a)
  let eh : (DerivedCategory.homologyFunctor C (-(q : ℤ))).obj
      ((DerivedCategory.singleFunctor C 0).obj F ⊗
        (DerivedCategory.singleFunctor C 0).obj F) ≅ F :=
    (DerivedCategory.homologyFunctor C _).mapIso et ≪≫
      (DerivedCategory.homologyFunctorFactors C _).app T ≪≫
      (T.isoHomologyπ _ _ rfl (hd _ _)).symm ≪≫ T.iCyclesIso _ _ rfl (hd _ _) ≪≫
      (tensorRight F).mapIso (HomologicalComplex.extendXIso P
        ComplexShape.embeddingDownNat rfl) ≪≫ λ_ F
  exact hnz (((DerivedCategory.isGE_iff _ a).1 (hab F).1
    (-(q : ℤ)) (by omega)).of_iso eh.symm)

private theorem residue_nonzero (n : ℕ) (hsq :
    (n • (𝟙 (𝟙_ C))) ≫ (n • (𝟙 (𝟙_ C))) = 0) (hnz : ¬ IsZero (𝟙_ C)) :
    ¬ IsZero (cokernel (n • (𝟙 (𝟙_ C)))) := by
  intro hz
  have : Epi (n • (𝟙 (𝟙_ C))) :=
    Preadditive.epi_of_isZero_cokernel (n • (𝟙 (𝟙_ C))) hz
  have ht : n • (𝟙 (𝟙_ C)) = 0 := (cancel_epi (n • (𝟙 (𝟙_ C)))).1
    (hsq.trans (comp_zero).symm)
  have : Epi (0 : 𝟙_ C ⟶ 𝟙_ C) := ht ▸ inferInstance
  exact hnz ((IsZero.iff_id_eq_zero _).2 ((cancel_epi (0 : 𝟙_ C ⟶ 𝟙_ C)).1
    (by simp)))

private noncomputable def twoTerm (f : 𝟙_ C ⟶ 𝟙_ C) : CochainComplex C ℤ :=
  HomologicalComplex.double f (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)

private theorem twoTerm_ge (f : 𝟙_ C ⟶ 𝟙_ C) : (twoTerm f).IsStrictlyGE (-1) :=
  ((twoTerm f).isStrictlyGE_iff _).2 fun i hi ↦
    HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega)

private theorem twoTerm_le (f : 𝟙_ C ⟶ 𝟙_ C) : (twoTerm f).IsStrictlyLE 0 :=
  ((twoTerm f).isStrictlyLE_iff _).2 fun i hi ↦
    HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega)

private noncomputable def twoTerm_h₀ (f : 𝟙_ C ⟶ 𝟙_ C) :
    (twoTerm f).homology 0 ≅ cokernel f := by
  let L := twoTerm f
  let S : ShortComplex C := ShortComplex.mk f (0 : 𝟙_ C ⟶ 0) (by simp)
  let e : L.sc' (-1) 0 1 ≅ S :=
    ShortComplex.isoMk (HomologicalComplex.doubleXIso₀ f
        (show (ComplexShape.up ℤ).Rel (-1) 0 by simp))
      (HomologicalComplex.doubleXIso₁ f
        (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (by omega))
      ((HomologicalComplex.isZero_double_X f
        (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) 1 (by omega) (by omega)).iso
        (isZero_zero _))
      (by simp [L, S, twoTerm, HomologicalComplex.double_d])
      (by simp [L, S, twoTerm, HomologicalComplex.double_d_eq_zero₀])
  exact L.homologyIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso e ≪≫
    (ShortComplex.LeftHomologyData.ofHasCokernel S rfl).homologyIso

private noncomputable def twoTerm_h₁ (f : 𝟙_ C ⟶ 𝟙_ C) :
    (twoTerm f).homology (-1) ≅ kernel f := by
  let L := twoTerm f
  let S : ShortComplex C := ShortComplex.mk (0 : 0 ⟶ 𝟙_ C) f (by simp)
  let e : L.sc' (-2) (-1) 0 ≅ S :=
    ShortComplex.isoMk
      ((HomologicalComplex.isZero_double_X f
        (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (-2) (by omega) (by omega)).iso
        (isZero_zero _))
      (HomologicalComplex.doubleXIso₀ f
        (show (ComplexShape.up ℤ).Rel (-1) 0 by simp))
      (HomologicalComplex.doubleXIso₁ f
        (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (by omega))
      (by simp [L, S, twoTerm, HomologicalComplex.double_d_eq_zero₀])
      (by simp [L, S, twoTerm, HomologicalComplex.double_d])
  exact L.homologyIsoSc' (-2) (-1) 0 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso e ≪≫
    (ShortComplex.RightHomologyData.ofHasKernel S rfl).homologyIso

private noncomputable def residue_kernel_iso (n : ℕ) (hsq)
    (hex : (ShortComplex.mk (n • (𝟙 (𝟙_ C))) (n • (𝟙 (𝟙_ C))) hsq).Exact) :
    kernel (n • (𝟙 (𝟙_ C))) ≅ cokernel (n • (𝟙 (𝟙_ C))) :=
  (kernelIsKernel _).conePointUniqueUpToIso hex.isLimitImage' ≪≫
    ((cokernelIsCokernel _).coconePointUniqueUpToIso hex.isColimitImage).symm

private theorem twoTerm_tor (f : 𝟙_ C ⟶ 𝟙_ C) :
    DerivedCategory.finiteTorAmplitude C (DerivedCategory.Q.obj (twoTerm f)) := by
  have := twoTerm_ge f
  have := twoTerm_le f
  refine ⟨-1, 0, DerivedCategory.torAmplitudeIn_Q_obj_of_flat (twoTerm f) (-1) 0 ?_⟩
  intro i
  by_cases h₀ : i = -1
  · subst i
    exact ObjectProperty.prop_of_iso _
      (HomologicalComplex.doubleXIso₀ f
        (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)).symm
      (ObjectProperty.flat_of_tensorIso (λ_ (𝟙_ C)))
  · by_cases h₁ : i = 0
    · subst i
      exact ObjectProperty.prop_of_iso _
        (HomologicalComplex.doubleXIso₁ f
          (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (by omega)).symm
        (ObjectProperty.flat_of_tensorIso (λ_ (𝟙_ C)))
    · exact ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_double_X _ _ i h₀ h₁)

private noncomputable def twoTerm_trunc (f : 𝟙_ C ⟶ 𝟙_ C) :
    (DerivedCategory.TStructure.t.truncGE 0).obj
        (DerivedCategory.Q.obj (twoTerm f)) ≅
      (DerivedCategory.singleFunctor C 0).obj (cokernel f) := by
  let K := DerivedCategory.Q.obj (twoTerm f)
  have := twoTerm_le f
  have : K.IsLE 0 := inferInstanceAs ((DerivedCategory.Q.obj (twoTerm f)).IsLE 0)
  let L := (DerivedCategory.TStructure.t.truncGE 0).obj K
  let h := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE L 0
  let Y := Classical.choose h
  let e := Classical.choice (Classical.choose_spec h)
  have : IsIso ((DerivedCategory.homologyFunctor C 0).map
      ((DerivedCategory.TStructure.t.truncGEπ 0).app K)) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K 0 0 le_rfl
  let eh : Y ≅ cokernel f :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor C 0).mapIso e.symm ≪≫
      (asIso ((DerivedCategory.homologyFunctor C 0).map
        ((DerivedCategory.TStructure.t.truncGEπ 0).app K))).symm ≪≫
      (DerivedCategory.homologyFunctorFactors C 0).app (twoTerm f) ≪≫ twoTerm_h₀ f
  exact e ≪≫ (DerivedCategory.singleFunctor C 0).mapIso eh

end CategoryTheory.SquareZeroInternal

namespace AlgebraicGeometry.ProEtale

private theorem residue_arithmetic (ℓ : ℕ) [Fact ℓ.Prime] :
    (ℓ : ZMod (ℓ ^ 2)) ^ 2 = 0 ∧
    ∀ a : ZMod (ℓ ^ 2), (ℓ : ZMod (ℓ ^ 2)) * a = 0 ↔
      a ∈ Ideal.span ({(ℓ : ZMod (ℓ ^ 2))} : Set (ZMod (ℓ ^ 2))) := by
  have hp := (Fact.out : ℓ.Prime)
  have : NeZero (ℓ ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  constructor
  · rw [← Nat.cast_pow, ZMod.natCast_self]
  · intro a
    rw [Ideal.mem_span_singleton]
    constructor
    · intro ha
      have hd : ℓ ^ 2 ∣ ℓ * a.val := by
        apply (ZMod.natCast_eq_zero_iff _ _).1
        simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using ha
      have hd' : ℓ ∣ a.val := by
        apply (Nat.mul_dvd_mul_iff_left hp.pos).1
        simpa only [pow_two] using hd
      obtain ⟨b, hb⟩ := hd'
      refine ⟨(b : ZMod (ℓ ^ 2)), ?_⟩
      rw [← Nat.cast_mul, ← hb, ZMod.natCast_zmod_val]
    · rintro ⟨b, rfl⟩
      rw [← mul_assoc, ← pow_two, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

private theorem proetale_bot_not_cover (X : Scheme.{0}) (U : X.ProEt)
    (hU : Nonempty U.left) : ¬ (⊥ : Sieve U) ∈ Scheme.ProEt.topology X U := by
  let F := Scheme.ProEt.forget X ⋙ Over.forget X
  have hc : CoverPreserving (Scheme.ProEt.topology X) Scheme.proetaleTopology F :=
    CoverPreserving.of_isContinuous F _ _
  have hj : Scheme.proetaleTopology.{0} ≤ Scheme.jointlySurjectiveTopology := by
    rw [Scheme.jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology]
    change Scheme.proetalePrecoverage.toGrothendieck ≤
      Scheme.jointlySurjectivePrecoverage.toPretopology.toGrothendieck
    rw [Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
    exact Precoverage.toGrothendieck_mono (le_trans inf_le_right inf_le_left)
  intro h
  have hb : (⊥ : Sieve U.left) ∈ Scheme.proetaleTopology U.left := by
    simpa only [Sieve.functorPushforward_bot, F, Functor.comp_obj,
      Scheme.ProEt.forget, MorphismProperty.Over.forget, MorphismProperty.Comma.forget,
      Over.forget_obj] using hc.cover_preserve h
  have hs := hj U.left hb
  change (⊥ : Presieve U.left) ∈ Scheme.jointlySurjectivePrecoverage U.left at hs
  rw [Precoverage.mem_comap_iff, Presieve.map_bot,
    Types.mem_jointlySurjectivePrecoverage_iff] at hs
  obtain ⟨x⟩ := hU
  obtain ⟨W, f, hf, _⟩ := hs x
  exact hf

private theorem constant_ab_injective (X : Scheme.{0}) [Nonempty X]
    (B : AddCommGrpCat.{1}) :
    Function.Injective ((toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj B)).app (op (Scheme.ProEt.mk (𝟙 X)))) := by
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{1} :=
    inferInstance
  intro a b hab
  by_contra hne
  have h := Presheaf.equalizerSieve_mem (Scheme.ProEt.topology X)
    (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj B)) a b hab
  have he : Presheaf.equalizerSieve (F := (Functor.const X.ProEtᵒᵖ).obj B)
      (X := op (Scheme.ProEt.mk (𝟙 X))) a b = ⊥ := by
    ext W f
    simp [Presheaf.equalizerSieve, hne]
  rw [he] at h
  exact proetale_bot_not_cover X (Scheme.ProEt.mk (𝟙 X))
    (show Nonempty (Scheme.ProEt.mk (𝟙 X)).left from inferInstanceAs (Nonempty X)) h

private theorem coefficient_data (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{0}) Ab.{1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Nonempty (Mon.mk Λ ≅
      Mon.mk (Profinite.continuousCoefficientRingObj.{0} (ZMod (ℓ ^ 2)))))
    (X : Scheme.{0}) [Nonempty X] :
    let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{1}) (condensedRingObj Λ X)
    ∃ hsq : (ℓ • (𝟙 (𝟙_ C))) ≫ (ℓ • (𝟙 (𝟙_ C))) = 0,
      (ShortComplex.mk (ℓ • (𝟙 (𝟙_ C))) (ℓ • (𝟙 (𝟙_ C))) hsq).Exact ∧
      ¬ IsZero (𝟙_ C) := by
  have hp := (Fact.out : ℓ.Prime)
  have : NeZero (ℓ ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : Fact (1 < ℓ ^ 2) := ⟨by have := hp.two_le; nlinarith⟩
  let A := ZMod (ℓ ^ 2)
  let B : Ab.{1} := AddCommGrpCat.of (ULift.{1} A)
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{1}) (condensedRingObj Λ X)
  let F := constantSheaf (Scheme.ProEt.topology X) Ab.{1}
  let U : C ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{1} :=
    Mod.forget (condensedRingObj Λ X)
  obtain ⟨eΛ⟩ := hΛ
  have := FiniteDiscreteOrdinary.canonicalAbelianMap_isIso A X
  let e : F.obj B ≅ U.obj (𝟙_ C) :=
    asIso (FiniteDiscreteOrdinary.canonicalAbelianMap A X) ≪≫
      (upperStarFromPoint X).mapIso ((Mon.forget _).mapIso eΛ.symm)
  have hsqB : (ℓ • (𝟙 B)) ≫ (ℓ • (𝟙 B)) = 0 := by
    ext x
    change ℓ • (ℓ • x.down) = (0 : A)
    simp only [nsmul_eq_mul]
    rw [← mul_assoc, ← pow_two, (residue_arithmetic ℓ).1, zero_mul]
  have hB : (ShortComplex.mk (ℓ • (𝟙 B)) (ℓ • (𝟙 B)) hsqB).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x hx
    change ℓ • x = (0 : ULift.{1} A) at hx
    have hx₀ : ℓ • x.down = (0 : A) := congrArg ULift.down hx
    have hx' : (ℓ : A) * x.down = 0 := by
      simpa only [nsmul_eq_mul] using hx₀
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ((residue_arithmetic ℓ).2 x.down |>.mp hx')
    refine ⟨ULift.up b, ?_⟩
    apply ULift.ext
    change ℓ • b = x.down
    simpa only [nsmul_eq_mul] using hb.symm
  have hsqU : (ℓ • (𝟙 (U.obj (𝟙_ C)))) ≫ (ℓ • (𝟙 (U.obj (𝟙_ C)))) = 0 := by
    apply (cancel_epi e.hom).1
    have h := congrArg (fun f ↦ F.map f ≫ e.hom) hsqB
    simpa only [Functor.map_comp, Functor.map_nsmul, Functor.map_id, Functor.map_zero, F.map_id B,
      Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
      Category.comp_id, zero_comp, comp_zero] using h
  have hsq : (ℓ • (𝟙 (𝟙_ C))) ≫ (ℓ • (𝟙 (𝟙_ C))) = 0 := by
    apply U.map_injective
    simpa only [Functor.map_comp, Functor.map_nsmul, U.map_id, Functor.map_zero]
      using hsqU
  refine ⟨hsq, ?_, ?_⟩
  · apply ((ShortComplex.mk _ _ hsq).exact_map_iff_of_faithful U).1
    let i : (ShortComplex.mk _ _ hsqB).map F ≅ (ShortComplex.mk _ _ hsq).map U :=
      ShortComplex.isoMk e e e
        (by
          change e.hom ≫ U.map (ℓ • 𝟙 _) = F.map (ℓ • 𝟙 _) ≫ e.hom
          simp only [Functor.map_nsmul, U.map_id, F.map_id,
            Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
            Category.comp_id])
        (by
          change e.hom ≫ U.map (ℓ • 𝟙 _) = F.map (ℓ • 𝟙 _) ≫ e.hom
          simp only [Functor.map_nsmul, U.map_id, F.map_id,
            Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
            Category.comp_id])
    exact (ShortComplex.exact_iff_of_iso i).mp (hB.map F)
  · intro hz
    have hzB := (U.map_isZero hz).of_iso e
    have hid : 𝟙 (F.obj B) = 0 := hzB.eq_of_src _ _
    let η := (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj B)).app (op (Scheme.ProEt.mk (𝟙 X)))
    have he : η (1 : ULift.{1} A) = η 0 := by
      have h := congrArg (fun f : F.obj B ⟶ F.obj B ↦
        f.hom.app (op (Scheme.ProEt.mk (𝟙 X))) (η (1 : ULift.{1} A))) hid
      change η (1 : ULift.{1} A) = 0 at h
      simpa only [map_zero] using h
    exact (one_ne_zero : (1 : ULift.{1} A) ≠ 0) (constant_ab_injective X B he)

private theorem residue_fp
    (Λ : Sheaf (coherentTopology Profinite.{0}) Ab.{1}) [MonObj Λ] [IsCommMonObj Λ] (n : ℕ) :
    Mod.IsFinitelyPresented Λ
      (cokernel (n • (𝟙 (𝟙_ (Mod (Sheaf (coherentTopology Profinite.{0}) Ab.{1}) Λ))))) := by
  let e : Mod.finiteFree Λ 1 ≅
      𝟙_ (Mod (Sheaf (coherentTopology Profinite.{0}) Ab.{1}) Λ) :=
    biproductUniqueIso _
  refine ⟨1, 1, e.hom ≫ (n • 𝟙 _) ≫ e.inv, ⟨?_⟩⟩
  exact cokernel.mapIso _ _ e.symm e.symm (by simp)

private theorem point_model
    (Λ : Sheaf (coherentTopology Profinite.{0}) Ab.{1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{0})
    (P : Mod (Sheaf (coherentTopology Profinite.{0}) Ab.{1}) Λ)
    (hP : Mod.IsFinitelyPresented Λ P) :
    HasFiniteConstantLocalModel Λ X (((upperStarFromPoint X).mapMod Λ).obj P) := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
  exact ⟨P, hP, ⟨(pullback_point_iso Λ (𝟙 X)).app P⟩⟩

private theorem local_constructible
    (Λ : Sheaf (coherentTopology Profinite.{0}) Ab.{1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{0})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ X M) : IsConstantModelConstructible Λ X M := by
  classical
  have strat (Y : Scheme.{0})
      (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{1}) (condensedRingObj Λ Y))
      (hN : HasFiniteConstantLocalModel Λ Y N) : IsFiniteConstantStratified Λ Y N :=
    ⟨Scheme.Stratification.trivial Y, fun _ ↦
      pullback_finiteConstantLocalModel Λ (𝟙 Y) N hN⟩
  unfold IsConstantModelConstructible
  split_ifs
  · exact strat X M hM
  · intro U _
    exact strat _ _ (pullback_finiteConstantLocalModel Λ U.ι M hM)

private theorem constructible_iso
    (Λ : Sheaf (coherentTopology Profinite.{0}) Ab.{1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{0})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X) e hM

private theorem zero_constructible
    (Λ : Sheaf (coherentTopology Profinite.{0}) Ab.{1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{0})
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{1}) (condensedRingObj Λ X)}
    (hM : IsZero M) : IsConstantModelConstructible Λ X M := by
  have : pointUpperStar.{0}.IsLeftAdjoint :=
    pointUpperStarLowerStarAdjunction.isLeftAdjoint
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : (upperStarFromPoint X).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  let F := (upperStarFromPoint X).mapMod Λ
  have hP : Mod.IsFinitelyPresented Λ 0 :=
    ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  exact constructible_iso Λ X ((F.map_isZero (isZero_zero _)).iso hM)
    (local_constructible Λ X _ (point_model Λ X 0 hP))

private noncomputable def residue_pullback_iso
    (Λ : Sheaf (coherentTopology Profinite.{0}) Ab.{1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{0}) (n : ℕ) :
    ((upperStarFromPoint X).mapMod Λ).obj
        (cokernel (n • (𝟙 (𝟙_ (Mod (Sheaf (coherentTopology Profinite.{0}) Ab.{1}) Λ))))) ≅
      cokernel (n • (𝟙 (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{1})
        (condensedRingObj Λ X))))) := by
  have : pointUpperStar.{0}.IsLeftAdjoint :=
    pointUpperStarLowerStarAdjunction.isLeftAdjoint
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : (upperStarFromPoint X).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  let F := (upperStarFromPoint X).mapMod Λ
  let e : 𝟙_ (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{1}) (condensedRingObj Λ X)) ≅
      F.obj (𝟙_ (Mod (Sheaf (coherentTopology Profinite.{0}) Ab.{1}) Λ)) :=
    Mod.isoMk (Iso.refl _) (by simp)
  exact PreservesCokernel.iso F _ ≪≫
    cokernel.mapIso _ _ e.symm e.symm (by simp only [Functor.map_nsmul, F.map_id,
      Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp, Category.comp_id])

/-- The constant square-zero residue has infinite Tor amplitude; its finite-free
presentation cone is bounded constructible of finite Tor amplitude and its upper
truncation is not of finite Tor amplitude.

Source: blueprint main-20261015, localizing-closure ctf-equals-bc proof, Examples
(blueprint: lem-sfb-constant-square-zero-tor-example).

Proof: set A = Z/ell^2. Primality gives ell^2 = 0 and ann(ell) = ell A.
The finite-discrete canonical abelian coefficient comparison, composed with the given
coefficient isomorphism, identifies the underlying internal tensor unit with the
constant abelian sheaf A. Exact constant sheafification and faithful exact forgetting
therefore show that multiplication by ell on this unit is square zero and its repeated
short complex is exact. Constant sections inject on the identity pro-etale object of
the nonempty scheme Spec k, so the unit is nonzero.
Construct the internal chain complex with this unit in every nonnegative degree and
multiplication by ell as differential, augmented to F = coker(ell). Exactness makes
this a resolution. Reindex in nonpositive cochain degrees; its flat terms and upper
bound make it K-flat. Ell annihilates F by the cokernel equation, so tensoring the
resolution with F kills all differentials. The source K-flat tensor comparison gives
H^(-q)(F[0] tensor-derived F[0]) = F for every natural q. The residue F is nonzero:
otherwise ell is epic, and its square-zero relation forces the unit to vanish.
Consequently F[0] has no finite lower Tor bound.
The condensed cokernel has a one-generator, one-relation finite presentation. Its
pullback is the internal cokernel because inverse image preserves the unit, integer
scalars and cokernels. The identity cover and trivial stratification establish its
constant-model constructibility; pullback handles the affine-local convention.
Finally construct [unit --ell--> unit] in degrees -1 and 0. Its flat terms give Tor
amplitude [-1,0]. Its homology is F in both degrees, using the image/coimage comparison
for ker(ell), and zero elsewhere, hence it is bounded constructible. Its upper
truncation at zero is isomorphic to F[0] by the single-degree derived-category theorem
and the degree-zero truncation map on homology. Isomorphism invariance transfers the
infinite Tor amplitude. The proof includes ell = 2 and every characteristic of k. -/
theorem constant_square_zero_tor_example (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{0}) Ab.{1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Nonempty (Mon.mk Λ ≅
      Mon.mk (Profinite.continuousCoefficientRingObj.{0} (ZMod (ℓ ^ 2)))))
    (k : Type) [Field k] [IsSepClosed k] :
    let X : Scheme.{0} := Scheme.Spec.obj (Opposite.op (CommRingCat.of k))
    let C := Mod (Sheaf (coherentTopology Profinite.{0}) Ab.{1}) Λ
    let P := cokernel ((ℓ : ℕ) • (𝟙 (𝟙_ C)))
    let Cₓ := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{1}) (condensedRingObj Λ X)
    let M : Cₓ := ((upperStarFromPoint X).mapMod Λ).obj P
    IsConstantModelConstructible Λ X M ∧
    ¬ _root_.DerivedCategory.finiteTorAmplitude Cₓ
      ((_root_.DerivedCategory.singleFunctor Cₓ 0).obj M) ∧
    ∃ K : DerivedCategory Cₓ,
      (constantModelBoundedConstructible Λ X ⊓
        _root_.DerivedCategory.finiteTorAmplitude Cₓ) K ∧
      ¬ _root_.DerivedCategory.finiteTorAmplitude Cₓ
        ((_root_.DerivedCategory.TStructure.t.truncGE 0).obj K) := by
  classical
  dsimp only
  let X : Scheme.{0} := Scheme.Spec.obj (op (CommRingCat.of k))
  let C := Mod (Sheaf (coherentTopology Profinite.{0}) Ab.{1}) Λ
  let Cₓ := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{1}) (condensedRingObj Λ X)
  let P : C := cokernel (ℓ • (𝟙 (𝟙_ C)))
  let M : Cₓ := ((upperStarFromPoint X).mapMod Λ).obj P
  change IsConstantModelConstructible Λ X M ∧
    ¬ _root_.DerivedCategory.finiteTorAmplitude Cₓ
      ((_root_.DerivedCategory.singleFunctor Cₓ 0).obj M) ∧ _
  have hM : IsConstantModelConstructible Λ X M :=
    local_constructible Λ X M (point_model Λ X P (residue_fp Λ ℓ))
  let e : M ≅ cokernel (ℓ • (𝟙 (𝟙_ Cₓ))) := residue_pullback_iso Λ X ℓ
  have : Nonempty X := inferInstanceAs (Nonempty (PrimeSpectrum k))
  obtain ⟨hsq, hex, hnz⟩ := coefficient_data ℓ Λ hΛ X
  have hnot : ¬ _root_.DerivedCategory.finiteTorAmplitude Cₓ
      ((_root_.DerivedCategory.singleFunctor Cₓ 0).obj (cokernel (ℓ • (𝟙 (𝟙_ Cₓ))))) :=
    CategoryTheory.SquareZeroInternal.not_finite_tor ℓ hsq hex
      (CategoryTheory.SquareZeroInternal.residue_nonzero ℓ hsq hnz)
  refine ⟨hM, fun h ↦ hnot (ObjectProperty.prop_of_iso
    (_root_.DerivedCategory.finiteTorAmplitude Cₓ)
    ((_root_.DerivedCategory.singleFunctor Cₓ 0).mapIso e) h), ?_⟩
  let f : 𝟙_ Cₓ ⟶ 𝟙_ Cₓ := ℓ • 𝟙 _
  let L := CategoryTheory.SquareZeroInternal.twoTerm f
  let K := _root_.DerivedCategory.Q.obj L
  have := CategoryTheory.SquareZeroInternal.twoTerm_ge f
  have := CategoryTheory.SquareZeroInternal.twoTerm_le f
  have hres : IsConstantModelConstructible Λ X (cokernel f) :=
    constructible_iso Λ X e hM
  refine ⟨K, ⟨⟨?_, ?_⟩, CategoryTheory.SquareZeroInternal.twoTerm_tor f⟩, ?_⟩
  · exact (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).mp
      ⟨-1, 0, inferInstance, inferInstance⟩
  · intro q
    let eh := (_root_.DerivedCategory.homologyFunctorFactors Cₓ q).app L
    by_cases hq₀ : q = 0
    · subst q
      exact constructible_iso Λ X
        (eh ≪≫ CategoryTheory.SquareZeroInternal.twoTerm_h₀ f).symm hres
    · by_cases hq₁ : q = -1
      · subst q
        exact constructible_iso Λ X
          (eh ≪≫ CategoryTheory.SquareZeroInternal.twoTerm_h₁ f ≪≫
            CategoryTheory.SquareZeroInternal.residue_kernel_iso ℓ hsq hex).symm hres
      · apply zero_constructible Λ X
        by_cases hq : q < -1
        · exact _root_.DerivedCategory.isZero_of_isGE K (-1) q hq
        · exact _root_.DerivedCategory.isZero_of_isLE K 0 q (by omega)
  · intro h
    exact hnot (ObjectProperty.prop_of_iso (_root_.DerivedCategory.finiteTorAmplitude Cₓ)
      (CategoryTheory.SquareZeroInternal.twoTerm_trunc f) h)

end AlgebraicGeometry.ProEtale
