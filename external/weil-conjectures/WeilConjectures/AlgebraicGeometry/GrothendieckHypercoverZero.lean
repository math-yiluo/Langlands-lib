/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverComparisonCocone
import WeilConjectures.AlgebraicGeometry.GrothendieckInjectiveHypercoverRow
import all WeilConjectures.AlgebraicGeometry.HypercoverInjectiveModuleRow
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Sites.Hypercover.One

/-! # Degree-zero hypercover comparison

Source: the sheaf equalizer argument in Stacks Project, Hypercoverings, Tag 01GV.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u' u
open CategoryTheory Limits Opposite CategoryTheory.Preadditive

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

private noncomputable def pairMatching (U : FiniteSplitEtaleHypercover X)
    (T : X.Etale) (a b : T ⟶ U.simplicial.obj (op (SimplexCategory.mk 0)))
    (Δ : SimplexCategory) (h : Δ.len < 1) (θ : Δ ⟶ SimplexCategory.mk 1) :
    T ⟶ U.simplicial.obj (op Δ) := by
  obtain rfl : Δ = SimplexCategory.mk 0 := SimplexCategory.ext (by change Δ.len = 0; omega)
  exact if θ.toOrderHom 0 = 0 then a else b

private lemma pairMatching_naturality (U : FiniteSplitEtaleHypercover X)
    (T : X.Etale) (a b : T ⟶ U.simplicial.obj (op (SimplexCategory.mk 0)))
    (Δ Δ' : SimplexCategory) (h : Δ.len < 1) (h' : Δ'.len < 1)
    (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk 1) :
    pairMatching U T a b Δ h θ ≫ U.simplicial.map α.op =
      pairMatching U T a b Δ' h' (α ≫ θ) := by
  obtain rfl : Δ = SimplexCategory.mk 0 := SimplexCategory.ext (by change Δ.len = 0; omega)
  obtain rfl : Δ' = SimplexCategory.mk 0 := SimplexCategory.ext (by change Δ'.len = 0; omega)
  have hα : α = 𝟙 (SimplexCategory.mk 0) := Subsingleton.elim _ _
  subst α
  simp

private noncomputable def zeroOneHypercover (U : FiniteSplitEtaleHypercover X) :
    X.smallEtaleTopology.OneHypercover (⊤_ X.Etale) where
  I₀ := Unit
  X _ := U.simplicial.obj (op (SimplexCategory.mk 0))
  f _ := terminal.from _
  I₁ _ _ := Unit
  Y _ _ _ := U.simplicial.obj (op (SimplexCategory.mk 1))
  p₁ _ _ _ := U.simplicial.δ 1
  p₂ _ _ _ := U.simplicial.δ 0
  w _ _ _ := terminal.hom_ext _ _
  mem₀ := by
    obtain ⟨S, hS, h⟩ :=
      FiniteSplitEtaleHypercover.matching_local_lifting U 0 (⊤_ X.Etale)
      (fun Δ h _ ↦ False.elim (by omega)) (by intro Δ Δ' h; omega)
    apply X.smallEtaleTopology.superset_covering (S := S) ?_ hS
    intro T f hf
    obtain ⟨t, _⟩ := h T f hf
    exact ⟨_, t, terminal.from _, ⟨()⟩, terminal.hom_ext _ _⟩
  mem₁ _ _ T a b _ := by
    obtain ⟨S, hS, h⟩ := FiniteSplitEtaleHypercover.matching_local_lifting U 1 T
      (pairMatching U T a b) (pairMatching_naturality U T a b)
    apply X.smallEtaleTopology.superset_covering (S := S) ?_ hS
    intro V f hf
    obtain ⟨t, ht⟩ := h V f hf
    refine ⟨(), t, ?_, ?_⟩
    · simpa [pairMatching, SimplicialObject.δ, SimplexCategory.δ_one_eq_const] using
        (ht (SimplexCategory.mk 0) (by decide) (SimplexCategory.δ 1)).symm
    · simpa [pairMatching, SimplicialObject.δ, SimplexCategory.δ_zero_eq_const] using
        (ht (SimplexCategory.mk 0) (by decide) (SimplexCategory.δ 0)).symm

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

omit [IsGrothendieckAbelian.{u + 1} A] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Degree-zero hypercover descent is the sheaf equalizer.
The first two matching covers give a one-hypercover. Its limiting multifork is
precisely the kernel of the alternating first differential. -/
private theorem sectionAugmentation_quasiIsoAt_zero (U : FiniteSplitEtaleHypercover X)
    (F : Sheaf X.smallEtaleTopology A) : QuasiIsoAt (sectionAugmentation A U F) 0 := by
  let E := zeroOneHypercover U
  let K := (sectionComplexFunctor A U).obj F
  let a := sectionAugmentation A U F
  have hd : K.d 0 1 = F.obj.map (U.simplicial.δ 0).op -
      F.obj.map (U.simplicial.δ 1).op := by
    simp [K, sectionComplexFunctor, AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj,
      CochainComplex.of.d, AlgebraicTopology.AlternatingCofaceMapComplex.objD,
      Fin.sum_univ_two]
    simp [CosimplicialObject.δ, SimplicialObject.δ, sub_eq_add_neg]
  have ha : a.f 0 = F.obj.map (terminal.from _).op := by
    simp only [a, sectionAugmentation, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  let S := ShortComplex.mk (a.f 0) (K.d 0 1) (by
    simpa only [HomologicalComplex.single_obj_d, zero_comp] using a.comm 0 1)
  let z {T : A} (f : T ⟶ K.X 0) (hf : f ≫ K.d 0 1 = 0) :
      Multifork (E.multicospanIndex F.obj) :=
    Multifork.ofι _ T (fun _ ↦ f) (by
      rintro ⟨⟨i, j⟩, k⟩
      change f ≫ F.obj.map (U.simplicial.δ 1).op =
        f ≫ F.obj.map (U.simplicial.δ 0).op
      have hh := hf
      rw [hd, comp_sub, sub_eq_zero] at hh
      exact hh.symm)
  let lift {T : A} (f : T ⟶ K.X 0) (hf : f ≫ K.d 0 1 = 0) :
      T ⟶ (terminalSections (X := X) A).obj F :=
    Multifork.IsLimit.lift (E.isLimitMultifork F) (z f hf).ι (z f hf).condition
  have fac {T : A} (f : T ⟶ K.X 0) (hf : f ≫ K.d 0 1 = 0) :
      lift f hf ≫ a.f 0 = f := by
    rw [ha]
    exact Multifork.IsLimit.fac (E.isLimitMultifork F) (z f hf).ι (z f hf).condition ()
  have hk : IsLimit (KernelFork.ofι S.f S.zero) :=
    KernelFork.IsLimit.ofι _ _ (fun f hf ↦ lift f hf) fac (by
      intro T f hf m hm
      apply Multifork.IsLimit.hom_ext (E.isLimitMultifork F)
      intro i
      have hh : m ≫ a.f 0 = lift f hf ≫ a.f 0 := hm.trans (fac f hf).symm
      simpa only [E, zeroOneHypercover, PreOneHypercover.multifork_ι, ha] using hh)
  rw [CochainComplex.quasiIsoAt₀_iff]
  apply (ShortComplex.quasiIso_iff_of_zeros _ ?_ ?_ ?_).mpr
    ⟨S.exact_of_f_is_kernel hk, mono_of_isLimit_fork hk⟩
  · exact HomologicalComplex.single_obj_d (.up ℕ) 0 _ 0 1
  · exact HomologicalComplex.single_obj_d (.up ℕ) 0 _ 0 0
  · exact K.shape 0 0 (by simp)

private noncomputable def sectionResolutionZeroMap
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F) :
    (CochainComplex.single₀ A).obj ((terminalSections A).obj F) ⟶
      sectionResolution A I.cocomplex :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨(terminalSections A).map (I.ι.f 0), by
      change (terminalSections A).map (I.ι.f 0) ≫
        (terminalSections A).map (I.cocomplex.d 0 1) = 0
      rw [← Functor.map_comp]
      have h := I.ι.comm 0 1
      rw [HomologicalComplex.single_obj_d, zero_comp] at h
      rw [h, Functor.map_zero]⟩

omit [CompactSpace X] [QuasiSeparatedSpace X] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionResolutionZeroMap_quasiIsoAt
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F) :
    QuasiIsoAt (sectionResolutionZeroMap A I) 0 := by
  have : PreservesFiniteLimits (terminalSections (X := X) A) := by
    unfold terminalSections
    infer_instance
  let S := ShortComplex.mk ((terminalSections A).map (I.ι.f 0))
    ((terminalSections A).map (I.cocomplex.d 0 1)) (by
      rw [← Functor.map_comp]
      have h := I.ι.comm 0 1
      rw [HomologicalComplex.single_obj_d, zero_comp] at h
      rw [h, Functor.map_zero])
  have hk : IsLimit (KernelFork.ofι S.f S.zero) :=
    KernelFork.mapIsLimit _ I.isLimitKernelFork (terminalSections A)
  rw [CochainComplex.quasiIsoAt₀_iff]
  apply (ShortComplex.quasiIso_iff_of_zeros _ ?_ ?_ ?_).mpr ⟨?_, ?_⟩
  · exact HomologicalComplex.single_obj_d (.up ℕ) 0 _ 0 1
  · exact HomologicalComplex.single_obj_d (.up ℕ) 0 _ 0 0
  · exact (sectionResolution A I.cocomplex).shape 0 0 (by simp)
  · change (ShortComplex.mk ((sectionResolutionZeroMap A I).f 0)
        ((sectionResolution A I.cocomplex).d 0 1) _).Exact
    have hh : (sectionResolutionZeroMap A I).f 0 =
        (terminalSections A).map (I.ι.f 0) := by
      exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
    simpa only [hh, S, sectionResolution, CochainComplex.single₀_obj_zero,
      Functor.mapHomologicalComplex_obj_X, Functor.mapHomologicalComplex_obj_d] using
        S.exact_of_f_is_kernel hk
  · change Mono ((sectionResolutionZeroMap A I).f 0)
    have hh : (sectionResolutionZeroMap A I).f 0 =
        (terminalSections A).map (I.ι.f 0) := by
      exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
    rw [hh]
    exact mono_of_isLimit_fork hk

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionResolutionZeroMap_triangle (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F) :
    sectionAugmentation A U F ≫ bottomInclusion A U I =
      sectionResolutionZeroMap A I ≫ resolutionAugmentation A U I.cocomplex := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [HomologicalComplex.comp_f, sectionAugmentation, sectionResolutionZeroMap,
      CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    dsimp only [bottomInclusion, resolutionAugmentation, restrictionToZero]
    let t := (resolutionDoubleComplex A U I.cocomplex).ιTotal (.up ℕ) 0 0 0 (by simp)
    with_unfolding_all
      change F.obj.map (terminal.from _).op ≫
          (I.ι.f 0).hom.app (op (U.simplicial.obj (op (SimplexCategory.mk 0)))) ≫ t =
        (I.ι.f 0).hom.app (op (⊤_ X.Etale)) ≫
          (I.cocomplex.X 0).obj.map (terminal.from _).op ≫ t
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f ↦ f ≫ t)
          ((I.ι.f 0).hom.naturality (terminal.from _).op)).trans (Category.assoc _ _ _))
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ n hn).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
/-- The explicit comparison is invertible in degree zero.
The section augmentation and the terminal-section resolution map are both
quasi-isomorphisms in degree zero. Their augmentation square proves the claim. -/
private theorem isIso_comparisonAt_zero (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F)
    [QuasiIso (resolutionAugmentation A U I.cocomplex)] :
    IsIso (comparisonAt A U I 0) := by
  have := sectionAugmentation_quasiIsoAt_zero A U F
  have := sectionResolutionZeroMap_quasiIsoAt A I
  have h := congrArg (fun f ↦ HomologicalComplex.homologyMap f 0)
    (sectionResolutionZeroMap_triangle A U I)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  have : IsIso (HomologicalComplex.homologyMap (sectionAugmentation A U F) 0 ≫
      HomologicalComplex.homologyMap (bottomInclusion A U I) 0) := by
    rw [h]
    infer_instance
  have : IsIso (HomologicalComplex.homologyMap (bottomInclusion A U I) 0) :=
    IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap (sectionAugmentation A U F) 0) _
  unfold comparisonAt
  infer_instance

local instance : HasColimitsOfSize.{u, u + 1} A :=
  hasColimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A

set_option backward.isDefEq.respectTransparency false in
/-- The explicit comparison cocone is colimiting in degree zero.
Source: Stacks Project, Hypercoverings, Tag 01GV, the sheaf equalizer argument.
(auxiliary; not a blueprint node).

Proof: the degree-zero and degree-one matching covers give a one-hypercover.
The sheaf multifork is limiting, so its augmentation is a degree-zero
quasi-isomorphism for every sheaf, with no injectivity assumption. The
terminal-section functor preserves finite limits, hence also the initial kernel
fork of an injective resolution. The augmentation square then makes the bottom
inclusion a degree-zero quasi-isomorphism. The explicit comparison is therefore
invertible on every hypercover. A cocone of isomorphisms over a connected index
is colimiting, giving the displayed isomorphism for the actual filtered index. -/
theorem isIso_colimit_comparison_zero (F : Sheaf X.smallEtaleTopology A) :
    IsIso (colimit.desc (homotopyCohomologyDiagram A F 0) (comparisonCocone A F 0)) := by
  have : IsConnected (HomotopyIndex X) := IsFiltered.isConnected _
  let C := comparisonCocone A F 0
  have hrow (U : FiniteSplitEtaleHypercover X) (F : Sheaf X.smallEtaleTopology A)
      (h : Injective F) : QuasiIso (sectionAugmentation A U F) := by
    have := h
    exact injective_row_quasiIso A U F
  have (U : HomotopyIndex X) : IsIso (C.ι.app U) := by
    have := resolutionAugmentation_quasiIso A hrow U.as.unop (injectiveResolution F)
    exact isIso_comparisonAt_zero A U.as.unop (injectiveResolution F)
  have : IsIso C.ι := NatIso.isIso_of_isIso_app _
  have hC : IsColimit C := C.isColimitOfIsIsoColimMapι
  exact ((colimit.isColimit _).nonempty_isColimit_iff_isIso_desc).mp ⟨hC⟩

end AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck
