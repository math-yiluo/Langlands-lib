/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.AlgebraicGeometry.Sites.Small
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import WeilConjectures.AlgebraicGeometry.EtaleOpenCechProductComparison
import WeilConjectures.CategoryTheory.InjectiveSheafCechAcyclic
import WeilConjectures.Topology.Sheaves.CechComparison
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Homology.SingleHomology

/-! # The injective étale Čech row on an open covering

Source: Stacks Project, Tags 03AW and 03F6.
(blueprint: lem-sc-etale-open-cech-injective-augmentation)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

open TopologicalSpace

-- Canonical degree-zero descent, following the proved open Čech homology calculation
-- in WeilConjectures.Topology.OpenCechZerothHomology (Stacks 03AN).
set_option backward.isDefEq.respectTransparency false in
private theorem openCechAugmentation_zero
    {T : TopCat.{u}} {ι : Type u} (U : ι → TopologicalSpace.Opens T)
    (hU : iSup U = ⊤)
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u + 1})
    (e : (CochainComplex.single₀ AddCommGrpCat.{u + 1}).obj (F.obj.obj (op ⊤)) ⟶
      (cechComplexFunctor U).obj F.obj)
    (he : ∀ t : Fin 1 → ι,
      e.f 0 ≫ Pi.π (fun s : Fin 1 → ι ↦
        F.obj.obj (op (∏ᶜ fun k ↦ U (s k)))) t =
          F.obj.map (homOfLE le_top).op) : QuasiIsoAt e 0 := by
  classical
  let P := F.obj
  let K := (CategoryTheory.cechComplexFunctor U).obj P
  let V := fun y : Fin 1 → ι ↦ ∏ᶜ fun l ↦ U (y l)
  have hV : (⊤ : TopologicalSpace.Opens T) ≤ iSup V := by
    rw [← hU]
    refine iSup_le fun j ↦ le_iSup_of_le (fun _ ↦ j) ?_
    exact (Pi.lift fun _ ↦ homOfLE le_rfl).le
  let a : P.obj (op ⊤) ⟶ K.X 0 := Pi.lift fun y ↦ P.map (homOfLE le_top).op
  have hap (y : Fin 1 → ι) :
      a ≫ TopCat.Presheaf.cechComplexFunctorπ U P 0 y = P.map (homOfLE le_top).op :=
    Pi.lift_comp_π _ y
  have ha : a ≫ K.d 0 1 = 0 := by
    apply Pi.hom_ext
    intro y
    rw [Category.assoc, zero_comp]
    change a ≫ K.d 0 1 ≫ TopCat.Presheaf.cechComplexFunctorπ U P 1 y = 0
    rw [TopCat.Presheaf.cechComplexFunctor_d_π]
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul]
    have hh (j : Fin 2) : a ≫ TopCat.Presheaf.cechComplexFunctorπ U P 0
        (y ∘ j.succAbove) ≫ P.map
          (Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l)) (j.succAbove l)).op =
        P.map (homOfLE le_top).op := by
      rw [← Category.assoc, hap, ← Functor.map_comp]
      congr 1
    simp_rw [hh]
    simp [Fin.sum_univ_two]
  let b := K.liftCycles a 1 (by simp) ha
  have hb : IsIso b := by
    rw [ConcreteCategory.isIso_iff_bijective]
    have hi : Function.Injective (K.iCycles 0) :=
      (AddCommGrpCat.mono_iff_injective _).1 inferInstance
    have hbi (s : P.obj (op ⊤)) : K.iCycles 0 (b s) = a s :=
      ConcreteCategory.congr_hom (K.liftCycles_i _ _ _ _) s
    constructor
    · intro s t hst
      apply TopCat.Sheaf.eq_of_locally_eq' F V ⊤ (fun _ ↦ homOfLE le_top) hV
      intro y
      have h := congrArg (fun c ↦ (TopCat.Presheaf.cechComplexFunctorπ U P 0 y)
        (K.iCycles 0 c)) hst
      simp only [hbi] at h
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hap] at h
      exact h
    · intro c
      have hd : K.d 0 1 (K.iCycles 0 c) = 0 :=
        ConcreteCategory.congr_hom (K.iCycles_d 0 1) c
      let sf := fun y ↦ TopCat.Presheaf.cechComplexFunctorπ U P 0 y (K.iCycles 0 c)
      have hc : TopCat.Presheaf.IsCompatible P V sf := by
        intro y z
        let t : Fin 2 → ι := fun j ↦ if j = 0 then y 0 else z 0
        have h0 : t ∘ (0 : Fin 2).succAbove = z := by
          funext l
          fin_cases l
          simp [t]
        have h1 : t ∘ (1 : Fin 2).succAbove = y := by
          funext l
          fin_cases l
          simp [t]
        let W := ∏ᶜ fun l ↦ U (t l)
        let f : V y ⊓ V z ⟶ W := Pi.lift fun j ↦ homOfLE (by
          fin_cases j
          · exact inf_le_left.trans ((Pi.π (fun l ↦ U (y l)) 0).le)
          · exact inf_le_right.trans ((Pi.π (fun l ↦ U (z l)) 0).le))
        have he := congrArg (fun x ↦ TopCat.Presheaf.cechComplexFunctorπ U P 1 t x) hd
        rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.cechComplexFunctor_d_π] at he
        simp only [AddCommGrpCat.sum_apply, map_zero] at he
        erw [Fin.sum_univ_two] at he
        simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
          neg_one_zsmul, ConcreteCategory.comp_apply] at he
        change P.map (Pi.lift fun l ↦ Pi.π (fun l ↦ U (t l))
            ((0 : Fin 2).succAbove l)).op
            (TopCat.Presheaf.cechComplexFunctorπ U P 0
              (t ∘ (0 : Fin 2).succAbove) (K.iCycles 0 c)) + -
          P.map (Pi.lift fun l ↦ Pi.π (fun l ↦ U (t l))
            ((1 : Fin 2).succAbove l)).op
            (TopCat.Presheaf.cechComplexFunctorπ U P 0
              (t ∘ (1 : Fin 2).succAbove) (K.iCycles 0 c)) = 0 at he
        have he' := eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using he)
        have hh := congrArg (P.map f.op) he'.symm
        have hr (j : Fin 2) (v : Fin 1 → ι) (hv : t ∘ j.succAbove = v)
            (g : V y ⊓ V z ⟶ V v) :
            P.map f.op (P.map (Pi.lift fun l ↦
              Pi.π (fun l ↦ U (t l)) (j.succAbove l)).op
                (sf (t ∘ j.succAbove))) = P.map g.op (sf v) := by
          cases hv
          rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
          congr 1
        change P.map f.op (P.map _ (sf (t ∘ (1 : Fin 2).succAbove))) =
          P.map f.op (P.map _ (sf (t ∘ (0 : Fin 2).succAbove))) at hh
        exact (hr 1 y h1 ((V y).infLELeft (V z))).symm.trans
          (hh.trans (hr 0 z h0 ((V y).infLERight (V z))))
      obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_gluing' F V ⊤
        (fun _ ↦ homOfLE le_top) hV sf hc
      refine ⟨s, hi ?_⟩
      rw [hbi]
      apply Concrete.limit_ext
      intro y
      change TopCat.Presheaf.cechComplexFunctorπ U P 0 y.as (a s) = sf y.as
      rw [← ConcreteCategory.comp_apply, hap]
      exact hs y.as
  have heq : e.f 0 = a := by
    apply Pi.hom_ext
    intro t
    exact (he t).trans (hap t).symm
  rw [CochainComplex.quasiIsoAt₀_iff]
  rw [ShortComplex.quasiIso_iff_of_zeros _ rfl rfl (K.shape _ _ (by simp))]
  change (ShortComplex.mk (e.f 0) (K.d 0 1) _).Exact ∧ Mono (e.f 0)
  simp only [heq]
  exact (CochainComplex.isIso_liftCycles_iff K a ha).mp hb


/-- Restriction from the terminal open object augments the pulled-back Čech
complex of a single injective étale sheaf by a quasi-isomorphism.

Source: Stacks Project, Tags 03AW and 03F6; the row calculation in
lem-sc-etale-open-cech-resolution-total, proof steps 1 and 2.
(blueprint: lem-sc-etale-open-cech-injective-augmentation)

Proof: The family of opens generates a covering sieve on top. Cover preservation
sends it to a covering sieve on i(top). Finite-limit preservation, and terminality
of i(top), identify i of every finite intersection with the fibre product of
the corresponding members over i(top). The unique projection-compatible product
isomorphisms commute with all Čech faces, hence identify the displayed complex
with the Čech complex of this image covering. Lift the index by ULift if the
large-index étale Čech interface requires it; reindexing products along the
canonical equivalence does not change the complex. The sheaf condition identifies
its zeroth homology with sections at i(top), through the restriction map fixed
by he. Injective Čech acyclicity gives zero homology in positive degrees. The
single-term source has the same zeroth homology and zero positive homology, so
e induces isomorphisms in every degree. For an empty covering, the sheaf condition
forces sections at i(top) to be zero and all the Čech terms are zero. This
argument uses no injective resolution or total complex. -/
theorem etaleOpenCechInjectiveAugmentation_quasiIso
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    (hc : CoverPreserving (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology i)
    [PreservesFiniteLimits i] (ht : IsTerminal (i.obj ⊤))
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (J : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective J]
    (e : (CochainComplex.single₀ AddCommGrpCat.{u + 1}).obj (J.obj.obj (op (i.obj ⊤))) ⟶
      (cechComplexFunctor U).obj (i.op ⋙ J.obj))
    (he : ∀ t : Fin 1 → ι,
      e.f 0 ≫ Pi.π (fun s : Fin 1 → ι ↦
        J.obj.obj (op (i.obj (∏ᶜ fun k ↦ U (s k))))) t =
          J.obj.map (i.map (homOfLE le_top)).op) : QuasiIso e := by
  have : RepresentablyFlat i := flat_of_preservesFiniteLimits i
  have : i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology :=
    Functor.isContinuous_iff_coverPreserving.mpr hc
  let F : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} :=
    ⟨i.op ⋙ J.obj, i.op_comp_isSheaf _ _ J⟩
  have hzero : QuasiIsoAt e 0 := openCechAugmentation_zero U hcover F e he
  let V : ULift.{u + 1} ι → X.Etale := fun t ↦ i.obj (U t.down)
  let f : ∀ t, V t ⟶ i.obj ⊤ := fun t ↦ i.map (homOfLE le_top)
  have hcov : Sieve.ofArrows V f ∈ X.smallEtaleTopology (i.obj ⊤) := by
    have hopen : Sieve.ofArrows U (fun _ ↦ homOfLE le_top) ∈
        Opens.grothendieckTopology X.carrier ⊤ := by
      intro x hx
      have hx' : x ∈ iSup U := by rw [hcover]; exact hx
      obtain ⟨t, hxt⟩ := Opens.mem_iSup.mp hx'
      exact ⟨U t, homOfLE le_top, Sieve.ofArrows_mk _ _ t, hxt⟩
    have himage := hc.cover_preserve hopen
    rw [Sieve.functorPushforward_ofArrows] at himage
    apply X.smallEtaleTopology.superset_covering _ himage
    intro W g hg
    obtain ⟨t, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
    exact (Sieve.mem_ofArrows_iff V f _).mpr ⟨ULift.up t, a, rfl⟩
  obtain ⟨c⟩ := etaleOpenCechProductComparison X i ht U J.obj
  refine ⟨fun p ↦ ?_⟩
  cases p with
  | zero => exact hzero
  | succ q =>
    rw [quasiIsoAt_iff_exactAt e (q + 1)
      (CochainComplex.exactAt_succ_single_obj _ q)]
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have hz := injective_sheaf_cech_acyclic X J (i.obj ⊤) (ULift.{u + 1} ι)
      V f hcov (q + 1) (Nat.succ_pos q)
    exact hz.of_iso (HomologicalComplex.homologyMapIso c (q + 1))

end AlgebraicGeometry.Scheme
