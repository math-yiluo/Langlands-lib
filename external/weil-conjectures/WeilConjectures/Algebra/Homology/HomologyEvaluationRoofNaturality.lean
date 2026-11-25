/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Naturality of cycle-compatible Hom evaluation -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory


section Evaluation
variable {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
  {R : Sheaf S CommRingCat.{u}}

set_option quotPrecheck false in
set_option hygiene false in
local notation "Mod" => SheafOfModules.{u}
  ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

open MonoidalCategory
@[instance_reducible]
private noncomputable def evaluationMonoidal : MonoidalCategory Mod :=
  SheafOfModules.monoidalCategory R
attribute [local instance] evaluationMonoidal

@[instance_reducible]
private noncomputable def evaluationSymmetric : SymmetricCategory Mod :=
  SheafOfModules.symmetricCategory R
attribute [local instance] evaluationSymmetric

@[instance_reducible]
private noncomputable def evaluationClosed : MonoidalClosed Mod :=
  SheafOfModules.monoidalClosed (R := R)
attribute [local instance] evaluationClosed

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
Adapted to a general small site from HomologyEvaluationCycleExistence.lean. -/
private lemma homMap_zero_left {A A' B B' : Mod} (g : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) (0 : A' ⟶ A) g = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver R.obj U.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj U.unop).map g.val = 0
  ext W x
  change ((g.val.app _).hom) ((φ.app W).hom (0)) = 0
  rw [map_zero, map_zero]

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
Adapted to a general small site from HomologyEvaluationCycleExistence.lean. -/
private lemma homMap_zero_right {A A' B B' : Mod} (f : A' ⟶ A) :
    SheafOfModules.homObjMap (R := R) f (0 : B ⟶ B') = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver R.obj U.unop).map f.val ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj U.unop).map 0 = 0
  ext W x
  rfl

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
Adapted to a general small site from HomologyEvaluationCycleExistence.lean. -/
private lemma tensorHomEquiv_zero (A B N : Mod) :
    SheafOfModules.tensorHomEquiv (R := R) A B N 0 = 0 := by
  have h := SheafOfModules.tensorHomEquiv_comp_homObjMap (R := R) A
    (0 : A ⊗ B ⟶ N) (0 : N ⟶ N)
  simpa only [comp_zero, homMap_zero_right] using h

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
Adapted to a general small site from HomologyEvaluationCycleExistence.lean. -/
private theorem homObj_cokernel_desc {A B B' Q N : Mod} (f : B' ⟶ B) (p : B ⟶ Q) (hp : f ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ p hp))
    (a : A ⟶ SheafOfModules.homObj (R := R) B N)
    (ha : a ≫ SheafOfModules.homObjMap (R := R) f (𝟙 N) = 0) :
    ∃ b : A ⟶ SheafOfModules.homObj (R := R) Q N,
      b ≫ SheafOfModules.homObjMap (R := R) p (𝟙 N) = a := by
  let F := tensorRight A
  have : F.PreservesZeroMorphisms := inferInstance
  have : PreservesColimitsOfSize.{0, 0} F := inferInstance
  let a' := (SheafOfModules.tensorHomEquiv (R := R) B A N).symm a
  have ha' : F.map f ≫ a' = 0 := by
    apply (SheafOfModules.tensorHomEquiv (R := R) B' A N).injective
    change SheafOfModules.tensorHomEquiv (R := R) B' A N
      (f ▷ A ≫ a') = _
    rw [SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := R) f a']
    simpa only [a', Equiv.apply_symm_apply, tensorHomEquiv_zero] using ha
  let hc' := CokernelCofork.mapIsColimit (CokernelCofork.ofπ p hp) hc F
  let b' : Q ⊗ A ⟶ N := hc'.desc (CokernelCofork.ofπ a' ha')
  have hb' : F.map p ≫ b' = a' := hc'.fac _ WalkingParallelPair.one
  refine ⟨SheafOfModules.tensorHomEquiv (R := R) Q A N b', ?_⟩
  calc
    _ = SheafOfModules.tensorHomEquiv (R := R) B A N (p ▷ A ≫ b') :=
      (SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := R) p b').symm
    _ = SheafOfModules.tensorHomEquiv (R := R) B A N a' := congrArg _ hb'
    _ = a := Equiv.apply_symm_apply _ a



/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
Adapted to a general small site from HomologyEvaluationCycleExistence.lean. -/
private theorem homMap_mono_right (A : Mod)
    {B B' : Mod} (f : B ⟶ B') [Mono f] :
    Mono (SheafOfModules.homObjMap (R := R) (𝟙 A) f) := by
  have : ((SheafOfModules.homFunctor R).obj (op A)).IsRightAdjoint :=
    (SheafOfModules.tensorHomAdjunction R A).isRightAdjoint
  exact inferInstanceAs (Mono (((SheafOfModules.homFunctor R).obj (op A)).map f))

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
Adapted to a general small site from HomologyEvaluationCycleExistence.lean. -/
private theorem homObj_liftCycles (K : CochainComplex Mod ℤ)
    (i : ℤ) {A B : Mod}
    (a : A ⟶ SheafOfModules.homObj (R := R) B (K.X i))
    (ha : a ≫ SheafOfModules.homObjMap (R := R) (𝟙 B) (K.d i (i + 1)) = 0) :
    ∃ b : A ⟶ SheafOfModules.homObj (R := R) B (K.cycles i),
      b ≫ SheafOfModules.homObjMap (R := R) (𝟙 B) (K.iCycles i) = a := by
  let a' := (SheafOfModules.tensorHomEquiv (R := R) B A (K.X i)).symm a
  have ha' : a' ≫ K.d i (i + 1) = 0 := by
    apply (SheafOfModules.tensorHomEquiv (R := R) B A (K.X (i + 1))).injective
    rw [SheafOfModules.tensorHomEquiv_comp_homObjMap (R := R) B a']
    simpa only [a', Equiv.apply_symm_apply, tensorHomEquiv_zero] using ha
  let b' := K.liftCycles a' (i + 1) (by simp) ha'
  refine ⟨SheafOfModules.tensorHomEquiv (R := R) B A (K.cycles i) b', ?_⟩
  calc
    _ = SheafOfModules.tensorHomEquiv (R := R) B A (K.X i)
        (b' ≫ K.iCycles i) :=
      (SheafOfModules.tensorHomEquiv_comp_homObjMap (R := R) B b' _).symm
    _ = a := by rw [HomologicalComplex.liftCycles_i]; exact Equiv.apply_symm_apply _ a

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
Adapted to a general small site from HomologyEvaluationCycleExistence.lean. -/
private theorem cyclePairing_lift (P T J : CochainComplex Mod ℤ)
    (π : ∀ (n p q : ℤ), p + n = q →
      (P.X n ⟶ SheafOfModules.homObj (R := R) (T.X p) (J.X q)))
    (hπ : ∀ (n m p q q' p' : ℤ), n + 1 = m →
      ∀ (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
      P.d n m ≫ π m p q hpq =
        π n p q' hq' ≫ SheafOfModules.homObjMap (R := R) (𝟙 (T.X p)) (J.d q' q) -
          n.negOnePow • (π n p' q hp' ≫
            SheafOfModules.homObjMap (R := R) (T.d p p') (𝟙 (J.X q))))
    (n : ℤ) :
    ∃ q : P.cycles n ⟶ SheafOfModules.homObj (R := R) (T.cycles (-n)) (J.cycles 0),
      q ≫ SheafOfModules.homObjMap (R := R) (𝟙 (T.cycles (-n))) (J.iCycles 0) =
        P.iCycles n ≫ π n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := R) (T.iCycles (-n)) (𝟙 (J.X 0)) := by
  let a := P.iCycles n ≫ π n (-n) 0 (by omega) ≫
    SheafOfModules.homObjMap (R := R) (T.iCycles (-n)) (𝟙 (J.X 0))
  apply homObj_liftCycles J 0 a
  have hd : (0 : P.cycles n ⟶ SheafOfModules.homObj (R := R)
      (T.X (-n)) (J.X 1)) =
      P.iCycles n ≫ (π n (-n) 0 (by omega) ≫
        SheafOfModules.homObjMap (R := R) (𝟙 (T.X (-n))) (J.d 0 1) -
        n.negOnePow • (π n (1 - n) 1 (by omega) ≫
          SheafOfModules.homObjMap (R := R) (T.d (-n) (1 - n)) (𝟙 (J.X 1)))) := by
    calc
      0 = P.iCycles n ≫ P.d n (n + 1) ≫
          π (n + 1) (-n) 1 (by omega) := by
        rw [← Category.assoc, P.iCycles_d, zero_comp]
      _ = _ := congrArg (fun f ↦ P.iCycles n ≫ f)
        (hπ n (n + 1) (-n) 1 0 (1 - n) (by omega)
          (by omega) (by omega) (by omega))
  have h := congrArg (fun f ↦ f ≫ SheafOfModules.homObjMap (R := R)
    (T.iCycles (-n)) (𝟙 (J.X 1))) hd
  simp only [zero_comp, Preadditive.comp_sub, Linear.comp_units_smul,
    Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc,
    SheafOfModules.homObjMap_comp_homObjMap, Category.comp_id,
    HomologicalComplex.iCycles_d, homMap_zero_left, comp_zero, smul_zero, sub_zero] at h
  change a ≫ SheafOfModules.homObjMap (R := R)
    (𝟙 (T.cycles (-n))) (J.d 0 1) = 0
  dsimp only [a]
  rw [Category.assoc, Category.assoc,
    SheafOfModules.homObjMap_comp_homObjMap (R := R)]
  simpa only [Category.id_comp] using h.symm

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
Adapted to a general small site from HomologyEvaluationCycleExistence.lean. -/
private theorem cyclePairing_boundary_left (P T J : CochainComplex Mod ℤ)
    (π : ∀ (n p q : ℤ), p + n = q →
      (P.X n ⟶ SheafOfModules.homObj (R := R) (T.X p) (J.X q)))
    (hπ : ∀ (n m p q q' p' : ℤ), n + 1 = m →
      ∀ (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
      P.d n m ≫ π m p q hpq =
        π n p q' hq' ≫ SheafOfModules.homObjMap (R := R) (𝟙 (T.X p)) (J.d q' q) -
          n.negOnePow • (π n p' q hp' ≫
            SheafOfModules.homObjMap (R := R) (T.d p p') (𝟙 (J.X q))))
    (n : ℤ) :
    ∀ (q : P.cycles n ⟶
        SheafOfModules.homObj (R := R) (T.cycles (-n)) (J.cycles 0)),
      q ≫ SheafOfModules.homObjMap (R := R) (𝟙 (T.cycles (-n))) (J.iCycles 0) =
        P.iCycles n ≫ π n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := R) (T.iCycles (-n)) (𝟙 (J.X 0)) →
      P.toCycles (n - 1) n ≫ q ≫
        SheafOfModules.homObjMap (R := R)
          (𝟙 (T.cycles (-n))) (J.homologyπ 0) = 0 := by
  intro q hq
  let δ := π (n - 1) (-n) (-1) (by omega) ≫
    SheafOfModules.homObjMap (R := R) (T.iCycles (-n)) (𝟙 (J.X (-1)))
  have hm := homMap_mono_right (T.cycles (-n)) (J.iCycles 0)
  have hqP : P.toCycles (n - 1) n ≫ q = δ ≫
      SheafOfModules.homObjMap (R := R)
        (𝟙 (T.cycles (-n))) (J.toCycles (-1) 0) := by
    apply (cancel_mono (SheafOfModules.homObjMap (R := R)
      (𝟙 (T.cycles (-n))) (J.iCycles 0))).1
    rw [Category.assoc, hq]
    have hd := hπ (n - 1) n (-n) 0 (-1) (1 - n) (by omega)
      (by omega) (by omega) (by omega)
    change P.d (n - 1) n ≫ π n (-n) 0 (by omega) = _ at hd
    dsimp only [δ]
    simp only [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
      Category.id_comp, HomologicalComplex.toCycles_i]
    rw [← Category.assoc, ← Category.assoc, P.toCycles_i, hd]
    simp only [Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc,
      SheafOfModules.homObjMap_comp_homObjMap, Category.comp_id,
      HomologicalComplex.iCycles_d, homMap_zero_left, comp_zero, smul_zero, sub_zero]
  rw [← Category.assoc, hqP, Category.assoc,
    SheafOfModules.homObjMap_comp_homObjMap (R := R),
    J.toCycles_comp_homologyπ, homMap_zero_right, comp_zero]

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
Adapted to a general small site from HomologyEvaluationCycleExistence.lean. -/
private lemma homMap_swap {A A' B B' : Mod}
    (f : A' ⟶ A) (g : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) f (𝟙 B) ≫
        SheafOfModules.homObjMap (R := R) (𝟙 A') g =
      SheafOfModules.homObjMap (R := R) (𝟙 A) g ≫
        SheafOfModules.homObjMap (R := R) f (𝟙 B') := by
  simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
Adapted to a general small site from HomologyEvaluationCycleExistence.lean. -/
private theorem cyclePairing_boundary_right (P T J : CochainComplex Mod ℤ)
    (π : ∀ (n p q : ℤ), p + n = q →
      (P.X n ⟶ SheafOfModules.homObj (R := R) (T.X p) (J.X q)))
    (hπ : ∀ (n m p q q' p' : ℤ), n + 1 = m →
      ∀ (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
      P.d n m ≫ π m p q hpq =
        π n p q' hq' ≫ SheafOfModules.homObjMap (R := R) (𝟙 (T.X p)) (J.d q' q) -
          n.negOnePow • (π n p' q hp' ≫
            SheafOfModules.homObjMap (R := R) (T.d p p') (𝟙 (J.X q))))
    (n : ℤ) :
    ∀ (q : P.cycles n ⟶
        SheafOfModules.homObj (R := R) (T.cycles (-n)) (J.cycles 0)),
      q ≫ SheafOfModules.homObjMap (R := R) (𝟙 (T.cycles (-n))) (J.iCycles 0) =
        P.iCycles n ≫ π n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := R) (T.iCycles (-n)) (𝟙 (J.X 0)) →
      (q ≫ SheafOfModules.homObjMap (R := R)
        (𝟙 (T.cycles (-n))) (J.homologyπ 0)) ≫
        SheafOfModules.homObjMap (R := R)
          (T.toCycles (-n - 1) (-n)) (𝟙 (J.homology 0)) = 0 := by
  intro q hq
  let δ := P.iCycles n ≫ π n (-n - 1) (-1) (by omega)
  let κ := P.iCycles n ≫ π n (-n) 0 (by omega) ≫
    SheafOfModules.homObjMap (R := R) (T.d (-n - 1) (-n)) (𝟙 (J.X 0))
  have hd : δ ≫ SheafOfModules.homObjMap (R := R)
      (𝟙 (T.X (-n - 1))) (J.d (-1) 0) = n.negOnePow • κ := by
    apply sub_eq_zero.mp
    have hh := congrArg (fun f ↦ P.iCycles n ≫ f)
      (hπ n (n + 1) (-n - 1) 0 (-1) (-n) (by omega)
        (by omega) (by omega) (by omega))
    change (P.iCycles n ≫ (P.d n (n + 1) ≫ _)) = _ at hh
    simpa only [δ, κ, ← Category.assoc, P.iCycles_d, zero_comp,
      Preadditive.comp_sub, Linear.comp_units_smul] using hh.symm
  have hk : κ = n.negOnePow • (δ ≫ SheafOfModules.homObjMap (R := R)
      (𝟙 (T.X (-n - 1))) (J.d (-1) 0)) := by
    rw [hd, smul_smul, Int.units_mul_self, one_smul]
  have hm := homMap_mono_right (T.X (-n - 1)) (J.iCycles 0)
  have hqT : q ≫ SheafOfModules.homObjMap (R := R)
      (T.toCycles (-n - 1) (-n)) (𝟙 (J.cycles 0)) =
      n.negOnePow • (δ ≫ SheafOfModules.homObjMap (R := R)
        (𝟙 (T.X (-n - 1))) (J.toCycles (-1) 0)) := by
    apply (cancel_mono (SheafOfModules.homObjMap (R := R)
      (𝟙 (T.X (-n - 1))) (J.iCycles 0))).1
    rw [Category.assoc, homMap_swap, ← Category.assoc, hq]
    dsimp only [κ] at hk
    simpa only [Linear.units_smul_comp, Category.assoc,
      SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp, Category.comp_id,
      HomologicalComplex.toCycles_i] using hk
  rw [Category.assoc, ← homMap_swap, ← Category.assoc, hqT,
    Linear.units_smul_comp, Category.assoc,
    SheafOfModules.homObjMap_comp_homObjMap (R := R),
    J.toCycles_comp_homologyπ, homMap_zero_right, comp_zero, smul_zero]


/-- The two homology cokernels give the evaluation map and its cycle lift.
Source: Stacks Project, Tag 0A8X and tensor-Hom adjunction Tag 03EO. -/
private theorem cyclePairing_descend (P T J : CochainComplex Mod ℤ)
    (π : ∀ (n p q : ℤ), p + n = q →
      (P.X n ⟶ SheafOfModules.homObj (R := R) (T.X p) (J.X q)))
    (hπ : ∀ (n m p q q' p' : ℤ), n + 1 = m →
      ∀ (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
      P.d n m ≫ π m p q hpq =
        π n p q' hq' ≫ SheafOfModules.homObjMap (R := R) (𝟙 (T.X p)) (J.d q' q) -
          n.negOnePow • (π n p' q hp' ≫
            SheafOfModules.homObjMap (R := R) (T.d p p') (𝟙 (J.X q))))
    (n : ℤ) :
    ∃ (e : P.homology n ⟶
        SheafOfModules.homObj (R := R) (T.homology (-n)) (J.homology 0))
      (q : P.cycles n ⟶
        SheafOfModules.homObj (R := R) (T.cycles (-n)) (J.cycles 0)),
      q ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (J.iCycles 0) =
        P.iCycles n ≫ π n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := R) (T.iCycles (-n)) (𝟙 _) ∧
      q ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (J.homologyπ 0) =
        P.homologyπ n ≫ e ≫
          SheafOfModules.homObjMap (R := R) (T.homologyπ (-n)) (𝟙 _) := by
  obtain ⟨q, hq⟩ := cyclePairing_lift P T J π hπ n
  let a := q ≫ SheafOfModules.homObjMap (R := R)
    (𝟙 (T.cycles (-n))) (J.homologyπ 0)
  have haP : P.toCycles (n - 1) n ≫ a = 0 :=
    cyclePairing_boundary_left P T J π hπ n q hq
  have haT : a ≫ SheafOfModules.homObjMap (R := R)
      (T.toCycles (-n - 1) (-n)) (𝟙 (J.homology 0)) = 0 :=
    cyclePairing_boundary_right P T J π hπ n q hq
  let hc := P.homologyIsCokernel (n - 1) n (by simp)
  let b := hc.desc (CokernelCofork.ofπ a haP)
  have hb : P.homologyπ n ≫ b = a := hc.fac _ WalkingParallelPair.one
  have hbT : b ≫ SheafOfModules.homObjMap (R := R)
      (T.toCycles (-n - 1) (-n)) (𝟙 (J.homology 0)) = 0 := by
    apply (cancel_epi (P.homologyπ n)).1
    rw [← Category.assoc, hb, comp_zero]
    exact haT
  obtain ⟨e, he⟩ := homObj_cokernel_desc
    (T.toCycles (-n - 1) (-n)) (T.homologyπ (-n))
    (T.toCycles_comp_homologyπ (-n - 1) (-n))
    (T.homologyIsCokernel (-n - 1) (-n) (by simp)) b hbT
  refine ⟨e, q, hq, ?_⟩
  dsimp only [a] at hb
  rw [he, hb]

/-- Precomposition by an epimorphism is a monomorphism on internal Hom.
Source: Stacks Project, Tag 03EO; tensoring preserves epimorphisms. -/
private theorem homMap_mono_left {B B' N : Mod} (p : B' ⟶ B) [Epi p] :
    Mono (SheafOfModules.homObjMap (R := R) p (𝟙 N)) := by
  constructor
  intro A f g h
  let e := SheafOfModules.tensorHomEquiv (R := R) B A N
  let e' := SheafOfModules.tensorHomEquiv (R := R) B' A N
  have : Epi ((tensorRight A).map p) := inferInstance
  apply e.symm.injective
  apply (cancel_epi ((tensorRight A).map p)).mp
  apply e'.injective
  change e' (p ▷ A ≫ e.symm f) = e' (p ▷ A ≫ e.symm g)
  simpa only [e, e', SheafOfModules.tensorHomEquiv_whiskerRight_comp,
    Equiv.apply_symm_apply] using h


/-- The cycle factorization identities imply naturality on homology.
Source: Stacks Project, Tag 0A8X, precomposition of Hom complexes. -/
private theorem cyclePairing_naturality
    (P Z B L K : CochainComplex Mod ℤ) (n : ℤ) (t : P ⟶ Z) (q : L ⟶ B)
    (πB : P.X n ⟶ SheafOfModules.homObj (R := R) (B.X (-n)) (K.X 0))
    (πL : Z.X n ⟶ SheafOfModules.homObj (R := R) (L.X (-n)) (K.X 0))
    (hπ : t.f n ≫ πL = πB ≫ SheafOfModules.homObjMap (R := R) (q.f (-n)) (𝟙 _))
    (g : P.homology n ⟶
      SheafOfModules.homObj (R := R) (B.homology (-n)) (K.homology 0))
    (d : P.cycles n ⟶
      SheafOfModules.homObj (R := R) (B.cycles (-n)) (K.cycles 0))
    (h : Z.homology n ⟶
      SheafOfModules.homObj (R := R) (L.homology (-n)) (K.homology 0))
    (k : Z.cycles n ⟶
      SheafOfModules.homObj (R := R) (L.cycles (-n)) (K.cycles 0))
    (hd : d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
      P.iCycles n ≫ πB ≫
        SheafOfModules.homObjMap (R := R) (B.iCycles (-n)) (𝟙 _))
    (hg : d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
      P.homologyπ n ≫ g ≫
        SheafOfModules.homObjMap (R := R) (B.homologyπ (-n)) (𝟙 _))
    (hk : k ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
      Z.iCycles n ≫ πL ≫
        SheafOfModules.homObjMap (R := R) (L.iCycles (-n)) (𝟙 _))
    (hh : k ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
      Z.homologyπ n ≫ h ≫
        SheafOfModules.homObjMap (R := R) (L.homologyπ (-n)) (𝟙 _)) :
    g ≫ SheafOfModules.homObjMap (R := R)
        (HomologicalComplex.homologyMap q (-n)) (𝟙 _) =
      HomologicalComplex.homologyMap t n ≫ h := by
  have hm := homMap_mono_right (L.cycles (-n)) (K.iCycles 0)
  have hcycles : d ≫ SheafOfModules.homObjMap (R := R)
      (HomologicalComplex.cyclesMap q (-n)) (𝟙 _) =
      HomologicalComplex.cyclesMap t n ≫ k := by
    apply (cancel_mono (SheafOfModules.homObjMap (R := R)
      (𝟙 (L.cycles (-n))) (K.iCycles 0))).mp
    rw [Category.assoc, homMap_swap, ← Category.assoc, hd]
    simp only [Category.assoc]
    rw [hk]
    simp only [SheafOfModules.homObjMap_comp_homObjMap,
      Category.comp_id, HomologicalComplex.cyclesMap_i]
    rw [HomologicalComplex.cyclesMap_i_assoc, ← Category.assoc (t.f n), hπ]
    simp only [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
      Category.comp_id]
  have hm' := homMap_mono_left (R := R)
    (N := K.homology 0) (L.homologyπ (-n))
  apply (cancel_epi (P.homologyπ n)).mp
  apply (cancel_mono (SheafOfModules.homObjMap (R := R)
    (L.homologyπ (-n)) (𝟙 (K.homology 0)))).mp
  simp only [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp]
  rw [HomologicalComplex.homologyπ_naturality]
  have hmap := SheafOfModules.homObjMap_comp_homObjMap (R := R)
    (B.homologyπ (-n)) (HomologicalComplex.cyclesMap q (-n))
    (𝟙 (K.homology 0)) (𝟙 (K.homology 0))
  simp only [Category.id_comp] at hmap
  rw [← hmap]
  rw [← Category.assoc (g), ← Category.assoc (P.homologyπ n), ← hg]
  rw [Category.assoc, ← homMap_swap, ← Category.assoc, hcycles]
  rw [Category.assoc, hh, ← HomologicalComplex.homologyπ_naturality_assoc]

end Evaluation

/-- Two cycle-compatible evaluations agree after passage through a common source.

Source: Stacks Project, Tag 0A8X, product projections and the Hom differential.
(blueprint: new-e3-homology-evaluation-roof-naturality).

The projection family is assumed to obey the Hom differential and naturality
identities, as supplied by `homComplex_projections_exists`.

Proof: Denote the homology precomposition maps induced by q and p by Q and P.
First descend the evaluation pairing for Hom(L,K): on Hom cycles and L cycles,
the Hom differential makes the value a K cycle. Evaluating a Hom boundary on a
cycle or a Hom cycle on an L boundary gives a K boundary (with the usual integer
sign). Thus the pairing descends through both homology quotients to an evaluation
h for L. This is a proof construction using kernels and cokernels, not a choice
of arbitrary comparison isomorphisms. Naturality of the supplied product projections
under precomposition shows that evaluation on q(z) equals evaluation of the
precomposed Hom cycle on z, and likewise for p. The two identities for d identify
g on cycle classes with this pairing, giving g followed by Hom(H(q),1) = Q
followed by h. The two identities for c similarly give f followed by
Hom(H(p),1) = P followed by h. To check these equalities, cancel the epimorphism
from Hom cycles to homology and internal-Hom precomposition by the source
homology projection. The latter is monic: uncurry using the tensor-Hom adjunction
and cancel the epimorphism obtained by tensoring that projection. Since P is
invertible, the second equation gives h = P inverse followed by f followed by
Hom(H(p),1). Substitute in the first equation. No quasi-isomorphism of q or p,
K-injectivity, or scheme is needed beyond the explicitly assumed invertibility
of P. The argument includes zero homology, zero complexes and empty sites. -/
theorem homologyEvaluation_roof_naturality
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    {R : Sheaf S CommRingCat.{u}}
    (A E L K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (π : ∀ (B M : CochainComplex (SheafOfModules.{u}
        ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (n a b : ℤ), a + n = b →
        ((homComplex (R := R) B M).X n ⟶
          SheafOfModules.homObj (R := R) (B.X a) (M.X b)))
    (hπdiff : ∀ (B M : CochainComplex (SheafOfModules.{u}
        ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (n m a b b' a' : ℤ) (_hnm : n + 1 = m)
      (hab : a + m = b) (hb' : a + n = b') (ha' : a' + n = b),
      (homComplex (R := R) B M).d n m ≫ π B M m a b hab =
        π B M n a b' hb' ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (M.d b' b) -
          n.negOnePow • (π B M n a' b ha' ≫
            SheafOfModules.homObjMap (R := R) (B.d a a') (𝟙 _)))
    (hπnat : ∀ (B B' M M' : CochainComplex (SheafOfModules.{u}
        ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (t : B' ⟶ B) (s : M ⟶ M') (n a b : ℤ) (hab : a + n = b),
      ((((homComplexFunctor (R := R)).map t.op).app M) ≫
          ((homComplexFunctor (R := R)).obj (op B')).map s).f n ≫ π B' M' n a b hab =
        π B M n a b hab ≫ SheafOfModules.homObjMap (R := R) (t.f a) (s.f b))
    (n : ℤ) (q : L ⟶ A) (p : L ⟶ E)
    [IsIso (HomologicalComplex.homologyMap
      (((homComplexFunctor (R := R)).map p.op).app K) n)] :
    let Q := homComplex (R := R) A K
    let P := homComplex (R := R) E K
    ∀ (g : Q.homology n ⟶ SheafOfModules.homObj (R := R)
        (A.homology (-n)) (K.homology 0))
      (d : Q.cycles n ⟶ SheafOfModules.homObj (R := R) (A.cycles (-n)) (K.cycles 0))
      (f : P.homology n ⟶ SheafOfModules.homObj (R := R)
        (E.homology (-n)) (K.homology 0))
      (c : P.cycles n ⟶ SheafOfModules.homObj (R := R) (E.cycles (-n)) (K.cycles 0)),
      d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
        Q.iCycles n ≫ π A K n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := R) (A.iCycles (-n)) (𝟙 _) →
      d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
        Q.homologyπ n ≫ g ≫
          SheafOfModules.homObjMap (R := R) (A.homologyπ (-n)) (𝟙 _) →
      c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
        P.iCycles n ≫ π E K n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := R) (E.iCycles (-n)) (𝟙 _) →
      c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
        P.homologyπ n ≫ f ≫
          SheafOfModules.homObjMap (R := R) (E.homologyπ (-n)) (𝟙 _) →
      g ≫ SheafOfModules.homObjMap (R := R)
          (HomologicalComplex.homologyMap q (-n)) (𝟙 _) =
        HomologicalComplex.homologyMap
            (((homComplexFunctor (R := R)).map q.op).app K) n ≫
          inv (HomologicalComplex.homologyMap
            (((homComplexFunctor (R := R)).map p.op).app K) n) ≫
          f ≫ SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.homologyMap p (-n)) (𝟙 _) := by
  dsimp only
  intro g d f c hd hg hc hf
  obtain ⟨h, k, hk, hh⟩ := cyclePairing_descend
    (homComplex (R := R) L K) L K (π L K) (hπdiff L K) n
  have hnat (B : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (t : L ⟶ B) :
      (((homComplexFunctor (R := R)).map t.op).app K).f n ≫
        π L K n (-n) 0 (by omega) =
      π B K n (-n) 0 (by omega) ≫
        SheafOfModules.homObjMap (R := R) (t.f (-n)) (𝟙 _) := by
    simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] using
      hπnat B L K K t (𝟙 K) n (-n) 0 (by omega)
  have hg' := cyclePairing_naturality
    (homComplex (R := R) A K) (homComplex (R := R) L K) A L K n
    (((homComplexFunctor (R := R)).map q.op).app K) q
    (π A K n (-n) 0 (by omega)) (π L K n (-n) 0 (by omega))
    (hnat A q) g d h k hd hg hk hh
  have hf' := cyclePairing_naturality
    (homComplex (R := R) E K) (homComplex (R := R) L K) E L K n
    (((homComplexFunctor (R := R)).map p.op).app K) p
    (π E K n (-n) 0 (by omega)) (π L K n (-n) 0 (by omega))
    (hnat E p) f c h k hc hf hk hh
  rw [hg', hf']
  simp only [IsIso.inv_hom_id_assoc]

end CategoryTheory
