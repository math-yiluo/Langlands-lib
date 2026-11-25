/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # A step in the construction of homology evaluation -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

open MonoidalCategory
@[instance_reducible]
private noncomputable def evaluationMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

attribute [local instance] evaluationMonoidal

@[instance_reducible]
private noncomputable def evaluationSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  SheafOfModules.symmetricCategory X.sheaf

attribute [local instance] evaluationSymmetric

@[instance_reducible]
private noncomputable def evaluationClosed (X : Scheme.{u}) : MonoidalClosed X.Modules :=
  SheafOfModules.monoidalClosed (R := X.sheaf)

attribute [local instance] evaluationClosed

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-b2-homology-evaluation-cycle-existence). -/
private lemma homMap_zero_left (X : Scheme.{u}) {A A' B B' : X.Modules} (g : B ⟶ B') :
    SheafOfModules.homObjMap (R := X.sheaf) (0 : A' ⟶ A) g = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver X.sheaf.obj U.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver X.sheaf.obj U.unop).map g.val = 0
  ext W x
  change ((g.val.app _).hom) ((φ.app W).hom (0)) = 0
  rw [map_zero, map_zero]

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-b2-homology-evaluation-cycle-existence). -/
private lemma homMap_zero_right (X : Scheme.{u}) {A A' B B' : X.Modules} (f : A' ⟶ A) :
    SheafOfModules.homObjMap (R := X.sheaf) f (0 : B ⟶ B') = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver X.sheaf.obj U.unop).map f.val ≫ φ ≫
    (PresheafOfModules.restrictOver X.sheaf.obj U.unop).map 0 = 0
  ext W x
  rfl

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-b2-homology-evaluation-cycle-existence). -/
private lemma tensorHomEquiv_zero (X : Scheme.{u}) (A B N : X.Modules) :
    SheafOfModules.tensorHomEquiv (R := X.sheaf) A B N 0 = 0 := by
  have h := SheafOfModules.tensorHomEquiv_comp_homObjMap (R := X.sheaf) A
    (0 : A ⊗ B ⟶ N) (0 : N ⟶ N)
  simpa only [comp_zero, homMap_zero_right] using h

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-b2-homology-evaluation-cycle-existence). -/
private theorem homObj_cokernel_desc (X : Scheme.{u})
    {A B B' Q N : X.Modules} (f : B' ⟶ B) (p : B ⟶ Q) (hp : f ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ p hp))
    (a : A ⟶ SheafOfModules.homObj (R := X.sheaf) B N)
    (ha : a ≫ SheafOfModules.homObjMap (R := X.sheaf) f (𝟙 N) = 0) :
    ∃ b : A ⟶ SheafOfModules.homObj (R := X.sheaf) Q N,
      b ≫ SheafOfModules.homObjMap (R := X.sheaf) p (𝟙 N) = a := by
  let F := tensorRight A
  have : F.PreservesZeroMorphisms := inferInstance
  have : PreservesColimitsOfSize.{0, 0} F := inferInstance
  let a' := (SheafOfModules.tensorHomEquiv (R := X.sheaf) B A N).symm a
  have ha' : F.map f ≫ a' = 0 := by
    apply (SheafOfModules.tensorHomEquiv (R := X.sheaf) B' A N).injective
    change SheafOfModules.tensorHomEquiv (R := X.sheaf) B' A N
      (f ▷ A ≫ a') = _
    rw [SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := X.sheaf) f a']
    simpa only [a', Equiv.apply_symm_apply, tensorHomEquiv_zero] using ha
  let hc' := CokernelCofork.mapIsColimit (CokernelCofork.ofπ p hp) hc F
  let b' : Q ⊗ A ⟶ N := hc'.desc (CokernelCofork.ofπ a' ha')
  have hb' : F.map p ≫ b' = a' := hc'.fac _ WalkingParallelPair.one
  refine ⟨SheafOfModules.tensorHomEquiv (R := X.sheaf) Q A N b', ?_⟩
  calc
    _ = SheafOfModules.tensorHomEquiv (R := X.sheaf) B A N (p ▷ A ≫ b') :=
      (SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := X.sheaf) p b').symm
    _ = SheafOfModules.tensorHomEquiv (R := X.sheaf) B A N a' := congrArg _ hb'
    _ = a := Equiv.apply_symm_apply _ a



/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-b2-homology-evaluation-cycle-existence). -/
private theorem homMap_mono_right (X : Scheme.{u}) (A : X.Modules)
    {B B' : X.Modules} (f : B ⟶ B') [Mono f] :
    Mono (SheafOfModules.homObjMap (R := X.sheaf) (𝟙 A) f) := by
  have : ((SheafOfModules.homFunctor X.sheaf).obj (op A)).IsRightAdjoint :=
    (SheafOfModules.tensorHomAdjunction X.sheaf A).isRightAdjoint
  exact inferInstanceAs (Mono (((SheafOfModules.homFunctor X.sheaf).obj (op A)).map f))

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-b2-homology-evaluation-cycle-existence). -/
private theorem homObj_liftCycles (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (i : ℤ) {A B : X.Modules}
    (a : A ⟶ SheafOfModules.homObj (R := X.sheaf) B (K.X i))
    (ha : a ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 B) (K.d i (i + 1)) = 0) :
    ∃ b : A ⟶ SheafOfModules.homObj (R := X.sheaf) B (K.cycles i),
      b ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 B) (K.iCycles i) = a := by
  let a' := (SheafOfModules.tensorHomEquiv (R := X.sheaf) B A (K.X i)).symm a
  have ha' : a' ≫ K.d i (i + 1) = 0 := by
    apply (SheafOfModules.tensorHomEquiv (R := X.sheaf) B A (K.X (i + 1))).injective
    rw [SheafOfModules.tensorHomEquiv_comp_homObjMap (R := X.sheaf) B a']
    simpa only [a', Equiv.apply_symm_apply, tensorHomEquiv_zero] using ha
  let b' := K.liftCycles a' (i + 1) (by simp) ha'
  refine ⟨SheafOfModules.tensorHomEquiv (R := X.sheaf) B A (K.cycles i) b', ?_⟩
  calc
    _ = SheafOfModules.tensorHomEquiv (R := X.sheaf) B A (K.X i)
        (b' ≫ K.iCycles i) :=
      (SheafOfModules.tensorHomEquiv_comp_homObjMap (R := X.sheaf) B b' _).symm
    _ = a := by rw [HomologicalComplex.liftCycles_i]; exact Equiv.apply_symm_apply _ a

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-b2-homology-evaluation-cycle-existence). -/
private theorem cyclePairing_lift (X : Scheme.{u}) (P T J : CochainComplex X.Modules ℤ)
    (π : ∀ (n p q : ℤ), p + n = q →
      (P.X n ⟶ SheafOfModules.homObj (R := X.sheaf) (T.X p) (J.X q)))
    (hπ : ∀ (n m p q q' p' : ℤ), n + 1 = m →
      ∀ (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
      P.d n m ≫ π m p q hpq =
        π n p q' hq' ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 (T.X p)) (J.d q' q) -
          n.negOnePow • (π n p' q hp' ≫
            SheafOfModules.homObjMap (R := X.sheaf) (T.d p p') (𝟙 (J.X q))))
    (n : ℤ) :
    ∃ q : P.cycles n ⟶ SheafOfModules.homObj (R := X.sheaf) (T.cycles (-n)) (J.cycles 0),
      q ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 (T.cycles (-n))) (J.iCycles 0) =
        P.iCycles n ≫ π n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := X.sheaf) (T.iCycles (-n)) (𝟙 (J.X 0)) := by
  let a := P.iCycles n ≫ π n (-n) 0 (by omega) ≫
    SheafOfModules.homObjMap (R := X.sheaf) (T.iCycles (-n)) (𝟙 (J.X 0))
  apply homObj_liftCycles X J 0 a
  have hd : (0 : P.cycles n ⟶ SheafOfModules.homObj (R := X.sheaf)
      (T.X (-n)) (J.X 1)) =
      P.iCycles n ≫ (π n (-n) 0 (by omega) ≫
        SheafOfModules.homObjMap (R := X.sheaf) (𝟙 (T.X (-n))) (J.d 0 1) -
        n.negOnePow • (π n (1 - n) 1 (by omega) ≫
          SheafOfModules.homObjMap (R := X.sheaf) (T.d (-n) (1 - n)) (𝟙 (J.X 1)))) := by
    calc
      0 = P.iCycles n ≫ P.d n (n + 1) ≫
          π (n + 1) (-n) 1 (by omega) := by
        rw [← Category.assoc, P.iCycles_d, zero_comp]
      _ = _ := congrArg (fun f => P.iCycles n ≫ f)
        (hπ n (n + 1) (-n) 1 0 (1 - n) (by omega)
          (by omega) (by omega) (by omega))
  have h := congrArg (fun f => f ≫ SheafOfModules.homObjMap (R := X.sheaf)
    (T.iCycles (-n)) (𝟙 (J.X 1))) hd
  simp only [zero_comp, Preadditive.comp_sub, Linear.comp_units_smul,
    Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc,
    SheafOfModules.homObjMap_comp_homObjMap, Category.comp_id,
    HomologicalComplex.iCycles_d, homMap_zero_left, comp_zero, smul_zero, sub_zero] at h
  change a ≫ SheafOfModules.homObjMap (R := X.sheaf)
    (𝟙 (T.cycles (-n))) (J.d 0 1) = 0
  dsimp only [a]
  rw [Category.assoc, Category.assoc,
    SheafOfModules.homObjMap_comp_homObjMap (R := X.sheaf)]
  simpa only [Category.id_comp] using h.symm

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-b2-homology-evaluation-cycle-existence). -/
private theorem cyclePairing_boundary_left (X : Scheme.{u}) (P T J : CochainComplex X.Modules ℤ)
    (π : ∀ (n p q : ℤ), p + n = q →
      (P.X n ⟶ SheafOfModules.homObj (R := X.sheaf) (T.X p) (J.X q)))
    (hπ : ∀ (n m p q q' p' : ℤ), n + 1 = m →
      ∀ (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
      P.d n m ≫ π m p q hpq =
        π n p q' hq' ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 (T.X p)) (J.d q' q) -
          n.negOnePow • (π n p' q hp' ≫
            SheafOfModules.homObjMap (R := X.sheaf) (T.d p p') (𝟙 (J.X q))))
    (n : ℤ) :
    ∀ (q : P.cycles n ⟶
        SheafOfModules.homObj (R := X.sheaf) (T.cycles (-n)) (J.cycles 0)),
      q ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 (T.cycles (-n))) (J.iCycles 0) =
        P.iCycles n ≫ π n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := X.sheaf) (T.iCycles (-n)) (𝟙 (J.X 0)) →
      P.toCycles (n - 1) n ≫ q ≫
        SheafOfModules.homObjMap (R := X.sheaf)
          (𝟙 (T.cycles (-n))) (J.homologyπ 0) = 0 := by
  intro q hq
  let δ := π (n - 1) (-n) (-1) (by omega) ≫
    SheafOfModules.homObjMap (R := X.sheaf) (T.iCycles (-n)) (𝟙 (J.X (-1)))
  have hm := homMap_mono_right X (T.cycles (-n)) (J.iCycles 0)
  have hqP : P.toCycles (n - 1) n ≫ q = δ ≫
      SheafOfModules.homObjMap (R := X.sheaf)
        (𝟙 (T.cycles (-n))) (J.toCycles (-1) 0) := by
    apply (cancel_mono (SheafOfModules.homObjMap (R := X.sheaf)
      (𝟙 (T.cycles (-n))) (J.iCycles 0))).1
    rw [Category.assoc, hq]
    have hd := hπ (n - 1) n (-n) 0 (-1) (1 - n) (by omega)
      (by omega) (by omega) (by omega)
    change P.d (n - 1) n ≫ π n (-n) 0 (by omega) = _ at hd
    dsimp only [δ]
    simp only [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
      Category.id_comp, Category.comp_id, HomologicalComplex.toCycles_i]
    rw [← Category.assoc, ← Category.assoc, P.toCycles_i, hd]
    simp only [Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc,
      SheafOfModules.homObjMap_comp_homObjMap, Category.comp_id,
      HomologicalComplex.iCycles_d, homMap_zero_left, comp_zero, smul_zero, sub_zero]
  rw [← Category.assoc, hqP, Category.assoc,
    SheafOfModules.homObjMap_comp_homObjMap (R := X.sheaf),
    J.toCycles_comp_homologyπ, homMap_zero_right, comp_zero]

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-b2-homology-evaluation-cycle-existence). -/
private lemma homMap_swap (X : Scheme.{u}) {A A' B B' : X.Modules}
    (f : A' ⟶ A) (g : B ⟶ B') :
    SheafOfModules.homObjMap (R := X.sheaf) f (𝟙 B) ≫
        SheafOfModules.homObjMap (R := X.sheaf) (𝟙 A') g =
      SheafOfModules.homObjMap (R := X.sheaf) (𝟙 A) g ≫
        SheafOfModules.homObjMap (R := X.sheaf) f (𝟙 B') := by
  simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-b2-homology-evaluation-cycle-existence). -/
private theorem cyclePairing_boundary_right (X : Scheme.{u}) (P T J : CochainComplex X.Modules ℤ)
    (π : ∀ (n p q : ℤ), p + n = q →
      (P.X n ⟶ SheafOfModules.homObj (R := X.sheaf) (T.X p) (J.X q)))
    (hπ : ∀ (n m p q q' p' : ℤ), n + 1 = m →
      ∀ (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
      P.d n m ≫ π m p q hpq =
        π n p q' hq' ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 (T.X p)) (J.d q' q) -
          n.negOnePow • (π n p' q hp' ≫
            SheafOfModules.homObjMap (R := X.sheaf) (T.d p p') (𝟙 (J.X q))))
    (n : ℤ) :
    ∀ (q : P.cycles n ⟶
        SheafOfModules.homObj (R := X.sheaf) (T.cycles (-n)) (J.cycles 0)),
      q ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 (T.cycles (-n))) (J.iCycles 0) =
        P.iCycles n ≫ π n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := X.sheaf) (T.iCycles (-n)) (𝟙 (J.X 0)) →
      (q ≫ SheafOfModules.homObjMap (R := X.sheaf)
        (𝟙 (T.cycles (-n))) (J.homologyπ 0)) ≫
        SheafOfModules.homObjMap (R := X.sheaf)
          (T.toCycles (-n - 1) (-n)) (𝟙 (J.homology 0)) = 0 := by
  intro q hq
  let δ := P.iCycles n ≫ π n (-n - 1) (-1) (by omega)
  let κ := P.iCycles n ≫ π n (-n) 0 (by omega) ≫
    SheafOfModules.homObjMap (R := X.sheaf) (T.d (-n - 1) (-n)) (𝟙 (J.X 0))
  have hd : δ ≫ SheafOfModules.homObjMap (R := X.sheaf)
      (𝟙 (T.X (-n - 1))) (J.d (-1) 0) = n.negOnePow • κ := by
    apply sub_eq_zero.mp
    have hh := congrArg (fun f => P.iCycles n ≫ f)
      (hπ n (n + 1) (-n - 1) 0 (-1) (-n) (by omega)
        (by omega) (by omega) (by omega))
    change (P.iCycles n ≫ (P.d n (n + 1) ≫ _)) = _ at hh
    simpa only [δ, κ, ← Category.assoc, P.iCycles_d, zero_comp,
      Preadditive.comp_sub, Linear.comp_units_smul] using hh.symm
  have hk : κ = n.negOnePow • (δ ≫ SheafOfModules.homObjMap (R := X.sheaf)
      (𝟙 (T.X (-n - 1))) (J.d (-1) 0)) := by
    rw [hd, smul_smul, Int.units_mul_self, one_smul]
  have hm := homMap_mono_right X (T.X (-n - 1)) (J.iCycles 0)
  have hqT : q ≫ SheafOfModules.homObjMap (R := X.sheaf)
      (T.toCycles (-n - 1) (-n)) (𝟙 (J.cycles 0)) =
      n.negOnePow • (δ ≫ SheafOfModules.homObjMap (R := X.sheaf)
        (𝟙 (T.X (-n - 1))) (J.toCycles (-1) 0)) := by
    apply (cancel_mono (SheafOfModules.homObjMap (R := X.sheaf)
      (𝟙 (T.X (-n - 1))) (J.iCycles 0))).1
    rw [Category.assoc, homMap_swap X, ← Category.assoc, hq]
    dsimp only [κ] at hk
    simpa only [Linear.units_smul_comp, Category.assoc,
      SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp, Category.comp_id,
      HomologicalComplex.toCycles_i] using hk
  rw [Category.assoc, ← homMap_swap X, ← Category.assoc, hqT,
    Linear.units_smul_comp, Category.assoc,
    SheafOfModules.homObjMap_comp_homObjMap (R := X.sheaf),
    J.toCycles_comp_homologyπ, homMap_zero_right, comp_zero, smul_zero]

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-b2-homology-evaluation-cycle-existence). -/
private theorem cyclePairing_representative (X : Scheme.{u})
    (P T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (π : P.X n ⟶ SheafOfModules.homObj (R := X.sheaf) (T.X (-n)) (J.X 0))
    (q : P.cycles n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.cycles (-n)) (J.cycles 0))
    (hq : q ≫ SheafOfModules.homObjMap (R := X.sheaf)
      (𝟙 (T.cycles (-n))) (J.iCycles 0) =
        P.iCycles n ≫ π ≫
          SheafOfModules.homObjMap (R := X.sheaf) (T.iCycles (-n)) (𝟙 (J.X 0)))
    (U : X.Opens) (φ : (P.cycles n).val.obj (op U))
    (z : (T.cycles (-n)).val.obj (op U)) (c : (J.cycles 0).val.obj (op U))
    (hc : (J.iCycles 0).val.app (op U) c =
      (π.val.app (op U) ((P.iCycles n).val.app (op U) φ)).app
        (op (Over.mk (𝟙 U))) ((T.iCycles (-n)).val.app (op U) z)) :
    (q.val.app (op U) φ).app (op (Over.mk (𝟙 U))) z = c := by
  have hqval := congrArg (fun f =>
    (f.val.app (op U) φ).app (op (Over.mk (𝟙 U))) z) hq
  change (J.iCycles 0).val.app (op U)
      ((q.val.app (op U) φ).app (op (Over.mk (𝟙 U))) z) =
    (π.val.app (op U) ((P.iCycles n).val.app (op U) φ)).app
      (op (Over.mk (𝟙 U))) ((T.iCycles (-n)).val.app (op U) z) at hqval
  have hm : Mono ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (J.iCycles 0)) :=
    inferInstance
  exact (ModuleCat.mono_iff_injective _).mp hm (hqval.trans hc.symm)

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-b2-homology-evaluation-cycle-existence). -/
private theorem homologyEvaluation_of_projections (X : Scheme.{u})
    (P T J : CochainComplex X.Modules ℤ)
    (π : ∀ (n p q : ℤ), p + n = q →
      (P.X n ⟶ SheafOfModules.homObj (R := X.sheaf) (T.X p) (J.X q)))
    (hπ : ∀ (n m p q q' p' : ℤ), n + 1 = m →
      ∀ (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
      P.d n m ≫ π m p q hpq =
        π n p q' hq' ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 (T.X p)) (J.d q' q) -
          n.negOnePow • (π n p' q hp' ≫
            SheafOfModules.homObjMap (R := X.sheaf) (T.d p p') (𝟙 (J.X q))))
    (n : ℤ) :
    ∃ e : P.homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0),
      ∀ (U : X.Opens) (φ : (P.cycles n).val.obj (op U))
        (z : (T.cycles (-n)).val.obj (op U)) (c : (J.cycles 0).val.obj (op U)),
        (J.iCycles 0).val.app (op U) c =
          ((π n (-n) 0 (by omega)).val.app (op U)
            ((P.iCycles n).val.app (op U) φ)).app
              (op (Over.mk (𝟙 U))) ((T.iCycles (-n)).val.app (op U) z) →
        (e.val.app (op U) ((P.homologyπ n).val.app (op U) φ)).app
          (op (Over.mk (𝟙 U))) ((T.homologyπ (-n)).val.app (op U) z) =
          (J.homologyπ 0).val.app (op U) c := by
  obtain ⟨q, hq⟩ := cyclePairing_lift X P T J π hπ n
  let a := q ≫ SheafOfModules.homObjMap (R := X.sheaf)
    (𝟙 (T.cycles (-n))) (J.homologyπ 0)
  have haP : P.toCycles (n - 1) n ≫ a = 0 :=
    cyclePairing_boundary_left X P T J π hπ n q hq
  have haT : a ≫ SheafOfModules.homObjMap (R := X.sheaf)
      (T.toCycles (-n - 1) (-n)) (𝟙 (J.homology 0)) = 0 :=
    cyclePairing_boundary_right X P T J π hπ n q hq
  let hc := P.homologyIsCokernel (n - 1) n (by simp)
  let b := hc.desc (CokernelCofork.ofπ a haP)
  have hb : P.homologyπ n ≫ b = a := hc.fac _ WalkingParallelPair.one
  have hbT : b ≫ SheafOfModules.homObjMap (R := X.sheaf)
      (T.toCycles (-n - 1) (-n)) (𝟙 (J.homology 0)) = 0 := by
    apply (cancel_epi (P.homologyπ n)).1
    rw [← Category.assoc, hb, comp_zero]
    exact haT
  obtain ⟨e, he⟩ := homObj_cokernel_desc X
    (T.toCycles (-n - 1) (-n)) (T.homologyπ (-n))
    (T.toCycles_comp_homologyπ (-n - 1) (-n))
    (T.homologyIsCokernel (-n - 1) (-n) (by simp)) b hbT
  refine ⟨e, ?_⟩
  intro U φ z c hc
  have h : (P.homologyπ n ≫ e) ≫ SheafOfModules.homObjMap (R := X.sheaf)
      (T.homologyπ (-n)) (𝟙 (J.homology 0)) = a := by
    rw [Category.assoc, he, hb]
  have hval := congrArg (fun f =>
    (f.val.app (op U) φ).app (op (Over.mk (𝟙 U))) z) h
  change (e.val.app (op U) ((P.homologyπ n).val.app (op U) φ)).app
    (op (Over.mk (𝟙 U))) ((T.homologyπ (-n)).val.app (op U) z) =
      (J.homologyπ 0).val.app (op U)
        ((q.val.app (op U) φ).app (op (Over.mk (𝟙 U))) z) at hval
  rw [cyclePairing_representative X P T J n (π n (-n) 0 (by omega)) q hq U φ z c hc]
    at hval
  exact hval


/-- Existence of the cycle-evaluation morphism.
Source: Stacks Project, Tag 0A8X, descent of the evaluation pairing.
(blueprint: new-b2-homology-evaluation-cycle-existence).

Proof: Write P = Hom(T,J). Its product projection defines the bilinear pairing
from P-cycles in degree n and T-cycles in degree -n to J in degree zero. For a
Hom cocycle phi and T-cycle z, the component differential equation gives
 d_J(phi(z)) = (-1)^n phi(d_T(z)) = 0.
Thus this pairing factors through J-cycles by their kernel universal property.
If phi = d_Hom(psi), with psi of degree n-1, evaluation on z is d_J(psi(z)),
since d_T(z)=0. If z=d_T(y), the cocycle equation in degree -n-1 gives
 phi(z)=(-1)^n d_J(phi(y)). Both values vanish after projecting to H^0(J).
The resulting bilinear pairing into H^0(J) therefore annihilates both boundary
subsheaves. Descend successively through the two cokernels defining homology.
These constructions commute with restriction because the product projections,
differentials and universal-property factorizations do. Curry the pairing by
internal Hom to obtain e. Its value on representatives is exactly the asserted
cycle formula. No cohomology concentration or finite-free hypothesis is needed.
For rank zero, zero complexes, or an empty open, the same universal properties
produce the zero pairing and the formula still holds. -/
theorem exists_homologyEvaluation_cycle (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ) :
    ∃ e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0),
      IsHomologyEvaluation X T J n e := by
  let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := X.sheaf))
  have hπ := (Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (R := X.sheaf))).2.1
  exact homologyEvaluation_of_projections X (homComplex (R := X.sheaf) T J) T J
    (fun n p q h => π T J n p q h) (hπ T J) n

end CategoryTheory
