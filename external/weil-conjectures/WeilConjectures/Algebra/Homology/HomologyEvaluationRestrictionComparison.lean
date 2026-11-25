/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
import WeilConjectures.Algebra.Homology.HomologyEvaluationRestrictionDiagrams
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Restriction of cycle evaluation -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

@[instance_reducible]
private noncomputable def evaluationMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

private lemma homMap_zero_left (X : Scheme.{u}) {A A' B B' : X.Modules} (g : B ⟶ B') :
    SheafOfModules.homObjMap (R := X.sheaf) (0 : A' ⟶ A) g = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver X.sheaf.obj U.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver X.sheaf.obj U.unop).map g.val = 0
  ext W x
  change ((g.val.app _).hom) ((φ.app W).hom (0)) = 0
  rw [map_zero, map_zero]

private lemma homMap_zero_right (X : Scheme.{u}) {A A' B B' : X.Modules} (f : A' ⟶ A) :
    SheafOfModules.homObjMap (R := X.sheaf) f (0 : B ⟶ B') = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver X.sheaf.obj U.unop).map f.val ≫ φ ≫
    (PresheafOfModules.restrictOver X.sheaf.obj U.unop).map 0 = 0
  ext W x
  rfl

private lemma tensorHomEquiv_zero (X : Scheme.{u}) (A B N : X.Modules) :
    SheafOfModules.tensorHomEquiv (R := X.sheaf) A B N 0 = 0 := by
  let := evaluationMonoidal X
  have h := SheafOfModules.tensorHomEquiv_comp_homObjMap (R := X.sheaf) A
    (0 : MonoidalCategory.tensorObj A B ⟶ N) (0 : N ⟶ N)
  simpa only [comp_zero, homMap_zero_right] using h

private theorem homObj_liftCycles (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (i : ℤ) {A B : X.Modules}
    (a : A ⟶ SheafOfModules.homObj (R := X.sheaf) B (K.X i))
    (ha : a ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 B) (K.d i (i + 1)) = 0) :
    ∃ b : A ⟶ SheafOfModules.homObj (R := X.sheaf) B (K.cycles i),
      b ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 B) (K.iCycles i) = a := by
  let := evaluationMonoidal X
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
      _ = _ := congrArg (fun f ↦ P.iCycles n ≫ f)
        (hπ n (n + 1) (-n) 1 0 (1 - n) (by omega)
          (by omega) (by omega) (by omega))
  have h := congrArg (fun f ↦ f ≫ SheafOfModules.homObjMap (R := X.sheaf)
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
private theorem ambient_cycle_pairing (X : Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0))
    (he : IsHomologyEvaluation X T J n e) :
    let P := homComplex (R := X.sheaf) T J
    ∃ d : P.cycles n ⟶
        SheafOfModules.homObj (R := X.sheaf) (T.cycles (-n)) (J.cycles 0),
      d ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 _) (J.iCycles 0) =
        P.iCycles n ≫ homologyEvaluationProjection X T J n ≫
          SheafOfModules.homObjMap (R := X.sheaf) (T.iCycles (-n)) (𝟙 _) ∧
      d ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 _) (J.homologyπ 0) =
        P.homologyπ n ≫ e ≫
          SheafOfModules.homObjMap (R := X.sheaf) (T.homologyπ (-n)) (𝟙 _) := by
  let P := homComplex (R := X.sheaf) T J
  let π := Classical.choose (homComplex_projections_exists (R := X.sheaf))
  have hπ := (Classical.choose_spec
    (homComplex_projections_exists (R := X.sheaf))).2.1
  obtain ⟨d, hd⟩ := cyclePairing_lift X P T J
    (fun n p q h ↦ π T J n p q h) (hπ T J) n
  refine ⟨d, hd, ?_⟩
  let l := d ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 _) (J.homologyπ 0)
  let r := P.homologyπ n ≫ e ≫
    SheafOfModules.homObjMap (R := X.sheaf) (T.homologyπ (-n)) (𝟙 _)
  have ht (U : X.Opens) (φ : (P.cycles n).val.obj (op U))
      (z : (T.cycles (-n)).val.obj (op U)) :
      (l.val.app (op U) φ).app (op (Over.mk (𝟙 U))) z =
        (r.val.app (op U) φ).app (op (Over.mk (𝟙 U))) z := by
    let b := (d.val.app (op U) φ).app (op (Over.mk (𝟙 U))) z
    have hb := congrArg (fun f ↦
      (f.val.app (op U) φ).app (op (Over.mk (𝟙 U))) z) hd
    change (J.iCycles 0).val.app (op U) b =
      ((homologyEvaluationProjection X T J n).val.app (op U)
        ((P.iCycles n).val.app (op U) φ)).app
          (op (Over.mk (𝟙 U))) ((T.iCycles (-n)).val.app (op U) z) at hb
    exact (he U φ z b hb).symm
  apply SheafOfModules.hom_ext
  ext U φ : 3
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let V := W.unop.left
  let φV := (P.cycles n).val.map W.unop.hom.op φ
  have hn (a : P.cycles n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.cycles (-n)) (J.homology 0)) :
      (a.val.app (op V) φV).app (op (Over.mk (𝟙 V))) z =
        (a.val.app U φ).app W z := by
    rw [PresheafOfModules.naturality_apply a.val W.unop.hom.op]
    exact PresheafOfModules.restrictOver_hom_app_congr _
      (Category.id_comp W.unop.hom) _
  exact (hn l).symm.trans ((ht V φV z).trans (hn r))

private theorem transport_cycle_pairing
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {Z H L M N B : C} {Z' H' L' M' N' B' : D}
    {m : Z ⟶ M} {i : L ⟶ M} {j : L ⟶ N} {p : Z ⟶ H} {z : B ⟶ N}
    {m' : Z' ⟶ M'} {i' : L' ⟶ M'} {j' : L' ⟶ N'}
    {p' : Z' ⟶ H'} {z' : B' ⟶ N'} (e : H ⟶ B)
    (h : ∃ a : F.obj H ≅ H', ∃ b : F.obj B ≅ B',
      ∃ c : F.obj Z ≅ Z', ∃ s : F.obj L ≅ L',
      ∃ t : F.obj M ≅ M', ∃ v : F.obj N ≅ N',
        F.map m ≫ t.hom = c.hom ≫ m' ∧
        F.map i ≫ t.hom = s.hom ≫ i' ∧
        F.map j ≫ v.hom = s.hom ≫ j' ∧
        F.map p ≫ a.hom = c.hom ≫ p' ∧
        F.map z ≫ v.hom = b.hom ≫ z')
    (hd : ∃ d : Z ⟶ L, d ≫ i = m ∧ d ≫ j = p ≫ e ≫ z) :
    ∃ a : F.obj H ≅ H', ∃ b : F.obj B ≅ B',
      ∃ g : H' ⟶ B', ∃ d : Z' ⟶ L',
        d ≫ i' = m' ∧ d ≫ j' = p' ≫ g ≫ z' ∧ F.map e ≫ b.hom = a.hom ≫ g := by
  obtain ⟨a, b, c, s, t, v, hproj, hi, hj, hp, ht⟩ := h
  obtain ⟨d, hd, heq⟩ := hd
  let g := a.inv ≫ F.map e ≫ b.hom
  let d' := c.inv ≫ F.map d ≫ s.hom
  refine ⟨a, b, g, d', ?_, ?_, ?_⟩
  · change (c.inv ≫ F.map d ≫ s.hom) ≫ i' = m'
    calc
      _ = c.inv ≫ F.map d ≫ F.map i ≫ t.hom := by
        rw [Category.assoc, Category.assoc, ← hi]
      _ = c.inv ≫ F.map (d ≫ i) ≫ t.hom := by rw [F.map_comp, Category.assoc]
      _ = m' := by rw [hd, hproj]; simp only [Iso.inv_hom_id_assoc]
  · have hpc : c.inv ≫ F.map p = p' ≫ a.inv := by
      apply (cancel_mono a.hom).1
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Iso.inv_hom_id_assoc] using congrArg (fun f ↦ c.inv ≫ f) hp
    change (c.inv ≫ F.map d ≫ s.hom) ≫ j' = p' ≫ g ≫ z'
    calc
      _ = c.inv ≫ F.map d ≫ F.map j ≫ v.hom := by
        rw [Category.assoc, Category.assoc, ← hj]
      _ = c.inv ≫ F.map (d ≫ j) ≫ v.hom := by rw [F.map_comp, Category.assoc]
      _ = c.inv ≫ F.map p ≫ F.map e ≫ b.hom ≫ z' := by
        rw [heq, F.map_comp, F.map_comp]
        simp only [Category.assoc]
        rw [ht]
      _ = p' ≫ g ≫ z' := by
        rw [← Category.assoc, hpc]
        simp only [g, Category.assoc]
  · change F.map e ≫ b.hom = a.hom ≫ (a.inv ≫ F.map e ≫ b.hom)
    simp only [Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency true in
/-- Restriction transports evaluation to a cycle-compatible evaluation on the over site.

Source: Stacks Project, Tags 0A8X (Hom differential) and 08DL (open restriction).
(blueprint: new-e3-homology-evaluation-restriction-comparison).

Proof: Write F for restriction to V followed by restriction to the site over W.
Both restrictions are exact and preserve products. Construct the comparison
F(Hom(T,J)) to Hom(F(T),F(J)) degreewise using the product universal property
and the local internal-Hom identifications: each local map is sent to the same
map on the smaller open. Checking each product projection proves differential
compatibility and evaluation compatibility. Exactness gives comparisons on
cycles and homology; internal Hom commutes with these restrictions by the same
local-map identification. These give a and b. Define g by transporting F(e)
along a and b. On Hom cycles, the differential identity says evaluation on a
source cycle is a target cycle. The kernel property of target cycles therefore
gives d. Its composite with target cycle inclusion is the first displayed
identity. To prove the second, evaluate on sections of source cycles on every
slice open. The hypothesis he identifies g on these representatives with the
class of the target cycle just constructed. Extensionality of local linear
maps and separatedness give the second morphism identity. The definition of g
gives the last square. This uses neither K-injectivity nor a roof, and works
for zero complexes and empty opens by the same universal properties. -/
theorem homologyEvaluation_restriction_comparison (X : Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0))
    (he : IsHomologyEvaluation X T J n e) (V : X.Opens) (W : V.toScheme.Opens) :
    let A := (moduleOpenOverComplexFunctor X V W).obj T
    let K := (moduleOpenOverComplexFunctor X V W).obj J
    let Q := homComplex (R := V.toScheme.sheaf.over W) A K
    let π := (Classical.choose
      (homComplex_projections_exists (R := V.toScheme.sheaf.over W)))
      A K n (-n) 0 (by omega)
    ∃ a : ((Scheme.Modules.restrictFunctor V.ι).obj
        ((homComplex (R := X.sheaf) T J).homology n)).over W ≅ Q.homology n,
      ∃ b : ((Scheme.Modules.restrictFunctor V.ι).obj
          (SheafOfModules.homObj (R := X.sheaf)
            (T.homology (-n)) (J.homology 0))).over W ≅
          SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.homology (-n)) (K.homology 0),
        ∃ g : Q.homology n ⟶ SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
            (A.homology (-n)) (K.homology 0),
          ∃ d : Q.cycles n ⟶ SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
              (A.cycles (-n)) (K.cycles 0),
            d ≫ SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W)
                (𝟙 _) (K.iCycles 0) =
              Q.iCycles n ≫ π ≫ SheafOfModules.homObjMap
                (R := V.toScheme.sheaf.over W) (A.iCycles (-n)) (𝟙 _) ∧
            d ≫ SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W)
                (𝟙 _) (K.homologyπ 0) =
              Q.homologyπ n ≫ g ≫ SheafOfModules.homObjMap
                (R := V.toScheme.sheaf.over W) (A.homologyπ (-n)) (𝟙 _) ∧
            (((Scheme.Modules.restrictFunctor V.ι).map e).over W) ≫ b.hom =
              a.hom ≫ g := by
  exact transport_cycle_pairing
    (Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf W) e
    (homologyEvaluation_restriction_diagrams X T J n V W)
    (ambient_cycle_pairing X T J n e he)

end CategoryTheory
