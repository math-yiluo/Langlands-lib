/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}

open MonoidalCategory
@[instance_reducible]
private noncomputable def evaluationMonoidal (R : Sheaf S CommRingCat.{u}) : MonoidalCategory
    (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :=
  SheafOfModules.monoidalCategory R

attribute [local instance] evaluationMonoidal

@[instance_reducible]
private noncomputable def evaluationSymmetric
    (R : Sheaf S CommRingCat.{u}) : SymmetricCategory (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :=
  SheafOfModules.symmetricCategory R

attribute [local instance] evaluationSymmetric

@[instance_reducible]
private noncomputable def evaluationClosed (R : Sheaf S CommRingCat.{u}) : MonoidalClosed
    (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :=
  SheafOfModules.monoidalClosed (R := R)

attribute [local instance] evaluationClosed

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-v4-finite-free-zero-homology-evaluation-cycles). -/
private lemma homMap_zero_left (R : Sheaf S CommRingCat.{u}) {A A' B B' : (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R))} (g : B ⟶ B') :
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
(blueprint: new-v4-finite-free-zero-homology-evaluation-cycles). -/
private lemma homMap_zero_right (R : Sheaf S CommRingCat.{u}) {A A' B B' : (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R))} (f : A' ⟶ A) :
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
(blueprint: new-v4-finite-free-zero-homology-evaluation-cycles). -/
private lemma tensorHomEquiv_zero (R : Sheaf S CommRingCat.{u}) (A B N : (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) :
    SheafOfModules.tensorHomEquiv (R := R) A B N 0 = 0 := by
  have h := SheafOfModules.tensorHomEquiv_comp_homObjMap (R := R) A
    (0 : A ⊗ B ⟶ N) (0 : N ⟶ N)
  simpa only [comp_zero, homMap_zero_right] using h

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-v4-finite-free-zero-homology-evaluation-cycles). -/
private theorem homMap_mono_right (R : Sheaf S CommRingCat.{u}) (A : (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    {B B' : (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R))} (f : B ⟶ B') [Mono f] :
    Mono (SheafOfModules.homObjMap (R := R) (𝟙 A) f) := by
  have : ((SheafOfModules.homFunctor R).obj (op A)).IsRightAdjoint :=
    (SheafOfModules.tensorHomAdjunction R A).isRightAdjoint
  exact inferInstanceAs (Mono (((SheafOfModules.homFunctor R).obj (op A)).map f))

/-- Auxiliary step of cycle evaluation.
Source: Stacks Project, Tag 0A8X, the Hom differential and its descent;
Tag 03EO, tensor-Hom adjunction.
(blueprint: new-v4-finite-free-zero-homology-evaluation-cycles). -/
private theorem homObj_liftCycles (R : Sheaf S CommRingCat.{u}) (K : CochainComplex
    (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (i : ℤ) {A B : (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R))}
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
(blueprint: new-v4-finite-free-zero-homology-evaluation-cycles). -/
private theorem cyclePairing_lift (R : Sheaf S CommRingCat.{u}) (P T J : CochainComplex
    (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
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
  apply homObj_liftCycles R J 0 a
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
      _ = _ := congrArg (fun f => P.iCycles n ≫ f)
        (hπ n (n + 1) (-n) 1 0 (1 - n) (by omega)
          (by omega) (by omega) (by omega))
  have h := congrArg (fun f => f ≫ SheafOfModules.homObjMap (R := R)
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
(blueprint: new-v4-finite-free-zero-homology-evaluation-cycles). -/
private theorem cyclePairing_boundary_left (R : Sheaf S CommRingCat.{u})
    (P T J : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
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
  have hm := homMap_mono_right R (T.cycles (-n)) (J.iCycles 0)
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

set_option backward.isDefEq.respectTransparency false in
/-- Canonical cycle evaluation and its descent for a zero-differential source.

Source: Stacks Project, Tag 0A8X, Hom differential and evaluation on cohomology.
(blueprint: new-v4-finite-free-zero-homology-evaluation-cycles).

Proof: The differential identity shows that evaluating a Hom cycle on an E cycle
lands in K cycles. Lift through the kernel inclusion using tensor-Hom adjunction.
Evaluation of a Hom boundary is a K boundary, so postcomposition with the K class
map descends through the cokernel defining Hom-complex homology. Since E has zero
differentials, its cycle-to-homology map is an isomorphism; precompose with its
inverse to obtain f. These constructions give both displayed identities. No
finite support, finite freeness, or concentration assumption is needed. -/
theorem finiteFreeZero_homologyEvaluation_cycles
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    (R : Sheaf S CommRingCat.{u})
    (E K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n : ℤ)
    (hzero : ∀ a b : ℤ, E.d a b = 0) :
    let P := homComplex (R := R) E K
    let π := (Classical.choose (homComplex_projections_exists (R := R)))
      E K n (-n) 0 (by omega)
    ∃ f : P.homology n ⟶ SheafOfModules.homObj (R := R)
        (E.homology (-n)) (K.homology 0),
      ∃ c : P.cycles n ⟶
        SheafOfModules.homObj (R := R) (E.cycles (-n)) (K.cycles 0),
      c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
        P.iCycles n ≫ π ≫ SheafOfModules.homObjMap (R := R) (E.iCycles (-n)) (𝟙 _) ∧
      c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
        P.homologyπ n ≫ f ≫ SheafOfModules.homObjMap (R := R) (E.homologyπ (-n)) (𝟙 _) := by
  dsimp
  let P := homComplex (R := R) E K
  let π := Classical.choose (homComplex_projections_exists (R := R))
  have hπ := (Classical.choose_spec (homComplex_projections_exists (R := R))).2.1
  obtain ⟨c, hc⟩ := cyclePairing_lift R P E K (π E K) (hπ E K) n
  let a := c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0)
  have ha : P.toCycles (n - 1) n ≫ a = 0 :=
    cyclePairing_boundary_left R P E K (π E K) (hπ E K) n c hc
  let hcok := P.homologyIsCokernel (n - 1) n (by simp)
  let b : P.homology n ⟶
      SheafOfModules.homObj (R := R) (E.cycles (-n)) (K.homology 0) :=
    hcok.desc (CokernelCofork.ofπ a ha)
  have hb : P.homologyπ n ≫ b = a := hcok.fac _ WalkingParallelPair.one
  have : IsIso (E.homologyπ (-n)) :=
    E.isIso_homologyπ (-n - 1) (-n) (by simp) (hzero _ _)
  let f := b ≫ SheafOfModules.homObjMap (R := R) (inv (E.homologyπ (-n))) (𝟙 _)
  refine ⟨f, c, hc, ?_⟩
  dsimp only [f]
  simp only [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap]
  simp only [IsIso.hom_inv_id, Category.id_comp, SheafOfModules.homObjMap_id]
  simpa only [Category.comp_id, a, P] using hb.symm

end CategoryTheory
