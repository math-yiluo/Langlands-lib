/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedAffineFiberInterpolation
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedAffinePatternCover
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! Local dual separation before sheafification.
(blueprint: lem-sfb-completed-affine-free-local-dual-local-presheaf)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Extend a natural scalar test by the free-module universal property, then descend
along the restricted sheafification unit. -/
private theorem scalar_test_extends
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J RingCat.{u}) (Q : Cᵒᵖ ⥤ Type u) (W : C)
    [(J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (β : (Over.forget W).op ⋙ Q ⟶
      (SheafOfModules.unit (R.over W)).val.presheaf ⋙ forget AddCommGrpCat.{u}) :
    let F := (PresheafOfModules.free R.obj).obj Q
    let P := (PresheafOfModules.sheafification (𝟙 R.obj)).obj F
    let η := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app F
    ∃ φ : P.over W ⟶ SheafOfModules.unit (R.over W),
      ∀ y : F.obj (op W), φ.val.app (op (Over.mk (𝟙 W))) (η.app (op W) y) =
        (ModuleCat.freeDesc (β.app (op (Over.mk (𝟙 W))))) y := by
  let F := (PresheafOfModules.free R.obj).obj Q
  let P := (PresheafOfModules.sheafification (𝟙 R.obj)).obj F
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app F
  let H := PresheafOfModules.pushforward (F := Over.forget W) (𝟙 (R.over W).obj)
  let ηW : H.obj F ⟶ (P.over W).val := H.map η
  let g : H.obj F ⟶ (SheafOfModules.unit (R.over W)).val :=
    PresheafOfModules.freeObjDesc β
  have hηi : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map η) := by
    change Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J F.presheaf)
    infer_instance
  have hηs : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map η) := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J F.presheaf)
    infer_instance
  have : PresheafOfModules.IsLocallyInjective (J.over W) ηW := by
    exact Presheaf.isLocallyInjective_whisker (J.over W) J (Over.forget W)
      ((PresheafOfModules.toPresheaf _).map η)
  have : PresheafOfModules.IsLocallySurjective (J.over W) ηW := by
    exact Presheaf.isLocallySurjective_whisker (J.over W) J (Over.forget W)
      ((PresheafOfModules.toPresheaf _).map η)
  let E := PresheafOfModules.homEquivOfIsLocallyBijective
    (J := J.over W) (f := ηW) (SheafOfModules.unit (R.over W)).isSheaf
  let φ : P.over W ⟶ SheafOfModules.unit (R.over W) := ⟨E.symm g⟩
  refine ⟨φ, fun y ↦ ?_⟩
  have he : ηW ≫ φ.val = g := E.apply_symm_apply g
  exact congrArg (fun k ↦ k y) (congrArg (fun k ↦ k.app (op (Over.mk (𝟙 W)))) he)

open Classical in
/-- Group a finite linear combination by an equivalence relation. Classes are allowed
to merge under the map to the module; each original class still sums to zero. -/
private theorem sum_smul_eq_zero_of_class_sums
    {ι A B : Type*} [Fintype ι] [Semiring A] [AddCommMonoid B] [Module A B]
    (r : Setoid ι) (a : ι → A) (b : ι → B)
    (hb : ∀ i j, r.r i j → b i = b j)
    (ha : ∀ i, (∑ j, if r.r j i then a j else 0) = 0) :
    (∑ j, a j • b j) = 0 := by
  classical
  apply Finset.sum_cancels_of_partition_cancels r
  intro i _
  have hs : (∑ j ∈ Finset.univ.filter (fun j ↦ r.r j i), a j) = 0 := by
    simpa only [Finset.sum_filter] using ha i
  calc
    _ = (∑ j ∈ Finset.univ.filter (fun j ↦ r.r j i), a j) • b i := by
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hb j i (Finset.mem_filter.mp hj).2]
    _ = 0 := by rw [hs, zero_smul]

/-- Finite-support local dual separation for the free presheaf on a pro-affine etale
representable, provided its section has nonzero image in sheafification.

Source: the finite-support argument in `completedAffineFree_localDual_detect`, in
`CompletedAffineFreeLocalDual.lean`; coefficient-twist blueprint, paragraph (1).
(blueprint: lem-sfb-completed-affine-free-local-dual-local-presheaf)

Proof: write the section as a finite free sum of maps to U with completed
coefficients. In a cofiltered affine etale presentation of U, each stage graph is
clopen. Its characteristic function defines a natural scalar-valued test on the
slice over W. Extend the test through the free-module and sheafification adjunctions.
Suppose every such test vanishes. After restricting W to an affine open, completed
coefficients are continuous functions on its profinite component space with values
in Z_l. At each component one common stage distinguishes the finitely many distinct
limit maps, so every equality-class coefficient sum vanishes. There are finitely
many equality patterns. On the closure of each pattern stratum, equalities persist
and coefficient sums remain zero by continuity into Hausdorff Z_l. The canonical
closed component restrictions, constructed by localizing at clopen-neighborhood
idempotents, give a finite jointly surjective pro-etale cover. On each restriction
the finite sum cancels class by class. Its sheafification image therefore vanishes
by separatedness, contrary to the hypothesis. Thus a stage test is nonzero, and its
extension is the required map. Empty support and an empty test object already have
zero sheafification image and cannot satisfy the hypothesis.

The former hypothesis `y ≠ 0` was false: four globally distinct maps on two disjoint
components may pair up differently on the components. The formal swap-kernel lemma
above certifies this obstruction; the change record gives the scheme example. -/
theorem completedAffineFree_presheaf_localDual (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ) (hU : proAffineEtale U.unop.hom)
    (W : X.ProEt) :
    let R := Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)
    let F := (PresheafOfModules.free R.obj).obj
      (uliftYoneda.{u + 1}.obj U.unop)
    let P := (PresheafOfModules.sheafification (𝟙 R.obj)).obj F
    ∀ y : F.obj (op W),
      (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app F).app
        (op W) y) ≠ 0 →
      ∃ (φ : P.over W ⟶ SheafOfModules.unit (R.over W)),
        φ.val.app (op (Over.mk (𝟙 W)))
          (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app F).app
            (op W) y) ≠ 0 := by
  classical
  dsimp only
  let R := Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)
  let Q := uliftYoneda.{u + 1}.obj U.unop
  let F := (PresheafOfModules.free R.obj).obj Q
  let P := (PresheafOfModules.sheafification (𝟙 R.obj)).obj F
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app F
  intro y hy0
  by_contra h
  have hφ : ∀ φ : P.over W ⟶ SheafOfModules.unit (R.over W),
      φ.val.app (op (Over.mk (𝟙 W))) (η.app (op W) y) = 0 := by
    intro φ
    by_contra hz
    exact h ⟨φ, hz⟩
  let : EssentiallySmall.{u + 1} (Over W) := essentiallySmallSelf.{0, u, u + 1} _
  have : ((Scheme.ProEt.topology X).over W).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let z : Q.obj (op W) →₀ R.obj.obj (op W) := y
  let ι := {i // i ∈ z.support}
  let q (i : ι) : Q.obj (op W) := i.val
  let a (i : ι) : R.obj.obj (op W) := z i.val
  have hy : y = ∑ i : ι, a i • ModuleCat.freeMk (q i) := by
    change z = ∑ i : ι, z i.val • Finsupp.single i.val 1
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact (z.sum_single).symm.trans (Finset.sum_attach _ _).symm
  obtain ⟨M⟩ := completedAffineCoefficientModel_exists l X
  have ha : ∀ (x : W.left) (i : ι),
      (∑ j : ι, if W.left.fromSpecResidueField x ≫ (q j).down.left =
          W.left.fromSpecResidueField x ≫ (q i).down.left
        then M.equiv W (a j) x else 0) = 0 := by
    intro x i
    obtain ⟨β, hβ⟩ := completedAffine_fiber_interpolation l X M U hU W q x i
    obtain ⟨φ, he⟩ := scalar_test_extends (Scheme.ProEt.topology X) R Q W β
    have hz := (he y).symm.trans (hφ φ)
    rw [hy] at hz
    simp only [map_sum, map_smul, ModuleCat.freeDesc_apply] at hz
    change (∑ j : ι, a j *
      (show R.obj.obj (op W) from β.app (op (Over.mk (𝟙 W))) (q j))) = 0 at hz
    have heval := congrArg (fun t ↦ M.equiv W t x) hz
    simpa only [map_sum, ContinuousMap.sum_apply, map_mul, ContinuousMap.mul_apply,
      map_zero, ContinuousMap.zero_apply, hβ, mul_ite, mul_one, mul_zero] using heval
  obtain ⟨S, hS, hlocal⟩ := completedAffine_pattern_cover l X M U hU W q a ha
  apply hy0
  apply P.isSheaf.isSeparated _ _ hS
  intro V f hf
  change P.val.map f.op (η.app (op W) y) = P.val.map f.op 0
  obtain ⟨r, hrq, hra⟩ := hlocal V f hf
  have hm (i : ι) : F.map f.op (ModuleCat.freeMk (q i)) =
      ModuleCat.freeMk (Q.map f.op (q i)) := ModuleCat.freeDesc_apply _ _
  have hz : F.map f.op y = 0 := by
    rw [hy]
    simp only [map_sum]
    simp_rw [F.map_smul, hm]
    apply sum_smul_eq_zero_of_class_sums r _ _ _ hra
    intro i j hij
    exact congrArg ModuleCat.freeMk (hrq i j hij)
  have hn := congrArg (fun k ↦ k y) (η.naturality f.op)
  change η.app (op V) (F.map f.op y) = P.val.map f.op (η.app (op W) y) at hn
  simpa only [hz, map_zero] using hn.symm

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
