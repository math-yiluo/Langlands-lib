/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Order.CompletePartialOrder
public import WeilConjectures.AlgebraicGeometry.AdicLisseModule
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCompletion
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
import all WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientTerminal

/-! # Normalized completion of compact adic continuous coefficients

Bhatt--Scholze, Lemmas 4.2.12 and 6.8.2(1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj Topology
namespace AlgebraicGeometry.ProEtale

private theorem quotient_locallyConstant
    (A : Type u) [CommRing A] [TopologicalSpace A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (n : ℕ) : IsLocallyConstant
      (Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1))) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  exact (hb x).mem_of_mem (i := n) trivial

private theorem residue_lift
    (A : Type u) [CommRing A] [TopologicalSpace A] [CompactSpace A] [T2Space A]
    (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (b : ∀ n : ℕ, A ⧸ Ideal.span ({p} : Set A) ^ (n + 1))
    (hcompat : ∀ n : ℕ,
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
        (b (n + 1)) = b n) :
    ∃! a : A, ∀ n : ℕ, Ideal.Quotient.mk
      (Ideal.span ({p} : Set A) ^ (n + 1)) a = b n := by
  let q (n : ℕ) := Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1))
  let S (n : ℕ) : Set A := {a | q n a = b n}
  have hclosed (n : ℕ) : IsClosed (S n) :=
    (quotient_locallyConstant A p hb n).isClosed_fiber _
  have hnon (n : ℕ) : (S n).Nonempty := Ideal.Quotient.mk_surjective (b n)
  have hstep (n : ℕ) : S (n + 1) ⊆ S n := by
    intro a ha
    exact (congrArg (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) ha).trans (hcompat n)
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hstep hnon (hclosed 0).isCompact hclosed
  have hqa (n : ℕ) : q n a = b n := Set.mem_iInter.mp ha n
  refine ⟨a, hqa, ?_⟩
  intro a' ha'
  apply pure_le_nhds_iff.mp
  intro V hV
  obtain ⟨n, _, hn⟩ := (hb a).mem_iff.mp hV
  exact hn ((ha' n).trans (hqa n).symm)

private theorem continuous_of_residues
    (A : Type u) [CommRing A] [TopologicalSpace A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    {X : Type v} [TopologicalSpace X] (f : X → A)
    (hf : ∀ n : ℕ, IsLocallyConstant (fun x ↦
      Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) (f x))) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt, (hb (f x)).tendsto_right_iff]
  intro n _
  exact (hf n).eventually_eq x

private theorem continuous_division
    (A : Type u) [CommRing A] [IsDomain A] [TopologicalSpace A]
    [IsTopologicalRing A] [CompactSpace A] [T2Space A]
    (p : A) (hp : p ≠ 0) {X : Type v} [TopologicalSpace X] (f : C(X, A))
    (a : A) (n : ℕ)
    (h : ∀ x, Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) (f x) =
      Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) a) :
    ∃ g : C(X, A), ∀ x, f x = a + p ^ (n + 1) * g x := by
  classical
  have hm : Continuous (fun z : A ↦ p ^ (n + 1) * z) :=
    continuous_const.mul continuous_id
  have hi : Function.Injective (fun z : A ↦ p ^ (n + 1) * z) :=
    mul_right_injective₀ (pow_ne_zero _ hp)
  have he := hm.isClosedEmbedding hi
  have hd (x : X) : ∃ z : A, p ^ (n + 1) * z = f x - a := by
    have hx := Ideal.Quotient.eq.mp (h x)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨z, hz⟩ := hx
    exact ⟨z, hz.symm⟩
  let g (x : X) : A := (hd x).choose
  have hg (x : X) : p ^ (n + 1) * g x = f x - a := (hd x).choose_spec
  have hgc : Continuous g := he.isEmbedding.isInducing.continuous_iff.mpr (by
    change Continuous (fun x ↦ p ^ (n + 1) * g x)
    have hc : Continuous (fun x : X ↦ f x - a) :=
      f.continuous.sub (continuous_const : Continuous (fun _ : X ↦ a))
    exact (show (fun x ↦ p ^ (n + 1) * g x) = (fun x ↦ f x - a) from
      funext hg) ▸ hc)
  refine ⟨⟨g, hgc⟩, ?_⟩
  intro x
  rw [show (⟨g, hgc⟩ : C(X, A)) x = g x from rfl, hg]
  exact (add_sub_cancel _ _).symm

private theorem continuousFiniteQuotientHom_ext
    (A : Type (u + 1)) [CommRing A] [IsDomain A] [TopologicalSpace A]
    [IsTopologicalRing A] [CompactSpace A] [T2Space A]
    (p : A) (hp : p ≠ 0)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (T : Scheme.{u}) (n : ℕ) (B : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (φ ψ : Scheme.continuousCoefficientSheaf T A ⟶ B)
    (hscalar : ∀ (U : T.ProEtᵒᵖ) (a : A),
      φ.hom.app U (ContinuousMap.const U.unop.left a) =
        ψ.hom.app U (ContinuousMap.const U.unop.left a))
    (hkill : ∀ U : T.ProEtᵒᵖ,
      φ.hom.app U (ContinuousMap.const U.unop.left p) ^ (n + 1) = 0) : φ = ψ := by
  classical
  ext U f
  change C(U.unop.left, A) at f
  let q := Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1))
  have hlocal : IsLocallyConstant (fun x ↦ q (f x)) :=
    (quotient_locallyConstant A p hb n).comp_continuous f.continuous
  let O (x : U.unop.left) : U.unop.left.Opens :=
    ⟨{y | q (f y) = q (f x)}, hlocal.isOpen_fiber _⟩
  have hc : Presheaf.equalizerSieve (φ.hom.app U f) (ψ.hom.app U f) ∈
      Scheme.ProEt.topology T U.unop := by
    apply Scheme.ProEt.mem_topology_of_openImmersion _ (fun x ↦ (O x).ι)
    · intro x
      exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
    · intro x
      let W := U.unop.ofOpenImmersion (O x).ι
      let j : W ⟶ U.unop := Scheme.ProEt.ofOpenImmersionHom U.unop (O x).ι
      let V := op W
      let f' : C(W.left, A) := f.comp (O x).ι.base.hom
      obtain ⟨g, hg⟩ := continuous_division A p hp f' (f x) n (fun y ↦ y.property)
      have heq : f' = ContinuousMap.const _ (f x) +
          ContinuousMap.const _ p ^ (n + 1) * g := by
        ext y
        exact hg y
      change B.obj.map j.op (φ.hom.app U f) = B.obj.map j.op (ψ.hom.app U f)
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
      change φ.hom.app V f' = ψ.hom.app V f'
      rw [heq, map_add, map_add, map_mul, map_mul, map_pow, map_pow]
      rw [← hscalar V p, hkill V, zero_mul, zero_mul, add_zero, add_zero,
        hscalar V (f x)]
  exact B.isSeparated U.unop _ hc _ _ (fun _ _ h ↦ h)

private theorem totallyDisconnected_of_basis
    (A : Type u) [CommRing A] [TopologicalSpace A] [T2Space A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x})) :
    TotallyDisconnectedSpace A := by
  let Q (n : ℕ) := A ⧸ Ideal.span ({p} : Set A) ^ (n + 1)
  let : ∀ n, TopologicalSpace (Q n) := fun _ ↦ ⊥
  let : ∀ n, DiscreteTopology (Q n) := fun _ ↦ ⟨rfl⟩
  let f : A → ∀ n, Q n := fun x n ↦ Ideal.Quotient.mk _ x
  have hc : Continuous f := continuous_pi (fun n ↦
    (IsLocallyConstant.iff_continuous _).mp (quotient_locallyConstant A p hb n))
  have hi : Function.Injective f := by
    intro x y hxy
    apply pure_le_nhds_iff.mp
    intro V hV
    obtain ⟨n, _, hn⟩ := (hb y).mem_iff.mp hV
    exact hn (congrFun hxy n)
  exact ⟨isTotallyDisconnected_of_image hc.continuousOn hi
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

private theorem ulift_basis
    (A : Type u) [CommRing A] [TopologicalSpace A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (x : ULift.{u + 1} A) :
    (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^
          (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^
          (n + 1)) x}) := by
  let e : ULift.{u + 1} A ≃+* A := ULift.ringEquiv
  have hm (n : ℕ) : Ideal.span ({p} : Set A) ^ (n + 1) =
      Ideal.map e.toRingHom
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^ (n + 1)) := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    rfl
  have hq (n : ℕ) (y : ULift.{u + 1} A) :
      Ideal.Quotient.mk (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^
          (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^
          (n + 1)) x ↔
      Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y.down =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x.down :=
    (Ideal.quotientEquiv _ _ e (hm n)).injective.eq_iff.symm
  rw [Topology.IsEmbedding.uliftDown.isInducing.nhds_eq_comap x]
  simpa only [Set.preimage_ofPred_eq, ← hq] using
    (hb x.down).comap (ULift.down : ULift.{u + 1} A → A)

private def quotientTower (A : Type (u + 1)) [CommRing A] (p : A) :
    ℕᵒᵖ ⥤ CommRingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n : ℕ ↦
    CommRingCat.of (A ⧸ Ideal.span ({p} : Set A) ^ (n + 1))) (fun n ↦
    CommRingCat.ofHom (Ideal.Quotient.factorPowSucc (Ideal.span ({p} : Set A)) (n + 1)))

private def continuousResidueCone (A : Type (u + 1)) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (T : Scheme.{u}) :
    Cone (quotientTower A p ⋙ Scheme.discreteContinuousCoefficientFunctor T) := by
  let Q (n : ℕ) := A ⧸ Ideal.span ({p} : Set A) ^ (n + 1)
  let : ∀ n, TopologicalSpace (Q n) := fun _ ↦ ⊥
  let : ∀ n, DiscreteTopology (Q n) := fun _ ↦ ⟨rfl⟩
  refine { pt := Scheme.continuousCoefficientSheaf T A, π := ?_ }
  exact NatTrans.ofOpSequence (fun n ↦ Scheme.continuousCoefficientMap
    (Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)))
    ((IsLocallyConstant.iff_continuous _).mp (quotient_locallyConstant A p hb n)) T)
    (by
      intro n
      simp only [Functor.const_obj_map, Functor.comp_map, quotientTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      ext U f
      apply @ContinuousMap.ext U.unop.left (Q n) _ ⊥
      intro x
      rfl)

private def continuousResidueCone_isLimit (A : Type (u + 1)) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [CompactSpace A] [T2Space A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (T : Scheme.{u}) : IsLimit (continuousResidueCone A p hb T) := by
  classical
  let Q (n : ℕ) := A ⧸ Ideal.span ({p} : Set A) ^ (n + 1)
  let : ∀ n, TopologicalSpace (Q n) := fun _ ↦ ⊥
  let : ∀ n, DiscreteTopology (Q n) := fun _ ↦ ⟨rfl⟩
  apply isLimitOfReflects (sheafToPresheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
  apply evaluationJointlyReflectsLimits
  intro U
  apply Classical.choice
  apply Scheme.commRingForgetReflectsLimit
  apply Classical.choice
  apply (Types.isLimit_iff_bijective_sectionOfCone _).mpr
  constructor
  · intro f g hfg
    change C(U.unop.left, A) at f g
    apply ContinuousMap.ext
    intro x
    have hf (n : ℕ) : Ideal.Quotient.mk
        (Ideal.span ({p} : Set A) ^ (n + 1)) (f x) =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) (g x) :=
      congrArg (fun s ↦ (s.val (op n) : C(U.unop.left, Q n)) x) hfg
    apply pure_le_nhds_iff.mp
    intro V hV
    obtain ⟨n, _, hn⟩ := (hb (g x)).mem_iff.mp hV
    exact hn (hf n)
  · intro s
    let t (n : ℕ) : C(U.unop.left, Q n) := s.val (op n)
    have ht (x : U.unop.left) : ∃! a : A, ∀ n, Ideal.Quotient.mk
        (Ideal.span ({p} : Set A) ^ (n + 1)) a = t n x := by
      apply residue_lift A p hb (fun n ↦ t n x)
      intro n
      have hn := s.property (homOfLE (Nat.le_succ n)).op
      simp only [Functor.comp_map, quotientTower,
        Functor.ofOpSequence_map_homOfLE_succ] at hn
      exact congrArg (fun f : C(U.unop.left, Q n) ↦ f x) hn
    let f (x : U.unop.left) : A := (ht x).exists.choose
    have hres (n : ℕ) (x : U.unop.left) : Ideal.Quotient.mk
        (Ideal.span ({p} : Set A) ^ (n + 1)) (f x) = t n x :=
      (ht x).exists.choose_spec n
    have hf : Continuous f := by
      apply continuous_of_residues A p hb f
      intro n
      have h := (IsLocallyConstant.iff_continuous (t n)).mpr (t n).continuous
      exact (show (fun x ↦ Ideal.Quotient.mk
        (Ideal.span ({p} : Set A) ^ (n + 1)) (f x)) = t n from funext (hres n)) ▸ h
    refine ⟨⟨f, hf⟩, ?_⟩
    apply Subtype.ext
    funext n
    apply @ContinuousMap.ext U.unop.left (Q n.unop) _ ⊥
    intro x
    exact hres n.unop x

private def quotientTowerConstantIso (A : Type (u + 1)) [CommRing A] (p : A)
    (T : Scheme.{u}) :
    quotientTower A p ⋙ constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} ≅
      Scheme.adicLisseRingSystem T (Ideal.span ({p} : Set A)) := by
  let η : quotientTower A p ⋙
      constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} ⟶
      Scheme.adicLisseRingSystem T (Ideal.span ({p} : Set A)) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [Functor.comp_map, quotientTower, Scheme.adicLisseRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id, Category.id_comp])
  let : ∀ n, IsIso (η.app n) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
  let := NatIso.isIso_of_isIso_app η
  exact asIso η

private def continuousCompletionIso (A : Type (u + 1)) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [CompactSpace A] [T2Space A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (T : Scheme.{u}) : Scheme.continuousCoefficientSheaf T A ≅
      Scheme.adicLisseCompletedRing T (Ideal.span ({p} : Set A)) := by
  let e := Functor.isoWhiskerLeft (quotientTower A p)
    (Scheme.discreteContinuousCoefficientIso T)
  exact (continuousResidueCone_isLimit A p hb T).conePointsIsoOfNatIso
    (limit.isLimit (Scheme.adicLisseRingSystem T (Ideal.span ({p} : Set A))))
    (e.symm ≪≫ quotientTowerConstantIso A p T)

section ConstantUnit
variable {C D B : Type*} [Category C] [Category D] [Category B]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J B] [HasWeakSheafify K B] [F.IsContinuous J K]
  [∀ P : Cᵒᵖ ⥤ B, F.op.HasPointwiseLeftKanExtension P]

private theorem constantPullback_unit_all {W : C} (hW : IsTerminal W)
    (hFW : IsTerminal (F.obj W)) (M : B) (G : Sheaf J B)
    (a : (constantSheaf J B).obj M ⟶ G) (V : C) :
    ((toSheafify K ((Functor.const Dᵒᵖ).obj M)) ≫
      ((constantPullbackMonoidalIso F J K hW hFW).hom.app M ≫
        (Functor.sheafPullbackConstruction.sheafPullback F B J K).map a).hom).app
          (op (F.obj V)) =
      ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op V) ≫ a.hom.app (op V)) ≫
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F B J K).unit.app G).hom.app
          (op V) := by
  let q := toSheafify K ((Functor.const Dᵒᵖ).obj M) ≫
    ((constantPullbackMonoidalIso F J K hW hFW).hom.app M ≫
      (Functor.sheafPullbackConstruction.sheafPullback F B J K).map a).hom
  let r := (toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫ a.hom) ≫
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F B J K).unit.app G).hom
  have h := constantPullback_unit_map F J K hW hFW M G a
  change q.app (op (F.obj W)) = r.app (op W) at h
  have hq := constant_naturality q (F.map (hW.from V)).op
  have hr := constant_naturality r (hW.from V).op
  change q.app (op (F.obj V)) = r.app (op V)
  rw [← hq, h]
  exact hr
end ConstantUnit

private theorem canonicalAbelianMap_unit (X : Scheme.{u})
    (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (S : Profinite.{u}) (b : ULift.{u + 1} B) :
    (FiniteDiscreteOrdinary.canonicalAbelianMap B X).hom.app
        (op ((profiniteToProEtOf X).obj S))
        ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)))).app
            (op ((profiniteToProEtOf X).obj S)) b) =
      ((pointUpperStarLowerStarAdjunction.comp
        (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).unit.app
          (FiniteDiscreteOrdinary.coefficient B)).hom.app
        (op S) (ULift.up (ContinuousMap.const S b.down)) := by
  let M : Ab.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} B)
  let R := FiniteDiscreteOrdinary.coefficient B
  let e : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj M ⟶ R :=
    ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
      _ R).symm (FiniteDiscreteOrdinary.pointConstants B)
  let a := constantPointIso.hom.app M ≫ pointUpperStar.map e
  have h₁ := constantPullback_unit_all
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X))
    (Scheme.ProEt.topology specZ.{u}) (Scheme.ProEt.topology X)
    (proEtIsTerminal (proEtTerminal specZ.{u}))
    (proEtIsTerminal ((MorphismProperty.Over.pullback @WeaklyEtale ⊤
      (toSpecZ X)).obj (proEtTerminal specZ.{u}))) M (pointUpperStar.obj R) a
        (profiniteToProEt.obj S)
  have h₂ := constantPullback_unit_all profiniteToProEt
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ.{u})
    (terminalIsTerminal (C := Profinite.{u}))
    ((terminalIsTerminal (C := Profinite.{u})).isTerminalObj profiniteToProEt)
    M R e S
  have he := (sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
    _ R |>.apply_symm_apply (FiniteDiscreteOrdinary.pointConstants B)
  rw [Adjunction.homEquiv_unit] at he
  change toSheafify (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj M) ≫ e.hom = _ at he
  have h₃ := congrArg (fun f ↦ f.app (op S)) he
  simp only [NatTrans.comp_app] at h₃
  rw [h₃] at h₂
  change (toSheafify (Scheme.ProEt.topology specZ.{u})
    ((Functor.const specZ.{u}.ProEtᵒᵖ).obj M)).app (op (profiniteToProEt.obj S)) ≫
      a.hom.app (op (profiniteToProEt.obj S)) = _ at h₂
  have h₄ := congrArg (fun f ↦ f ≫
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)) Ab.{u + 1}
      (Scheme.ProEt.topology specZ.{u}) (Scheme.ProEt.topology X)).unit.app
        (pointUpperStar.obj R)).hom.app (op (profiniteToProEt.obj S))) h₂
  have h := congrArg (fun f : M ⟶ _ ↦ f b) (h₁.trans h₄)
  dsimp only [M, R, e] at h
  simp only [FiniteDiscreteOrdinary.canonicalAbelianMap, constantSchemeIso,
    Iso.trans_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.associator_hom_app, Functor.whiskerRight_app,
    a, M, R, e, upperStarFromPoint, upperStarLowerStarAdjunction, Adjunction.comp_unit_app,
    Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp, Category.assoc,
    Category.comp_id,
    CategoryTheory.comp_apply, FiniteDiscreteOrdinary.pointConstants,
    pointUpperStarLowerStarAdjunction, pointLowerStar,
    Functor.sheafPushforwardContinuous_map_hom_app] at h ⊢
  exact h

private theorem comparison_constants
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (T : Scheme.{u}) (U : T.ProEtᵒᵖ) (a : A) :
    (ContinuousRingUniverse.comparison T A).hom.app U
      ((FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app U
        ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U
            (ULift.up a))) = ULift.up (ContinuousMap.const U.unop.left a) := by
  let M := AddCommGrpCat.of (ULift.{u + 1} A)
  let H := ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousCoefficientRingSheaf T A)).obj
  let q : (Functor.const T.ProEtᵒᵖ).obj M ⟶ H :=
    toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj M) ≫
      (FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom ≫
        (ContinuousRingUniverse.comparison T A).hom
  let S := ⊤_ Profinite.{u}
  have ht : IsTerminal ((profiniteToProEtOf T).obj S) := by
    let F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)
    let hS := (terminalIsTerminal (C := Profinite.{u})).isTerminalObj profiniteToProEt
    let e := F.mapIso (hS.uniqueUpToIso (proEtIsTerminal (proEtTerminal specZ.{u})))
    exact (proEtIsTerminal (F.obj (proEtTerminal specZ.{u}))).ofIso e.symm
  have hq : q.app (op ((profiniteToProEtOf T).obj S)) (ULift.up a) =
      ULift.up (ContinuousMap.const ((profiniteToProEtOf T).obj S).left a) := by
    dsimp only [q, NatTrans.comp_app]
    simp only [CategoryTheory.comp_apply]
    dsimp only [M]
    erw [canonicalAbelianMap_unit T A S (ULift.up a)]
    have h := ContinuousRingUniverse.comparison_eq T A S (ContinuousMap.const S a)
    rw [Adjunction.homEquiv_unit] at h
    exact h
  have hn := ConcreteCategory.congr_hom
    (constant_naturality q (ht.from U.unop).op) (ULift.up a)
  change q.app U (ULift.up a) = _
  have hn' : H.map (ht.from U.unop).op (q.app (op ((profiniteToProEtOf T).obj S))
      (ULift.up a)) = q.app U (ULift.up a) := hn
  rw [← hn', hq]
  rfl

private def continuousLiftRingIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (T : Scheme.{u}) : continuousCoefficientRingSheaf T A ≅
      (sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (Scheme.continuousCoefficientSheaf T (ULift.{u + 1} A)) := by
  apply (fullyFaithfulSheafToPresheaf _ _).preimageIso
  refine NatIso.ofComponents (fun U ↦ ?_) (fun f ↦ ?_)
  · change RingCat.of (ULift.{u + 1} C(U.unop.left, A)) ≅
      RingCat.of C(U.unop.left, ULift.{u + 1} A)
    exact RingEquiv.toRingCatIso
      { toFun := fun f ↦ ⟨fun x ↦ ULift.up (f.down x),
          continuous_uliftUp.comp f.down.continuous⟩
        invFun := fun f ↦ ULift.up ⟨fun x ↦ (f x).down,
          continuous_uliftDown.comp f.continuous⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl }
  · apply RingCat.hom_ext
    apply RingHom.ext
    intro f
    apply ContinuousMap.ext
    intro x
    rfl

private def continuousRealizationIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TotallyDisconnectedSpace A] (T : Scheme.{u}) :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) T) ≅
        Scheme.continuousCoefficientSheaf T (ULift.{u + 1} A) := by
  let J := Scheme.ProEt.topology T
  let R : Sheaf J Ab.{u + 1} :=
    condensedRingObj (Profinite.continuousCoefficientRingObj A) T
  let Q : Sheaf J RingCat.{u + 1} := continuousCoefficientRingSheaf T A
  let B : Sheaf J Ab.{u + 1} :=
    (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Q
  let : IsCommMonObj B := Sheaf.isCommMonObj_sheafCompose_obj J Q
    (fun U (a b : ULift.{u + 1} C(U.unop.left, A)) ↦ mul_comm a b)
  let b : R ≅ B := by
    have := ContinuousRingUniverse.comparison_isIso T A
    exact asIso (ContinuousRingUniverse.comparison T A)
  let : IsMonHom b.hom := ContinuousRingUniverse.comparison_isMonHom T A
  let : IsMonHom b.inv := inferInstance
  let c : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J B :=
    { hom := CondensedRing.sectionRingMap T b.hom
      inv := CondensedRing.sectionRingMap T b.inv
      hom_inv_id := by
        ext V x
        exact congrArg (fun f : R ⟶ R ↦ f.hom.app V x) b.hom_inv_id
      inv_hom_id := by
        ext V x
        exact congrArg (fun f : B ⟶ B ↦ f.hom.app V x) b.inv_hom_id }
  let F := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let hF : F.FullyFaithful := fullyFaithfulSheafCompose J
    CommRingCat.fullyFaithfulForget₂ToRingCat.{u + 1}
  exact hF.preimageIso
    (X := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R)
    (Y := Scheme.continuousCoefficientSheaf T (ULift.{u + 1} A))
    (F.mapIso c ≪≫ CondensedRing.reconstructedRingIso T Q ≪≫ continuousLiftRingIso A T)

private theorem continuousRealizationIso_constants
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TotallyDisconnectedSpace A] (T : Scheme.{u}) (U : T.ProEtᵒᵖ) (a : A) :
    (continuousRealizationIso A T).hom.hom.app U
      ((FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app U
        ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U
            (ULift.up a))) = ContinuousMap.const U.unop.left (ULift.up a) := by
  change (⟨fun x ↦ ULift.up (((ContinuousRingUniverse.comparison T A).hom.app U
    ((FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app U
      ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U
          (ULift.up a)))).down x),
      continuous_uliftUp.comp (ContinuousMap.continuous _)⟩ :
        C(U.unop.left, ULift.{u + 1} A)) = _
  rw [comparison_constants]
  rfl

private theorem continuousCompletionIso_constants
    (A : Type (u + 1)) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CompactSpace A] [T2Space A] (p : A)
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (T : Scheme.{u}) (U : T.ProEtᵒᵖ) (a : A) (n : ℕ) :
    (limit.π (Scheme.adicLisseRingSystem T (Ideal.span ({p} : Set A))) (op n)).hom.app U
      ((continuousCompletionIso A p hb T).hom.hom.app U (ContinuousMap.const _ a)) =
    (toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (A ⧸ Ideal.span ({p} : Set A) ^ (n + 1))))).app U
        (Ideal.Quotient.mk _ a) := by
  let Q := A ⧸ Ideal.span ({p} : Set A) ^ (n + 1)
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  have : IsIso (Scheme.continuousCoefficientConstantComparison T Q) :=
    Scheme.continuousCoefficientConstantComparison_isIso T Q
  apply (ConcreteCategory.bijective_of_isIso
    ((Scheme.continuousCoefficientConstantComparison T Q).hom.app U)).1
  have h := (continuousResidueCone_isLimit A p hb T).conePointsIsoOfNatIso_hom_comp
    (limit.isLimit (Scheme.adicLisseRingSystem T (Ideal.span ({p} : Set A))))
    ((Functor.isoWhiskerLeft (quotientTower A p)
      (Scheme.discreteContinuousCoefficientIso T)).symm ≪≫ quotientTowerConstantIso A p T)
        (op n)
  have h' := congrArg (fun f ↦ f ≫ Scheme.continuousCoefficientConstantComparison T Q) h
  have hu := Scheme.continuousCoefficientConstantComparison_unit T Q
  have hv := ConcreteCategory.congr_hom (congr_app hu U) (Ideal.Quotient.mk
    (Ideal.span ({p} : Set A) ^ (n + 1)) a)
  dsimp only [continuousCompletionIso] at *
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, quotientTowerConstantIso,
    asIso_hom, NatTrans.ofOpSequence_app, Category.comp_id,
    Scheme.discreteContinuousCoefficientIso, NatIso.ofComponents_inv_app,
    asIso_inv, Category.assoc, Category.comp_id] at h'
  change _ = (continuousResidueCone A p hb T).π.app (op n) ≫
    inv (Scheme.continuousCoefficientConstantComparison T Q) ≫
      Scheme.continuousCoefficientConstantComparison T Q at h'
  rw [IsIso.inv_hom_id, Category.comp_id] at h'
  have hh := congrArg
    (fun f : Scheme.continuousCoefficientSheaf T A ⟶
      Scheme.continuousCoefficientSheaf T Q ↦ f.hom.app U (ContinuousMap.const _ a)) h'
  exact hh.trans hv.symm

/-- A compact separated principal-adic domain is realized by its positive finite quotient
constant sheaves, uniquely with the prescribed constant scalars.

Bhatt--Scholze, Lemmas 4.2.12 and 6.8.2(1)
(auxiliary; not a blueprint node).

Proof: The quotient fibres are open by the given neighborhood basis. Each finite
quotient's continuous-function sheaf is canonically its constant sheaf, by gluing on
these open fibres, including the empty object. Compatible residues have a unique lift
in A: compactness intersects the nested nonempty closed cosets, and the Hausdorff
neighborhood basis separates points. The coordinate maps and their inverse are
continuous, since the same cosets are a neighborhood basis. Thus continuous A-valued
functions are the sectionwise inverse limit of finite continuous quotient functions.
The canonical continuous-ring realization identifies these functions with the actual
pulled-back coefficient ring and carries scalar constants to constant functions.
This constructs the normalized comparison as a ring isomorphism. For uniqueness,
fix n and restrict a continuous function to the open fibres of its n-th residue.
On such a fibre choose a scalar lift a. The difference from a is p^(n+1) times a
continuous function: multiplication by this nonzero power embeds compact A in the
Hausdorff space A, and its inverse onto its image is continuous. Every normalized
ring map to the n-th quotient therefore takes the original function to the residue
of a. Hence two candidates have equal finite projections locally, and thus globally.
Joint monicity of the limit projections gives equality of the ring isomorphisms. -/
theorem compact_adic_continuous_identification
    (A : Type u) [CommRing A] [IsDomain A] [TopologicalSpace A] [IsTopologicalRing A]
    [CompactSpace A] [T2Space A] (p : A) (hp : p ≠ 0)
    (hf : ∀ n : ℕ, Finite (A ⧸ Ideal.span ({p} : Set A) ^ (n + 1)))
    (hb : ∀ x : A, (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
      {y | Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) y =
        Ideal.Quotient.mk (Ideal.span ({p} : Set A) ^ (n + 1)) x}))
    (T : Scheme.{u}) :
    (∃! e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) T) ≅
    Scheme.adicLisseCompletedRing T
      (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))),
    ∀ (U : T.ProEtᵒᵖ) (a : A) (n : ℕ),
      ((limit.π (Scheme.adicLisseRingSystem T
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)))) (op n)).hom.app U)
        ((e.hom.hom.app U)
          ((FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app U
            ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).obj
                (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} A)))).app U (ULift.up a)))) =
      (toSheafify (D := CommRingCat.{u + 1}) (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
          (ULift.{u + 1} A ⧸
            (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))) ^ (n + 1))))).app U
          (Ideal.Quotient.mk
            ((Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))) ^ (n + 1))
            (ULift.up a))) := by
  classical
  have _ := hf
  let B := ULift.{u + 1} A
  let : IsDomain B := MulEquiv.isDomain A ULift.ringEquiv.toMulEquiv
  let b : B := ULift.up p
  have hb' := ulift_basis A p hb
  let : TotallyDisconnectedSpace A := totallyDisconnected_of_basis A p hb
  let r := continuousRealizationIso A T
  let c := continuousCompletionIso B b hb' T
  let e := r ≪≫ c
  have he : ∀ (U : T.ProEtᵒᵖ) (a : A) (n : ℕ),
      (limit.π (Scheme.adicLisseRingSystem T (Ideal.span ({b} : Set B))) (op n)).hom.app U
        (e.hom.hom.app U ((FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app U
          ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of B))).app U (ULift.up a)))) =
      (toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (B ⧸ Ideal.span ({b} : Set B) ^ (n + 1))))).app U
          (Ideal.Quotient.mk _ (ULift.up a)) := by
    intro U a n
    change (limit.π (Scheme.adicLisseRingSystem T (Ideal.span ({b} : Set B)))
      (op n)).hom.app U
      (c.hom.hom.app U (r.hom.hom.app U _)) = _
    rw [continuousRealizationIso_constants]
    exact continuousCompletionIso_constants B b hb' T U (ULift.up a) n
  refine ⟨e, he, ?_⟩
  intro d hd
  have hr (U : T.ProEtᵒᵖ) (a : B) :
      r.inv.hom.app U (ContinuousMap.const U.unop.left a) =
        (FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app U
          ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of B))).app U a) := by
    have h := congrArg (fun f ↦ f.hom.app U
      ((FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app U
        ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of B))).app U a))) r.hom_inv_id
    change r.inv.hom.app U (r.hom.hom.app U _) = _ at h
    rw [continuousRealizationIso_constants A T U a.down] at h
    exact h
  apply Iso.ext
  apply (cancel_epi r.inv).mp
  apply limit.hom_ext
  intro n
  let φ := r.inv ≫ d.hom ≫ limit.π
    (Scheme.adicLisseRingSystem T (Ideal.span ({b} : Set B))) n
  let ψ := c.hom ≫ limit.π
    (Scheme.adicLisseRingSystem T (Ideal.span ({b} : Set B))) n
  have hs : ∀ (U : T.ProEtᵒᵖ) (a : B),
      φ.hom.app U (ContinuousMap.const U.unop.left a) =
        ψ.hom.app U (ContinuousMap.const U.unop.left a) := by
    intro U a
    change (limit.π (Scheme.adicLisseRingSystem T (Ideal.span ({b} : Set B))) n).hom.app U
      (d.hom.hom.app U
      (r.inv.hom.app U (ContinuousMap.const U.unop.left a))) = _
    rw [hr]
    exact (hd U a.down n.unop).trans
      (continuousCompletionIso_constants B b hb' T U a n.unop).symm
  have hk : ∀ U : T.ProEtᵒᵖ,
      φ.hom.app U (ContinuousMap.const U.unop.left b) ^ (n.unop + 1) = 0 := by
    intro U
    rw [hs]
    have h := continuousCompletionIso_constants B b hb' T U b n.unop
    change ψ.hom.app U (ContinuousMap.const U.unop.left b) = _ at h
    rw [h]
    change ((toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (B ⧸ Ideal.span ({b} : Set B) ^ (n.unop + 1))))).app U)
        (Ideal.Quotient.mk _ b) ^ (n.unop + 1) = 0
    rw [← map_pow]
    have hz : Ideal.Quotient.mk (Ideal.span ({b} : Set B) ^ (n.unop + 1))
        (b ^ (n.unop + 1)) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [Ideal.span_singleton_pow]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hpow := map_pow
      (Ideal.Quotient.mk (Ideal.span ({b} : Set B) ^ (n.unop + 1))) b (n.unop + 1)
    rw [← hpow, hz, map_zero]
  have h := continuousFiniteQuotientHom_ext B b
    (by exact fun h ↦ hp (congrArg ULift.down h)) hb' T n.unop _ φ ψ hs hk
  change r.inv ≫ d.hom ≫ limit.π _ n = r.inv ≫ e.hom ≫ limit.π _ n
  rw [← Category.assoc r.inv e.hom, show r.inv ≫ e.hom = c.hom by simp [e]]
  exact h

end AlgebraicGeometry.ProEtale
