import Langlands.BaseChange.SigmaDiscreteSeriesOrbitDecompositionStatement
import Langlands.BaseChange.NormalizedProductEntrywiseAut
import Langlands.BaseChange.TwistedCharacter.StableLanglandsData
import Langlands.BaseChange.SigmaOrbitConjugates
import Langlands.Combinatorics.FiniteOccurrenceMatching
import Langlands.LocalField.CharZeroPadicRealization
import Langlands.LocalField.PadicBridge
import Langlands.AllField.Representation.Induction.BlockEquivalence
import Langlands.AllField.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.Category.UniverseLiftPadic
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.Representation.Classification.TemperedBlockExhaustionProof
import Langlands.Representation.Classification.TemperedBlockUniquenessProof
import Langlands.Representation.Induction.BlockInducingRecovery
import Langlands.Representation.Parabolic.FlattenedProductInduction
import Mathlib.Dynamics.PeriodicPts.Defs

/-! # Orbit decomposition of σ-discrete series -/

noncomputable section

set_option autoImplicit false

namespace Langlands.BaseChange

open CategoryTheory GeneralLinear Geometric TopologicalSpace
open scoped BigOperators

universe u v uW

/-- The multiset of a finite family, counting all occurrences. -/
private def occurrences {α : Type*} {k : ℕ} (a : Fin k → α) : Multiset α := List.ofFn a

private theorem occurrences_map {α β : Type*} {k : ℕ} (f : α → β) (a : Fin k → α) :
    (occurrences a).map f = occurrences (f ∘ a) := by
  simp only [occurrences, Multiset.map_coe, List.map_ofFn]

private theorem occurrences_sum {α : Type*} {k : ℕ} (a : Fin k → α) :
    occurrences a = ∑ i, ({a i} : Multiset α) := by
  rw [← Multiset.sum_map_singleton (occurrences a), occurrences_map]
  simp only [occurrences, Multiset.sum_coe, List.sum_ofFn, Function.comp_apply]

private theorem occurrences_mem {α : Type*} {k : ℕ} {a : Fin k → α} {x : α} :
    x ∈ occurrences a ↔ ∃ i, a i = x := by
  simp only [occurrences, Multiset.mem_coe, List.mem_ofFn]

private theorem occurrences_congr {α : Type*} {k j : ℕ} {a : Fin k → α} {b : Fin j → α}
    (e : Fin k ≃ Fin j) (h : ∀ i, a i = b (e i)) : occurrences a = occurrences b := by
  rw [occurrences_sum, occurrences_sum]
  exact Fintype.sum_equiv e _ _ fun i => congrArg (fun x => ({x} : Multiset α)) (h i)

private theorem orbit_occurrences_map {α : Type*} (f : α → α) (x : α) {t : ℕ}
    (hfix : f^[t] x = x) :
    (occurrences fun i : Fin t => f^[i.val] x).map f =
      occurrences (fun i : Fin t => f^[i.val] x) := by
  cases t with
  | zero => simp [occurrences]
  | succ t =>
    let a (i : Fin (t + 1)) := f^[i.val] x
    have h (i : Fin (t + 1)) : f (a i) = a (finRotate (t + 1) i) := by
      change f (f^[i.val] x) = f^[(finRotate (t + 1) i).val] x
      rw [← Function.iterate_succ_apply' (f := f) (n := i.val) x]
      by_cases hi : i = Fin.last t
      · simpa only [hi, Fin.val_last, finRotate_last, Fin.val_zero,
          Function.iterate_zero_apply] using hfix
      · rw [coe_finRotate_of_ne_last hi]
    rw [occurrences_map]
    exact occurrences_congr (finRotate (t + 1)) h

private theorem orbit_submultiset {α : Type*} (f : α → α) (x : α)
    (M : Multiset α) (hM : M.map f = M) (hx : x ∈ M) :
    let O := occurrences (fun i : Fin (Function.minimalPeriod f x) => f^[i.val] x)
    ∃ R : Multiset α, M = O + R ∧ O.map f = O ∧ R.map f = R := by
  intro O
  have hO : O.map f = O := orbit_occurrences_map f x (Function.iterate_minimalPeriod)
  have hnodup : O.Nodup := Multiset.coe_nodup.mpr (List.nodup_ofFn.mpr fun i j h =>
    Fin.ext ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp h))
  have hmem (k : ℕ) : f^[k] x ∈ M := by
    induction k with
    | zero => exact hx
    | succ k ih =>
      rw [Function.iterate_succ_apply', ← hM]
      exact Multiset.mem_map_of_mem f ih
  have hle : O ≤ M := (Multiset.le_iff_subset hnodup).mpr fun _ hy => by
    obtain ⟨i, rfl⟩ := occurrences_mem.mp hy
    exact hmem i.val
  obtain ⟨R, hR⟩ := Multiset.le_iff_exists_add.mp hle
  refine ⟨R, hR, hO, add_left_cancel (a := O) ?_⟩
  calc
    O + R.map f = M.map f := by rw [hR, Multiset.map_add, hO]
    _ = O + R := hM.trans hR

section Padic

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{v} p} (T : K.TopologicalData)

private abbrev BlockObject (r : ℕ) :=
  letI := T.topology
  SmoothRep.{0,v,max v uW} ℂ (GeneralLinear r K.Carrier)

/-- The isomorphism class of a smooth block together with its rank. -/
private abbrev BlockClass :=
  letI := T.topology
  Σ r : ℕ, SmoothRep.IsoClass.{0,v,max v uW} ℂ (GeneralLinear r K.Carrier)

private def blockClass {r : ℕ} (A : BlockObject.{v,uW} T r) : BlockClass.{v,uW} T := by
  let := T.topology
  exact ⟨r, A.isoClass⟩

private theorem blockClass_eq_iff {r s : ℕ}
    (A : BlockObject.{v,uW} T r) (C : BlockObject.{v,uW} T s) :
    blockClass T A = blockClass T C ↔ ∃ h : r = s, Nonempty ((h ▸ A) ≅ C) := by
  let := T.topology
  constructor
  · intro h
    have hr := congrArg Sigma.fst h
    change r = s at hr
    subst s
    exact ⟨rfl, (SmoothRep.isoClass_eq_iff _ _).mp (eq_of_heq (Sigma.mk.inj_iff.mp h).2)⟩
  · rintro ⟨h, e⟩
    subst s
    exact congrArg (Sigma.mk r) ((SmoothRep.isoClass_eq_iff _ _).mpr e)

/-- Actual square-integrable inducing blocks, with the conditions for tempered uniqueness. -/
private structure DiscreteBlocks (n : ℕ) where
  shape : BlockShape n
  blocks : ∀ i, BlockObject.{v,uW} T (shape.size i)
  properties : letI := T.topology
    ∀ i, (blocks i).IsIrreducible ∧ T.IsSquareIntegrable (blocks i).representation ∧
      IsUnitarizable (blocks i).representation

variable {T}

private abbrev DiscreteBlocks.product {n : ℕ} (D : DiscreteBlocks.{v,uW} T n) :
    BlockObject.{v,uW} T n := (T.normalizedProductInductionFunctor D.shape).obj D.blocks

private def DiscreteBlocks.classes {n : ℕ} (D : DiscreteBlocks.{v,uW} T n) :
    Multiset (BlockClass.{v,uW} T) := occurrences (fun i => blockClass T (D.blocks i))

private theorem DiscreteBlocks.sum_ranks {n : ℕ} (D : DiscreteBlocks.{v,uW} T n) :
    (D.classes.map Sigma.fst).sum = n := by
  rw [DiscreteBlocks.classes, occurrences_map]
  change (List.ofFn D.shape.size : Multiset ℕ).sum = n
  rw [Multiset.sum_coe, List.sum_ofFn, D.shape.sum_eq]

private theorem DiscreteBlocks.product_iso_iff {n : ℕ} (hn : 0 < n)
    (D C : DiscreteBlocks.{v,uW} T n) :
    Nonempty (D.product ≅ C.product) ↔ D.classes = C.classes := by
  let := T.topology
  rw [Classification.temperedBlockUniqueness.{v,uW} K T n hn D.shape C.shape
    D.blocks C.blocks D.properties C.properties]
  constructor
  · rintro ⟨e, h, he⟩
    exact occurrences_congr e fun i => (blockClass_eq_iff T _ _).mpr ⟨h i, he i⟩
  · intro h
    obtain ⟨e, he⟩ := Combinatorics.exists_equiv_of_ofFn_multiset_eq _ _ h
    choose hr hi using fun i => (blockClass_eq_iff T (D.blocks i) (C.blocks (e i))).mp (he i)
    exact ⟨e, hr, hi⟩

variable {F : Type u} [Field F] [TopologicalSpace F] [Algebra F K.Carrier]
  (hModule : letI := T.topology; IsModuleTopology F K.Carrier)

variable (T)

private def galoisAut (σ : K.Carrier ≃ₐ[F] K.Carrier) (r : ℕ) :
    letI := T.topology
    GeneralLinear r K.Carrier ≃ₜ* GeneralLinear r K.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  exact fieldEquiv r σ.toRingEquiv (continuous_algEquiv σ) (continuous_algEquiv σ.symm)

private def pullBlock (σ : K.Carrier ≃ₐ[F] K.Carrier) {r : ℕ}
    (A : BlockObject.{v,uW} T r) : BlockObject.{v,uW} T r := by
  let := T.topology
  exact SmoothRep.pullback (galoisAut T hModule σ r) A

private def pullClass (σ : K.Carrier ≃ₐ[F] K.Carrier) :
    BlockClass.{v,uW} T → BlockClass.{v,uW} T := by
  let := T.topology
  intro c
  refine ⟨c.1, Quotient.liftOn c.2 (fun A => (pullBlock T hModule σ A).isoClass) ?_⟩
  intro A C h
  change Nonempty (A ≅ C) at h
  obtain ⟨e⟩ := h
  exact (SmoothRep.isoClass_eq_iff _ _).mpr
    ⟨(SmoothRep.pullbackFunctor (galoisAut T hModule σ c.1)).mapIso e⟩

private theorem pullClass_blockClass (σ : K.Carrier ≃ₐ[F] K.Carrier) {r : ℕ}
    (A : BlockObject.{v,uW} T r) : pullClass T hModule σ (blockClass T A) =
      blockClass T (pullBlock T hModule σ A) := rfl

private theorem pullBlock_representation (σ : K.Carrier ≃ₐ[F] K.Carrier) {r : ℕ}
    (A : BlockObject.{v,uW} T r) :
    letI := T.topology
    (pullBlock T hModule σ A).representation =
      A.representation.comp (entrywiseAut σ r).toMonoidHom := rfl

set_option maxHeartbeats 650000 in
private theorem pullClass_iterate (σ : K.Carrier ≃ₐ[F] K.Carrier) {r : ℕ}
    (A : BlockObject.{v,uW} T r) (i : ℕ) :
    (pullClass T hModule σ)^[i] (blockClass T A) =
      blockClass T (pullBlock T hModule (σ ^ i) A) := by
  let := T.topology
  induction i with
  | zero =>
    rw [Function.iterate_zero_apply]
    apply (blockClass_eq_iff T A _).mpr
    refine ⟨rfl, ⟨SmoothRep.mkIso (equivOfRepresentationEq ?_)⟩⟩
    rw [pullBlock_representation]
    apply MonoidHom.ext
    intro g
    simp only [pow_zero, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, entrywiseAut_one_apply]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, pullClass_blockClass]
    apply (blockClass_eq_iff T _ _).mpr
    refine ⟨rfl, ⟨SmoothRep.mkIso (equivOfRepresentationEq ?_)⟩⟩
    simp only [pullBlock_representation, pow_succ]
    exact comp_entrywiseAut_mul A.representation (σ ^ i) σ

private theorem isPeriodicPt_blockClass_iff (σ : K.Carrier ≃ₐ[F] K.Carrier) {r : ℕ}
    (A : BlockObject.{v,uW} T r) (i : ℕ) :
    letI := T.topology
    Function.IsPeriodicPt (pullClass T hModule σ) i (blockClass T A) ↔
      Nonempty (A.representation.Equiv
        (A.representation.comp (entrywiseAut (σ ^ i) r).toMonoidHom)) := by
  let := T.topology
  change (pullClass T hModule σ)^[i] (blockClass T A) = blockClass T A ↔ _
  rw [pullClass_iterate, blockClass_eq_iff]
  constructor
  · rintro ⟨h, ⟨e⟩⟩
    cases h
    exact ⟨(SmoothRep.equivOfIso e).symm⟩
  · rintro ⟨e⟩
    exact ⟨rfl, ⟨SmoothRep.mkIso e.symm⟩⟩

variable {T}

private theorem DiscreteBlocks.pull_properties {n : ℕ} (D : DiscreteBlocks.{v,uW} T n)
    (σ : K.Carrier ≃ₐ[F] K.Carrier) (i : Fin D.shape.length) :
    letI := T.topology
    (pullBlock T hModule σ (D.blocks i)).IsIrreducible ∧
      T.IsSquareIntegrable (pullBlock T hModule σ (D.blocks i)).representation ∧
      IsUnitarizable (pullBlock T hModule σ (D.blocks i)).representation := by
  let := T.topology
  let e := galoisAut T hModule σ (D.shape.size i)
  obtain ⟨hi, hsq, hu⟩ := D.properties i
  exact ⟨(isIrreducible_comp_continuousMulEquiv_iff _ e).mpr hi,
    T.isSquareIntegrable_comp_continuousMulEquiv _ e hsq, hu.comp e.toMonoidHom⟩

private def DiscreteBlocks.pull {n : ℕ} (D : DiscreteBlocks.{v,uW} T n)
    (σ : K.Carrier ≃ₐ[F] K.Carrier) : DiscreteBlocks.{v,uW} T n :=
  ⟨D.shape, fun i => pullBlock T hModule σ (D.blocks i), D.pull_properties hModule σ⟩

private theorem DiscreteBlocks.pull_classes {n : ℕ} (D : DiscreteBlocks.{v,uW} T n)
    (σ : K.Carrier ≃ₐ[F] K.Carrier) :
    (D.pull hModule σ).classes = D.classes.map (pullClass T hModule σ) := by
  rw [DiscreteBlocks.classes, DiscreteBlocks.classes, occurrences_map]
  rfl

set_option maxHeartbeats 650000 in
private def DiscreteBlocks.pull_product_equiv {n : ℕ} (D : DiscreteBlocks.{v,uW} T n)
    (σ : K.Carrier ≃ₐ[F] K.Carrier) :
    letI := T.topology
    Representation.Equiv (D.product.representation.comp (entrywiseAut σ n).toMonoidHom)
      (D.pull hModule σ).product.representation := by
  let := T.topology
  let C := D.pull hModule σ
  change Representation.Equiv
    (((T.normalizedProductInductionFunctor D.shape).obj D.blocks).representation.comp
      (entrywiseAut σ n).toMonoidHom)
    ((T.normalizedProductInductionFunctor C.shape).obj C.blocks).representation
  rw [T.normalizedProductInductionFunctor_obj, T.normalizedProductInductionFunctor_obj]
  let ρ := fun i => (D.blocks i).representation
  let ρ' := fun i => ρ i |>.comp (entrywiseAut σ (D.shape.size i)).toMonoidHom
  have hρ : (fun i => (C.blocks i).representation) = ρ' :=
    funext fun i => pullBlock_representation T hModule σ (D.blocks i)
  exact Eq.mpr (congrArg (fun A => Representation.Equiv
    ((T.normalizedProductInduced D.shape ρ).comp (entrywiseAut σ n).toMonoidHom)
    (T.normalizedProductInduced D.shape A)) hρ)
    (normalizedProductEntrywisePullbackEquiv T hModule σ D.shape ρ).symm

private theorem DiscreteBlocks.stable_iff {n : ℕ} (hn : 0 < n) (D : DiscreteBlocks.{v,uW} T n)
    (σ : K.Carrier ≃ₐ[F] K.Carrier) :
    letI := T.topology
    IsSigmaStable σ n D.product.representation ↔ D.classes.map (pullClass T hModule σ) = D.classes := by
  let := T.topology
  rw [← D.pull_classes hModule σ, eq_comm, ← DiscreteBlocks.product_iso_iff hn D (D.pull hModule σ)]
  constructor
  · rintro ⟨e⟩
    exact ⟨SmoothRep.mkIso (e.trans (D.pull_product_equiv hModule σ))⟩
  · rintro ⟨e⟩
    exact ⟨(SmoothRep.equivOfIso e).trans (D.pull_product_equiv hModule σ).symm⟩

private def DiscreteBlocks.orbit {n : ℕ} (D : DiscreteBlocks.{v,uW} T n)
    (σ : K.Carrier ≃ₐ[F] K.Carrier) (j : Fin D.shape.length) (t : ℕ) :
    DiscreteBlocks.{v,uW} T (t * D.shape.size j) :=
  ⟨BlockShape.uniform t _ (D.shape.positive j),
    fun i => pullBlock T hModule (σ ^ i.val) (D.blocks j),
    fun i => D.pull_properties hModule (σ ^ i.val) j⟩

private theorem DiscreteBlocks.orbit_classes {n : ℕ} (D : DiscreteBlocks.{v,uW} T n)
    (σ : K.Carrier ≃ₐ[F] K.Carrier) (j : Fin D.shape.length) (t : ℕ) :
    (D.orbit hModule σ j t).classes =
      occurrences (fun i : Fin t => (pullClass T hModule σ)^[i.val] (blockClass T (D.blocks j))) := by
  unfold DiscreteBlocks.classes
  congr 1
  funext i
  exact (pullClass_iterate T hModule σ (D.blocks j) i.val).symm

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency.types false in
private def DiscreteBlocks.orbit_product_equiv {n : ℕ} (D : DiscreteBlocks.{v,uW} T n)
    (σ : K.Carrier ≃ₐ[F] K.Carrier) (j : Fin D.shape.length) (t : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    (D.orbit hModule σ j t).product.representation.Equiv
      (sigmaOrbitProduct σ t (D.shape.positive j) (D.blocks j).representation) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let B := BlockShape.uniform t _ (D.shape.positive j)
  let ρ (i : Fin B.length) := (D.blocks j).representation.comp
    (entrywiseAut (σ ^ i.val) (D.shape.size j)).toMonoidHom
  let L := LocalFieldData.ofInstances K.Carrier
  let I : BlockObject.{v,uW} T (t * D.shape.size j) :=
    SmoothRep.of (L.normalizedProductInduced B ρ) (L.isSmooth_normalizedProductInduced B ρ)
  have hI : (D.orbit hModule σ j t).product = I := by rfl
  exact SmoothRep.equivOfIso (eqToIso hI)

private theorem DiscreteBlocks.product_equiv_of_classes_eq {r s : ℕ} (hr : 0 < r)
    (D : DiscreteBlocks.{v,uW} T r) (C : DiscreteBlocks.{v,uW} T s) (h : s = r)
    (hM : D.classes = C.classes) :
    letI := T.topology
    Nonempty (D.product.representation.Equiv (C.product.representation.comp
      (GeneralLinear.reindex (R := K.Carrier) (finCongr h)).symm.toMonoidHom)) := by
  let := T.topology
  subst s
  obtain ⟨e⟩ := (DiscreteBlocks.product_iso_iff hr D C).mpr hM
  exact ⟨(SmoothRep.equivOfIso e).trans (equivOfRepresentationEq (by
    rw [GeneralLinear.reindex_finCongr_rfl]
    rfl))⟩

set_option maxHeartbeats 850000 in
/-- An invariant split of the block multiset yields a two-block normalized induction
whose two inner products are separately σ-stable. -/
private theorem DiscreteBlocks.regroup {n : ℕ} (hn : 0 < n) (D : DiscreteBlocks.{v,uW} T n)
    (σ : K.Carrier ≃ₐ[F] K.Carrier) (M₀ M₁ : Multiset (BlockClass.{v,uW} T))
    (hM : D.classes = M₀ + M₁) (h₀ : M₀ ≠ 0) (h₁ : M₁ ≠ 0)
    (hs₀ : M₀.map (pullClass T hModule σ) = M₀) (hs₁ : M₁.map (pullClass T hModule σ) = M₁) :
    letI := T.topology
    ∃ (B : BlockShape n) (_ : 2 ≤ B.length)
      (A : ∀ i, BlockObject.{v,uW} T (B.size i)),
      (∀ i, IsSigmaStable σ (B.size i) (A i).representation) ∧
      Nonempty (D.product ≅ (T.normalizedProductInductionFunctor B).obj A) := by
  classical
  let := T.topology
  let M : Fin 2 → Multiset (BlockClass.{v,uW} T) := ![M₀, M₁]
  have hne (i : Fin 2) : M i ≠ 0 := by fin_cases i <;> assumption
  have hstable (i : Fin 2) : (M i).map (pullClass T hModule σ) = M i := by
    fin_cases i <;> assumption
  have hle (i : Fin 2) : M i ≤ D.classes := by
    rw [hM]
    fin_cases i
    · exact le_add_of_nonneg_right bot_le
    · exact le_add_of_nonneg_left bot_le
  let L (i : Fin 2) := (M i).toList
  have hselection (i : Fin 2) (j : Fin (L i).length) :
      ∃ k : Fin D.shape.length, blockClass T (D.blocks k) = (L i).get j := by
    apply occurrences_mem.mp
    apply Multiset.mem_of_le (hle i)
    exact Multiset.mem_toList.mp (List.get_mem _ _)
  choose k hk using hselection
  let r (i : Fin 2) := ∑ j, D.shape.size (k i j)
  have hr (i : Fin 2) : 0 < r i := by
    let j : Fin (L i).length := ⟨0, List.length_pos_iff_ne_nil.mpr
      (fun h => hne i (Multiset.toList_eq_nil.mp h))⟩
    apply (D.shape.positive (k i j)).trans_le
    change D.shape.size (k i j) ≤ ∑ j', D.shape.size (k i j')
    exact Finset.single_le_sum (f := fun j' => D.shape.size (k i j'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let C (i : Fin 2) : DiscreteBlocks.{v,uW} T (r i) :=
    ⟨⟨(L i).length, fun j => D.shape.size (k i j), fun j => D.shape.positive (k i j), rfl⟩,
      fun j => D.blocks (k i j), fun j => D.properties (k i j)⟩
  have hC (i : Fin 2) : (C i).classes = M i := by
    calc
      (C i).classes = occurrences ((L i).get) := congrArg occurrences (funext (hk i))
      _ = M i := by rw [occurrences, List.ofFn_get, Multiset.coe_toList]
  have hsum : ∑ i, r i = n := by
    rw [Fin.sum_univ_two, ← (C 0).sum_ranks, ← (C 1).sum_ranks, hC, hC]
    change (M₀.map Sigma.fst).sum + (M₁.map Sigma.fst).sum = n
    simpa only [hM, Multiset.map_add, Multiset.sum_add] using D.sum_ranks
  let B : BlockShape n := ⟨2, r, hr, hsum⟩
  let S : BlockRefinement B := fun i => (C i).shape
  let A (i : Fin B.length) (j : Fin (S i).length) := (C i).blocks j
  let Dflat : DiscreteBlocks.{v,uW} T n :=
    ⟨B.flatten S, Parabolic.flattenedSmoothFamily K T B S A,
      fun j => (C ((B.flattenBlockEquiv S).symm j).1).properties
        ((B.flattenBlockEquiv S).symm j).2⟩
  have hflat : Dflat.classes = M₀ + M₁ := by
    calc
      Dflat.classes = ∑ q : (i : Fin B.length) × Fin (S i).length,
          ({blockClass T (A q.1 q.2)} : Multiset (BlockClass.{v,uW} T)) := by
        rw [DiscreteBlocks.classes, occurrences_sum]
        exact Fintype.sum_equiv (B.flattenBlockEquiv S).symm _ _ fun _ => rfl
      _ = ∑ i : Fin B.length, ∑ j : Fin (S i).length,
          ({blockClass T (A i j)} : Multiset (BlockClass.{v,uW} T)) :=
        Fintype.sum_sigma' fun i j => {blockClass T (A i j)}
      _ = ∑ i : Fin 2, (C i).classes := by
        exact Finset.sum_congr rfl fun i _ => (occurrences_sum _).symm
      _ = M₀ + M₁ := by
        rw [Fin.sum_univ_two, hC, hC]
        rfl
  obtain ⟨eflat⟩ := (DiscreteBlocks.product_iso_iff hn D Dflat).mpr (hM.trans hflat.symm)
  have hi (i : Fin B.length) : IsSigmaStable σ (B.size i) (C i).product.representation :=
    (DiscreteBlocks.stable_iff hModule (hr i) (C i) σ).mpr (by rw [hC]; exact hstable i)
  let estages := Parabolic.flattenedProductInducedEquiv K T B S A
  exact ⟨B, le_rfl, fun i => (C i).product, hi, ⟨eflat ≪≫ SmoothRep.mkIso estages⟩⟩

end Padic

section Exclusion

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [TopologicalSpace E] [ValuativeRel E]
  [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]

set_option maxHeartbeats 750000 in
/-- Move the invariant half-modulus into the Levi action, then realize that action
in the carrier universe used by the exclusion in σ-discreteness. -/
private theorem false_of_proper_stable_product (σ : E ≃ₐ[F] E) {n : ℕ}
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear n E) W) (hP : IsSigmaDiscreteSeries σ n P)
    (B : BlockShape n) (hB : 2 ≤ B.length)
    {V : Fin B.length → Type (max v uW)} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (V i))
    (hρ : ∀ i, IsSmooth (ρ i)) (hσ : ∀ i, IsSigmaStable σ (B.size i) (ρ i))
    (e : P.Equiv ((LocalFieldData.ofInstances E).normalizedProductInduced B ρ)) : False := by
  classical
  let T := LocalFieldData.ofInstances E
  have := T.generalLinearTopologicalGroup n
  have := T.leviTopologicalGroup B
  let δ := T.leviHalfModulus B
  let Ξ := B.blockTensor ρ
  let Ξδ := twist δ Ξ
  have hΞ : IsSmooth Ξ := FiniteTensor.isSmooth_external ρ hρ
  have hΞδ : IsSmooth Ξδ := (isSmooth_twist_iff _ _ (T.isOpen_ker_leviHalfModulus B)).mpr hΞ
  have hδ : δ.comp (leviAut σ B).toMonoidHom = δ := by
    apply MonoidHom.ext
    intro m
    apply Units.ext
    simp only [δ, T, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      LocalFieldData.leviHalfModulus_apply, leviModulus_leviAut]
  have hΞσ : IsLeviSigmaStable σ B Ξ := by
    let a := FiniteTensor.congrEquiv (fun i =>
      BinaryTensor.compEquiv (hσ i).some (Pi.evalMonoidHom (fun j => GeneralLinear (B.size j) E) i))
    refine ⟨a.trans (equivOfRepresentationEq ?_)⟩
    exact (blockTensor_comp_leviAut σ B ρ).symm
  have hΞδσ : IsLeviSigmaStable σ B Ξδ := by
    refine ⟨(twistEquiv δ hΞσ.some).trans (equivOfRepresentationEq ?_)⟩
    rw [twist_comp, hδ]
  have eδ : P.Equiv (Induction.smoothInduced (B.parabolic E)
      (Ξδ.comp (B.leviProjection E))) := by
    refine e.trans (Induction.smoothInducedEquiv _ (equivOfRepresentationEq ?_))
    rw [twist_comp]
    rfl
  have hΞδirr := (B.isIrreducible_isAdmissible_of_smoothInduced hΞδ
    ((isIrreducible_iff_of_equiv eδ).mp hP.2.1)
    ((isAdmissible_iff_of_equiv eδ).mp hP.1)).1
  have (i : Fin B.length) : SecondCountableTopology (GeneralLinear (B.size i) E) :=
    T.generalLinearSecondCountableTopology (B.size i)
  have : SeparableSpace (B.Levi E) := inferInstanceAs (SeparableSpace (∀ i, GeneralLinear (B.size i) E))
  obtain ⟨Ξsmall, _, ⟨esmall⟩⟩ := exists_irreducible_smoothRep_equiv_of_separable.{v,max v uW,uW}
    (SmoothRep.of Ξδ hΞδ) hΞδirr
  have hsmallσ : IsLeviSigmaStable σ B Ξsmall.representation :=
    ⟨esmall.symm.trans (hΞδσ.some.trans (BinaryTensor.compEquiv esmall (leviAut σ B).toMonoidHom))⟩
  let eind := Induction.smoothInducedEquiv (B.parabolic E)
    (BinaryTensor.compEquiv esmall (B.leviProjection E))
  exact (hP.2.2.2.2 B hB Ξsmall Ξsmall.representation Ξsmall.isSmooth hsmallσ).false (eδ.trans eind)

end Exclusion

section OrbitAssembly

variable {F : Type u} [Field F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra F E]

private abbrev HasOrbitProduct (σ : E ≃ₐ[F] E) {n : ℕ} {W : Type uW}
    [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GeneralLinear n E) W) : Prop :=
  ∃ (t m : ℕ) (hm : 0 < m) (h : t * m = n)
    (X : Type uW) (_ : AddCommGroup X) (_ : Module ℂ X)
    (Q : Representation ℂ (GeneralLinear m E) X),
    Q.IsIrreducible ∧ JacquetLanglands.IsSquareIntegrable Q ∧
    (∀ i : ℕ, Nonempty (Q.Equiv (Q.comp (entrywiseAut (σ ^ i) m).toMonoidHom)) ↔ t ∣ i) ∧
    Nonempty (P.Equiv ((sigmaOrbitProduct σ t hm Q).comp
      (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom))

set_option maxHeartbeats 650000 in
private theorem hasOrbitProduct_of_large_block (σ : E ≃ₐ[F] E) {n t m : ℕ} (hm : 0 < m)
    (hrank : t * m = n) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear n E) W)
    (A : SmoothRep.{0,v,max v uW} ℂ (GeneralLinear m E)) (hi : A.IsIrreducible)
    (hsq : JacquetLanglands.IsSquareIntegrable A.representation)
    (hperiod : ∀ i : ℕ, Nonempty (A.representation.Equiv
      (A.representation.comp (entrywiseAut (σ ^ i) m).toMonoidHom)) ↔ t ∣ i)
    (e : P.Equiv ((sigmaOrbitProduct σ t hm A.representation).comp
      (GeneralLinear.reindex (R := E) (finCongr hrank)).symm.toMonoidHom)) :
    HasOrbitProduct σ P := by
  obtain ⟨Q, hiQ, ⟨eQ⟩⟩ := AllField.padicIrreducibleSmoothSmallRealization.{v,max v uW,uW}
    E (LocalFieldData.ofInstances E) m A hi
  have hQsq := (JacquetLanglands.isSquareIntegrable_iff_of_equiv eQ).mp hsq
  have hperiodQ (i : ℕ) : Nonempty (Representation.Equiv Q.representation
      (Q.representation.comp (entrywiseAut (σ ^ i) m).toMonoidHom)) ↔ t ∣ i := by
    let θ := (entrywiseAut (σ ^ i) m).toMonoidHom
    refine Iff.trans ?_ (hperiod i)
    constructor
    · rintro ⟨g⟩
      exact ⟨eQ.trans (g.trans (BinaryTensor.compEquiv eQ.symm θ))⟩
    · rintro ⟨g⟩
      exact ⟨eQ.symm.trans (g.trans (BinaryTensor.compEquiv eQ θ))⟩
  let eOrbit : (sigmaOrbitProduct σ t hm A.representation).Equiv
      (sigmaOrbitProduct σ t hm Q.representation) :=
    (LocalFieldData.ofInstances E).normalizedProductInducedEquiv
      (BlockShape.uniform t m hm) (fun i =>
        BinaryTensor.compEquiv eQ (entrywiseAut (σ ^ i.val) m).toMonoidHom)
  let reindexRank := (GeneralLinear.reindex (R := E) (finCongr hrank)).symm.toMonoidHom
  exact ⟨t, m, hm, hrank, Q, inferInstance, inferInstance, Q.representation, hiQ, hQsq,
    hperiodQ, ⟨e.trans (BinaryTensor.compEquiv eOrbit reindexRank)⟩⟩

end OrbitAssembly

section PadicAssembly

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{v} p} {T : K.TopologicalData}
variable {F : Type u} [Field F] [TopologicalSpace F] [Algebra F K.Carrier]
  (hModule : letI := T.topology; IsModuleTopology F K.Carrier)

set_option maxHeartbeats 750000 in
private theorem false_of_invariant_split (σ : K.Carrier ≃ₐ[F] K.Carrier) {n : ℕ} (hn : 0 < n)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear n K.Carrier) W) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    IsSigmaDiscreteSeries σ n P → ∀ (D : DiscreteBlocks.{v,uW} T n),
    P.Equiv D.product.representation → ∀ (M₀ M₁ : Multiset (BlockClass.{v,uW} T)),
    D.classes = M₀ + M₁ → M₀ ≠ 0 → M₁ ≠ 0 →
    M₀.map (pullClass T hModule σ) = M₀ → M₁.map (pullClass T hModule σ) = M₁ → False := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  intro hP D e M₀ M₁ hM h₀ h₁ hs₀ hs₁
  obtain ⟨J, hJ, U, hU, ⟨eU⟩⟩ := D.regroup hModule hn σ M₀ M₁ hM h₀ h₁ hs₀ hs₁
  let e' := e.trans (SmoothRep.equivOfIso eU)
  change P.Equiv ((LocalFieldData.ofInstances K.Carrier).normalizedProductInduced J
    (fun i => (U i).representation)) at e'
  exact false_of_proper_stable_product σ P hP J hJ
    (fun i => (U i).representation) (fun i => (U i).isSmooth) hU e'

set_option maxHeartbeats 700000 in
private theorem DiscreteBlocks.exists_orbit {n : ℕ} (D : DiscreteBlocks.{v,uW} T n)
    (σ : K.Carrier ≃ₐ[F] K.Carrier) {l : ℕ} (hcyc : IsCyclicAlgebra σ l) (hn : 0 < n)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear n K.Carrier) W) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    IsSigmaDiscreteSeries σ n P → P.Equiv D.product.representation →
    ∃ (j : Fin D.shape.length) (t : ℕ), D.classes = (D.orbit hModule σ j t).classes ∧
      ∀ i : ℕ, Nonempty ((D.blocks j).representation.Equiv
        ((D.blocks j).representation.comp (entrywiseAut (σ ^ i) (D.shape.size j)).toMonoidHom)) ↔
        t ∣ i := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hP e
  obtain ⟨eσ⟩ := hP.2.2.2.1
  let f := pullClass T hModule σ
  have hM : D.classes.map f = D.classes :=
    (DiscreteBlocks.stable_iff hModule hn D σ).mp
      ⟨e.symm.trans (eσ.trans (BinaryTensor.compEquiv e (entrywiseAut σ n).toMonoidHom))⟩
  have hlength : 0 < D.shape.length := by
    by_contra! h
    have : IsEmpty (Fin D.shape.length) := Fin.isEmpty_iff.mpr (Nat.eq_zero_of_le_zero h)
    exact hn.ne' (D.shape.sum_eq.symm.trans (Finset.sum_of_isEmpty _))
  let j : Fin D.shape.length := ⟨0, hlength⟩
  let m := D.shape.size j
  let hm : 0 < m := D.shape.positive j
  let A₀ := D.blocks j
  let x := blockClass T A₀
  let t := Function.minimalPeriod f x
  have hfix : Function.IsPeriodicPt f l x := by
    have hpow : σ ^ l = 1 := hcyc.pow_eq_one
    apply (isPeriodicPt_blockClass_iff T hModule σ A₀ l).mpr
    refine ⟨equivOfRepresentationEq ?_⟩
    apply MonoidHom.ext
    intro g
    change A₀.representation g = A₀.representation (entrywiseAut (σ ^ l) m g)
    rw [hpow, entrywiseAut_one_apply]
  have ht : 0 < t := hfix.minimalPeriod_pos hcyc.pos
  have hx : x ∈ D.classes := occurrences_mem.mpr ⟨j, rfl⟩
  let C := D.orbit hModule σ j t
  have hC : C.classes = occurrences (fun i : Fin t => f^[i.val] x) :=
    D.orbit_classes hModule σ j t
  obtain ⟨R, hR, hO, hRstable⟩ := orbit_submultiset f x D.classes hM hx
  change D.classes = occurrences (fun i : Fin t => f^[i.val] x) + R at hR
  change (occurrences fun i : Fin t => f^[i.val] x).map f =
    occurrences (fun i : Fin t => f^[i.val] x) at hO
  rw [← hC] at hR hO
  have hCne : C.classes ≠ 0 := by
    intro h
    have hsum := C.sum_ranks
    rw [h, Multiset.map_zero, Multiset.sum_zero] at hsum
    exact (Nat.mul_pos ht hm).ne' hsum.symm
  have hRzero : R = 0 := by
    by_contra hne
    exact false_of_invariant_split hModule σ hn P hP D e C.classes R hR hCne hne hO hRstable
  refine ⟨j, t, ?_, fun i => ?_⟩
  · simpa only [hRzero, add_zero] using hR
  · exact (isPeriodicPt_blockClass_iff T hModule σ A₀ i).symm.trans
      Function.isPeriodicPt_iff_minimalPeriod_dvd

set_option maxHeartbeats 900000 in
private theorem hasOrbitProduct_of_block_match (σ : K.Carrier ≃ₐ[F] K.Carrier)
    {n : ℕ} (hn : 0 < n) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear n K.Carrier) W) (D : DiscreteBlocks.{v,uW} T n)
    (j : Fin D.shape.length) (t : ℕ) (hsame : D.classes = (D.orbit hModule σ j t).classes) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    P.Equiv D.product.representation →
    (∀ i : ℕ, Nonempty ((D.blocks j).representation.Equiv
      ((D.blocks j).representation.comp (entrywiseAut (σ ^ i) (D.shape.size j)).toMonoidHom)) ↔
        t ∣ i) → HasOrbitProduct σ P := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro e hperiod
  let C := D.orbit hModule σ j t
  have hrank : t * D.shape.size j = n := by rw [← C.sum_ranks, ← hsame, D.sum_ranks]
  obtain ⟨eC⟩ := DiscreteBlocks.product_equiv_of_classes_eq hn D C hrank hsame
  let θ := (GeneralLinear.reindex (R := K.Carrier) (finCongr hrank)).symm.toMonoidHom
  let ef := BinaryTensor.compEquiv (D.orbit_product_equiv hModule σ j t) θ
  exact hasOrbitProduct_of_large_block σ (D.shape.positive j) hrank P (D.blocks j)
    (D.properties j).1 (D.properties j).2.1 hperiod (e.trans (eC.trans ef))

include hModule in
set_option maxHeartbeats 850000 in
private theorem sigmaDiscreteOrbit_of_padic (σ : K.Carrier ≃ₐ[F] K.Carrier)
    {l n : ℕ} (hcyc : IsCyclicAlgebra σ l) (hn : 0 < n)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear n K.Carrier) W) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    IsSigmaDiscreteSeries σ n P → HasOrbitProduct σ P := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hP
  let P₀ := SmoothRep.of P hP.1.1
  let Plift := P₀.universeLift.{v}
  let e₀ := P₀.universeLiftEquiv.{v}
  have htemp : T.IsTempered P := hP.2.2.1
  obtain ⟨B, A, hA, ⟨eA⟩⟩ := Classification.temperedBlockExhaustion.{v,uW} K T n hn Plift
    ((isIrreducible_iff_of_equiv e₀).mp hP.2.1) ((T.isTempered_iff_of_equiv e₀).mp htemp)
  let D : DiscreteBlocks.{v,uW} T n := ⟨B, A, hA⟩
  let e : P.Equiv D.product.representation := e₀.trans (SmoothRep.equivOfIso eA)
  obtain ⟨j, t, hsame, hperiod⟩ := D.exists_orbit hModule σ hcyc hn P hP e
  exact hasOrbitProduct_of_block_match hModule σ hn P D j t hsame e hperiod

end PadicAssembly

/-- A positive-rank σ-discrete series is the normalized product of one orbit
of an irreducible square-integrable representation. -/
theorem sigmaDiscreteSeriesOrbitDecomposition : SigmaDiscreteSeriesOrbitDecompositionStatement.{u,v,uW} := by
  intro F _ _ _ _ _ E _ _ _ _ _ _ σ l n hcyc hn W _ _ P hP
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  let : Algebra F (CharZeroLocalField.padicField E).Carrier := ‹Algebra F E›
  exact sigmaDiscreteOrbit_of_padic (T := CharZeroLocalField.topologicalData E) (F := F)
    (‹IsModuleTopology F E›) σ hcyc hn P hP

end Langlands.BaseChange
