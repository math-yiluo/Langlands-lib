import Langlands.Global.Factors.IsobaricAutomorphicRepresentation
import Langlands.Automorphic.CuspidalArchimedeanPlaceComponent
import Langlands.Automorphic.OperatorSubquotientLocalComponentStatement
import Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveReduction
import Langlands.Representation.Archimedean.RealLeviDuality
import Langlands.Representation.Archimedean.RealLeviSlices
import Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionReduction

/-!
# Archimedean ordering and quotient embeddings for isobaric sums

The ranks add on concatenation and are preserved by stable sorting into Langlands
order. This sorting can be achieved by adjacent swaps of strictly inverted pairs.
If a largest proper `(𝔤, K)`-stable subspace is given, the quotient is irreducible.
An embedded irreducible quotient of an ordered standard module supplies the
corresponding place predicate on the ambient operator subquotient.
-/

noncomputable section

open scoped BigOperators TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

section Quotient

variable {K L V W : Type*} [Group K] [LieRing L] [LieAlgebra ℂ L]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {κ : Representation ℂ K V} {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    {κ' : Representation ℂ K W} {π' : L →ₗ⁅ℂ⁆ Module.End ℂ W}

/-- The quotient projection intertwines the induced compact and Lie actions. -/
theorem quotientProjection_mem_gkHoms {R : Submodule ℂ V}
    (hR : IsGKSubmodule κ π R) :
    R.mkQ ∈ gkHoms κ π (κ.quotient R hR.1) (RealLeviDuality.quotLie π R hR.2) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- The quotient by the largest proper stable subspace is irreducible. -/
theorem isIrreducibleGKModule_quotient_of_largest {R : Submodule ℂ V}
    (hR : IsGKSubmodule κ π R) (hne : R ≠ ⊤)
    (hmax : ∀ S : Submodule ℂ V, IsGKSubmodule κ π S → S ≠ ⊤ → S ≤ R) :
    IsIrreducibleGKModule (κ.quotient R hR.1) (RealLeviDuality.quotLie π R hR.2) := by
  refine ⟨?_, fun S hK hL => ?_⟩
  · by_contra h
    have hsub : Subsingleton (V ⧸ R) := not_nontrivial_iff_subsingleton.mp h
    apply hne (top_unique fun x _ => (Submodule.Quotient.mk_eq_zero R).mp
      (hsub.elim (R.mkQ x) 0))
  · have hS : IsGKSubmodule κ π (S.comap R.mkQ) :=
      ⟨fun k x hx => hK k (R.mkQ x) hx, fun X x hx => hL X (R.mkQ x) hx⟩
    have hmap := Submodule.map_comap_eq_of_surjective R.mkQ_surjective S
    by_cases htop : S.comap R.mkQ = ⊤
    · right
      rwa [htop, Submodule.map_top, Submodule.range_mkQ, eq_comm] at hmap
    · left
      have hcomap : S.comap R.mkQ = R :=
        le_antisymm (hmax _ hS htop) (Submodule.le_comap_mkQ R S)
      rwa [hcomap, Submodule.mkQ_map_self, eq_comm] at hmap

/-- The image of a nonzero map out of an irreducible module is an irreducible subspace. -/
theorem isIrreducible_range_of_gkHoms (hV : IsIrreducibleGKModule κ π)
    {B : V →ₗ[ℂ] W} (hB : B ∈ gkHoms κ π κ' π') (hne : B ≠ 0) :
    Automorphic.PlaceComponent.IsIrreducible κ' π' (LinearMap.range B) := by
  have h := (mem_gkHoms κ π κ' π' B).mp hB
  refine ⟨fun hz => hne (LinearMap.range_eq_bot.mp hz), ⟨?_, ?_⟩, ?_⟩
  · rintro k _ ⟨x, rfl⟩
    exact ⟨κ k x, h.1 k x⟩
  · rintro X _ ⟨x, rfl⟩
    exact ⟨π X x, h.2 X x⟩
  · intro S hS hstab
    have hK (k : K) (x : V) (hx : x ∈ S.comap B) : κ k x ∈ S.comap B := by
      change B (κ k x) ∈ S
      rw [h.1]
      exact hstab.1 k _ hx
    have hL (X : L) (x : V) (hx : x ∈ S.comap B) : π X x ∈ S.comap B := by
      change B (π X x) ∈ S
      rw [h.2]
      exact hstab.2 X _ hx
    have hmap : (S.comap B).map B = S := Submodule.map_comap_eq_of_le hS
    rcases hV.2 (S.comap B) hK hL with hzero | htop
    · left
      rwa [hzero, Submodule.map_bot, eq_comm] at hmap
    · right
      rwa [htop, Submodule.map_top, eq_comm] at hmap

end Quotient

end Langlands.Archimedean

namespace Langlands.LocalFactor.Archimedean

open Langlands.Archimedean (complexLanglandsLE isComplexLanglandsOrdered_mergeSort
  realBlockExponent realRank_perm)

/-- One adjacent swap moving an element of strictly higher weight to the left. -/
def StrictAdjacentSwap {α β : Type*} [LT β] (weight : α → β) (xs ys : List α) : Prop :=
  ∃ (pre post : List α) (a b : α), weight a < weight b ∧
    xs = pre ++ a :: b :: post ∧ ys = pre ++ b :: a :: post

/-- A strict adjacent swap preserves the elements with their multiplicities. -/
theorem StrictAdjacentSwap.perm {α β : Type*} [LT β] {weight : α → β} {xs ys : List α}
    (h : StrictAdjacentSwap weight xs ys) : xs.Perm ys := by
  obtain ⟨pre, post, a, b, _, rfl, rfl⟩ := h
  exact (List.Perm.swap b a post).append_left pre

private theorem strictAdjacentSwaps_cons {α β : Type*} [LT β] {weight : α → β}
    {xs ys : List α} (a : α) (h : Relation.ReflTransGen (StrictAdjacentSwap weight) xs ys) :
    Relation.ReflTransGen (StrictAdjacentSwap weight) (a :: xs) (a :: ys) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    obtain ⟨pre, post, b, c, hlt, rfl, rfl⟩ := hstep
    exact ih.tail ⟨a :: pre, post, b, c, hlt, rfl, rfl⟩

private theorem strictAdjacentSwaps_insert {α β : Type*} [LT β] (weight : α → β)
    (a : α) (pre post : List α) (h : ∀ b ∈ pre, weight a < weight b) :
    Relation.ReflTransGen (StrictAdjacentSwap weight) (a :: (pre ++ post))
      (pre ++ a :: post) := by
  induction pre with
  | nil => exact .refl
  | cons b pre ih =>
    have hstep : StrictAdjacentSwap weight (a :: b :: (pre ++ post))
        (b :: a :: (pre ++ post)) :=
      ⟨[], pre ++ post, a, b, h b List.mem_cons_self, rfl, rfl⟩
    exact .head hstep (strictAdjacentSwaps_cons b (ih fun c hc => h c (List.mem_cons_of_mem _ hc)))

/-- Stable decreasing sort is reached by swaps across strictly greater weights. -/
theorem strictAdjacentSwaps_mergeSort {α β : Type*} [LinearOrder β]
    (weight : α → β) (xs : List α) :
    Relation.ReflTransGen (StrictAdjacentSwap weight) xs
      (xs.mergeSort fun a b => decide (weight b ≤ weight a)) := by
  let le : α → α → Bool := fun a b => decide (weight b ≤ weight a)
  change Relation.ReflTransGen (StrictAdjacentSwap weight) xs (xs.mergeSort le)
  have htrans (a b c : α) (hab : le a b) (hbc : le b c) : le a c := by
    simp only [le, decide_eq_true_eq] at hab hbc ⊢
    exact hbc.trans hab
  have htotal (a b : α) : le a b || le b a := by
    simp only [le, Bool.or_eq_true, decide_eq_true_eq]
    exact le_total _ _
  induction xs with
  | nil => simpa only [List.mergeSort_nil] using
      (Relation.ReflTransGen.refl : Relation.ReflTransGen (StrictAdjacentSwap weight) [] [])
  | cons a xs ih =>
    obtain ⟨pre, post, hsort, htail, hpre⟩ := List.mergeSort_cons htrans htotal a xs
    rw [hsort]
    rw [htail] at ih
    exact (strictAdjacentSwaps_cons a ih).trans
      (strictAdjacentSwaps_insert weight a pre post
        (fun b hb => by simpa [le, not_le] using hpre b hb))

/-- The Boolean comparator for real Langlands order. -/
def realLanglandsLE (a b : RealBlock) : Bool :=
  decide (b.exponent.re ≤ a.exponent.re)

/-- Sorting real blocks uses only adjacent swaps with strictly increasing real exponents. -/
theorem realStrictAdjacentSwaps_mergeSort (ds : List RealBlock) :
    Relation.ReflTransGen (StrictAdjacentSwap fun d : RealBlock => d.exponent.re) ds
      (ds.mergeSort realLanglandsLE) :=
  strictAdjacentSwaps_mergeSort (fun d : RealBlock => d.exponent.re) ds

/-- Sorting complex characters uses only adjacent swaps with strictly increasing real
exponents. -/
theorem complexStrictAdjacentSwaps_mergeSort (ds : List ComplexCharacterData) :
    Relation.ReflTransGen (StrictAdjacentSwap fun d : ComplexCharacterData => d.exponent.re) ds
      (ds.mergeSort complexLanglandsLE) :=
  strictAdjacentSwaps_mergeSort (fun d : ComplexCharacterData => d.exponent.re) ds

/-- The sorted real blocks are in Langlands order. -/
theorem isRealLanglandsOrdered_mergeSort (ds : List RealBlock) :
    IsRealLanglandsOrdered (ds.mergeSort realLanglandsLE) := by
  have hs := List.pairwise_mergeSort (le := realLanglandsLE)
    (fun a b c hab hbc => by
      simp only [realLanglandsLE, decide_eq_true_eq] at hab hbc ⊢
      exact hbc.trans hab)
    (fun a b => by
      simp only [realLanglandsLE, Bool.or_eq_true, decide_eq_true_eq]
      exact le_total _ _) ds
  exact hs.imp (by simp [realLanglandsLE])

/-- The two real Langlands order predicates use the same real exponents. -/
theorem isRealLanglandsOrdered_iff {ds : List RealBlock} :
    IsRealLanglandsOrdered ds ↔ Langlands.Archimedean.IsRealLanglandsOrdered ds := by
  have he (d : RealBlock) : d.exponent.re = realBlockExponent d := by cases d <;> rfl
  simp only [IsRealLanglandsOrdered, Langlands.Archimedean.IsRealLanglandsOrdered, he]

/-- Sorting a concatenation of real blocks preserves its total rank. -/
theorem exists_ordered_realBlock_concatenation {k n : ℕ} (ds : Fin k → List RealBlock)
    (hr : ∑ i, realRank (ds i) = n) :
    ∃ es, es.Perm (List.ofFn ds).flatten ∧ realRank es = n ∧ IsRealLanglandsOrdered es := by
  let xs := (List.ofFn ds).flatten
  have hp := List.mergeSort_perm xs realLanglandsLE
  refine ⟨xs.mergeSort realLanglandsLE, hp, ?_, isRealLanglandsOrdered_mergeSort xs⟩
  rw [realRank_perm hp]
  exact (Langlands.Archimedean.RealLeviSlices.realRank_flat ds).trans hr

/-- Sorting a concatenation of complex characters preserves its length. -/
theorem exists_ordered_complexCharacter_concatenation {k n : ℕ}
    (ds : Fin k → List ComplexCharacterData) (hr : ∑ i, (ds i).length = n) :
    ∃ es, es.Perm (List.ofFn ds).flatten ∧ es.length = n ∧ IsComplexLanglandsOrdered es := by
  let xs := (List.ofFn ds).flatten
  have hp := List.mergeSort_perm xs complexLanglandsLE
  refine ⟨xs.mergeSort complexLanglandsLE, hp, ?_, isComplexLanglandsOrdered_mergeSort xs⟩
  rw [hp.length_eq, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  exact hr

end Langlands.LocalFactor.Archimedean

namespace Langlands.Automorphic.OperatorSubquotient

open Langlands.Archimedean
open Langlands.LocalFactor.Archimedean (RealBlock ComplexCharacterData realRank)

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem stable_lie_of_one_tmul {M U : Type*} [AddCommGroup M] [Module ℝ M]
    [AddCommGroup U] [Module ℂ U] (π : ℂ ⊗[ℝ] M →ₗ[ℂ] Module.End ℂ U)
    {S : Submodule ℂ U} (h : ∀ X : M, ∀ y ∈ S, π (1 ⊗ₜ X) y ∈ S)
    (X : ℂ ⊗[ℝ] M) (y : U) (hy : y ∈ S) : π X y ∈ S := by
  induction X using TensorProduct.inductionOn with
  | tmul c X =>
    have he : c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he, map_smul, LinearMap.smul_apply]
    exact S.smul_mem c (h X y hy)
  | add X Y hX hY =>
    rw [map_add, LinearMap.add_apply]
    exact S.add_mem hX hY

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} {J : Type*}
    [AddCommGroup J] [Module ℂ J] {Q : OperatorSubquotient F n}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

set_option maxHeartbeats 1200000 in
/-- An embedded irreducible quotient of an ordered real standard module gives the real
place quotient predicate. -/
theorem hasRealPlaceLanglandsQuotient_of_quotient {v : RP} {ds : List RealBlock}
    (hr : realRank ds = n) (ho : LocalFactor.Archimedean.IsRealLanglandsOrdered ds)
    {κ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) J}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ J}
    (hJ : IsIrreducibleGKModule κ π)
    {p : realStandardKFinite n ds →ₗ[ℂ] J} (hp : Function.Surjective p)
    (hpGK : p ∈ gkHoms (realStandardRep n ds) (realStandardLie n ds) κ π)
    {B : J →ₗ[ℂ] Q.Space} (hne : B ≠ 0)
    (hB : B ∈ gkHoms κ π (Q.realPlaceCompactRepresentation v) (Q.realPlaceLieAction v)) :
    Q.HasRealPlaceLanglandsQuotient v ds := by
  let A : realStandardKFinite n ds →ₗ[ℂ] Q.Space := B ∘ₗ p
  have hrange : LinearMap.range A = LinearMap.range B :=
    LinearMap.range_comp_of_range_eq_top B (LinearMap.range_eq_top.mpr hp)
  have hA := isIrreducible_range_of_gkHoms hJ hB hne
  rw [← hrange] at hA
  have hB' := (mem_gkHoms κ π _ _ B).mp hB
  have hp' := (mem_gkHoms (realStandardRep n ds) (realStandardLie n ds) κ π p).mp hpGK
  refine ⟨hr, ho, A, fun k f => ?_, fun X f => ?_, hA.1, fun S hS hK hL => ?_⟩
  · obtain ⟨hf, he⟩ := (isRealStandardIntertwiner_id n ds).1 k f
    simp only [LinearMap.id_apply] at he
    exact ⟨hf, (congrArg (fun x : realStandardKFinite n ds => B (p x)) he).trans
      ((congrArg B (hp'.1 ⟨_, k.2⟩ f)).trans (hB'.1 ⟨_, k.2⟩ (p f)))⟩
  · obtain ⟨hf, he⟩ := (isRealStandardIntertwiner_id n ds).2 X f
    simp only [LinearMap.id_apply] at he
    exact ⟨hf, (congrArg (fun x : realStandardKFinite n ds => B (p x)) he).trans
      ((congrArg B (hp'.2 (1 ⊗ₜ X) f)).trans (hB'.2 (1 ⊗ₜ X) (p f)))⟩
  · exact hA.2.2 S hS ⟨hK,
      stable_lie_of_one_tmul (Q.realPlaceLieAction v).toLinearMap hL⟩

set_option maxHeartbeats 1200000 in
/-- An embedded irreducible quotient of an ordered complex standard module gives the complex
place quotient predicate. -/
theorem hasComplexPlaceLanglandsQuotient_of_quotient {v : CP} {ds : List ComplexCharacterData}
    (hr : ds.length = n) (ho : LocalFactor.Archimedean.IsComplexLanglandsOrdered ds)
    {κ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) J}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ J}
    (hJ : IsIrreducibleGKModule κ π)
    {p : complexStandardKFinite n ds →ₗ[ℂ] J} (hp : Function.Surjective p)
    (hpGK : p ∈ gkHoms (complexStandardRep n ds) (complexStandardLie n ds) κ π)
    {B : J →ₗ[ℂ] Q.Space} (hne : B ≠ 0)
    (hB : B ∈ gkHoms κ π (Q.complexPlaceCompactRepresentation v) (Q.complexPlaceLieAction v)) :
    Q.HasComplexPlaceLanglandsQuotient v ds := by
  let A : complexStandardKFinite n ds →ₗ[ℂ] Q.Space := B ∘ₗ p
  have hrange : LinearMap.range A = LinearMap.range B :=
    LinearMap.range_comp_of_range_eq_top B (LinearMap.range_eq_top.mpr hp)
  have hA := isIrreducible_range_of_gkHoms hJ hB hne
  rw [← hrange] at hA
  have hB' := (mem_gkHoms κ π _ _ B).mp hB
  have hp' := (mem_gkHoms (complexStandardRep n ds) (complexStandardLie n ds) κ π p).mp hpGK
  refine ⟨hr, ho, A, fun k f => ?_, fun X f => ?_, hA.1, fun S hS hK hL => ?_⟩
  · obtain ⟨hf, he⟩ := (isComplexStandardIntertwining_id n ds).1 k f
    simp only [LinearMap.id_apply] at he
    exact ⟨hf, (congrArg (fun x : complexStandardKFinite n ds => B (p x)) he).trans
      ((congrArg B (hp'.1 ⟨_, k.2⟩ f)).trans (hB'.1 ⟨_, k.2⟩ (p f)))⟩
  · obtain ⟨hf, he⟩ := (isComplexStandardIntertwining_id n ds).2 X f
    simp only [LinearMap.id_apply] at he
    exact ⟨hf, (congrArg (fun x : complexStandardKFinite n ds => B (p x)) he).trans
      ((congrArg B (hp'.2 (1 ⊗ₜ X) f)).trans (hB'.2 (1 ⊗ₜ X) (p f)))⟩
  · exact hA.2.2 S hS ⟨hK,
      stable_lie_of_one_tmul (Q.complexPlaceLieAction v).toLinearMap hL⟩

end Langlands.Automorphic.OperatorSubquotient
