import Langlands.Global.Factors.CuspidalBlockSectionLieExtension
import Langlands.Global.Factors.CuspidalInducedSingleBlock
import Langlands.Global.Factors.CuspidalIsobaricAutomorphyStatement
import Langlands.Global.Factors.ComplexIsobaricPlaceQuotient
import Langlands.Global.Factors.RealIsobaricQuotientReordering
import Langlands.Automorphic.CuspidalArchimedeanComponentUnitaryProof
import Langlands.Representation.Archimedean.RealGenericStandardParameterProof
import Langlands.Representation.Archimedean.RealTemperedIrreducibleProof
import Langlands.Representation.Classification.MultisegmentHeadExhaustionProof

/-! # Isobaric automorphy for a single cuspidal block -/

noncomputable section

open scoped BigOperators TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 65000

universe u uQ

namespace Langlands.Global

open Automorphic _root_.Langlands.Archimedean
open CompletionPadic (padicField)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open LocalFactor.Archimedean (RealBlock ComplexCharacterData)

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem inverse_of_irreducibleGKSubquotient {K L V J : Type*}
    [Group K] [LieRing L] [LieAlgebra ℂ L] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup J] [Module ℂ J]
    {κ : Representation ℂ K V} {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    {κJ : Representation ℂ K J} {πJ : L →ₗ⁅ℂ⁆ Module.End ℂ J}
    (hV : IsIrreducibleGKModule κ π) (hJ : IsIrreducibleGKModule κJ πJ)
    {W : Submodule ℂ V} {hW : IsGKSubmodule κ π W} {q : W →ₗ[ℂ] J}
    (hq : IsGKSubquotientMap κJ πJ hW q) :
    ∃ j : J →ₗ[ℂ] V, Function.Injective j ∧
      (∀ k x, j (κJ k x) = κ k (j x)) ∧ (∀ Y x, j (πJ Y x) = π Y (j x)) := by
  let : Nontrivial J := hJ.1
  obtain ⟨y, hy⟩ := exists_ne (0 : J)
  obtain ⟨w, hw⟩ := hq.1 y
  have htop : W = ⊤ := (hV.2 W hW.1 hW.2).resolve_left (fun hb => by
    have hz : w = 0 := Subtype.ext ((Submodule.mem_bot ℂ).mp (hb ▸ w.property))
    exact hy (hw.symm.trans (hz ▸ q.map_zero)))
  let toW : V →ₗ[ℂ] W := (LinearMap.id : V →ₗ[ℂ] V).codRestrict W
    (fun x => htop.symm ▸ Submodule.mem_top (R := ℂ) (x := x))
  let p := q.comp toW
  have hp : Function.Surjective p := fun y' => by
    obtain ⟨w', hw'⟩ := hq.1 y'
    exact ⟨w'.val, hw'⟩
  have hk (k : K) (x : V) : p (κ k x) = κJ k (p x) := hq.2.1 k (toW x)
  have hX (Y : L) (x : V) : p (π Y x) = πJ Y (p x) := hq.2.2 Y (toW x)
  have hker : LinearMap.ker p = ⊥ := (hV.2 (LinearMap.ker p)
    (fun k x hx => LinearMap.mem_ker.mpr (by rw [hk, LinearMap.mem_ker.mp hx, map_zero]))
    (fun Y x hx => LinearMap.mem_ker.mpr (by rw [hX, LinearMap.mem_ker.mp hx, map_zero]))).resolve_right
    (fun ht => by
      obtain ⟨x, hx⟩ := hp y
      exact hy (hx.symm.trans (LinearMap.mem_ker.mp (ht.symm ▸ Submodule.mem_top))))
  let e := LinearEquiv.ofBijective p ⟨LinearMap.ker_eq_bot.mp hker, hp⟩
  refine ⟨e.symm.toLinearMap, e.symm.injective, fun k x => ?_, fun Y x => ?_⟩
  · exact e.symm_apply_eq.mpr ((hk k (e.symm x)).trans (congrArg (κJ k) (e.apply_symm_apply x))).symm
  · exact e.symm_apply_eq.mpr ((hX Y (e.symm x)).trans (congrArg (πJ Y) (e.apply_symm_apply x))).symm

private theorem nonzero_of_injective {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial V] {f : V →ₗ[ℂ] W} (hf : Function.Injective f) :
    f ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  intro h
  exact hx (hf (by rw [h]; rfl))

section Single

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r : ℕ} (T : CuspidalOperatorRealization F r)

local notation "Q" => T.toIrreducibleSubquotient

private local instance (j : ℕ) : AddCommGroup (RationalInvariantFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (ContinuousRationalFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (AutomorphicForms F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (StableAutomorphicFunctions F j) := Submodule.addCommGroup _
private local instance {j : ℕ} (V : OperatorRealization F j) : AddCommGroup V.Space := Submodule.addCommGroup _
local notation "T₁" => (fun _ : Fin 1 => T)
local notation "n" => r + 1
local notation "RP" => {v : NumberField.InfinitePlace F // v.IsReal}
local notation "CP" => {v : NumberField.InfinitePlace F // v.IsComplex}

private theorem singleton_rank : ∑ _i : Fin 1, n = n := Fin.sum_univ_one _

private theorem singleton_flatten {X : Type*} (ds : Fin 1 → List X) :
    (List.ofFn ds).flatten = ds 0 := by simp [List.ofFn_succ]

private theorem singleBlockReal (v : RP) :
    ∃ ds : Fin 1 → List RealBlock, (∀ i, (T₁ i).realization.HasRealPlaceParameter v (ds i)) ∧
      ∃ es : List RealBlock, es.Perm (List.ofFn ds).flatten ∧ (Q).subquotient.HasRealPlaceLanglandsQuotient v es := by
  obtain ⟨ds, es, hds, hes, hn, ho, R, hR, hJ, W, hW, q, hq⟩ :=
    realIsobaricPlaceQuotientReduction realGenericStandardParameter realTemperedStandardIrreducible
      F r 1 (fun _ => r) singleton_rank T₁ v
  let xs := (List.ofFn ds).flatten
  have hp : T.realization.HasRealPlaceParameter v xs := by
    rw [show xs = ds 0 from singleton_flatten ds]
    exact (hds 0).1
  have hstd : IsIrreducibleGKModule (realStandardRep n xs) (realStandardLie n xs) := by
    rw [show xs = ds 0 from singleton_flatten ds]
    exact (hds 0).2
  obtain ⟨j, hji, hjK, hjL⟩ := inverse_of_irreducibleGKSubquotient hstd hJ hq
  obtain ⟨_, a, hai, haK, haL⟩ := hp
  let e := (OperatorRealization.toSubquotientEquiv F n T.realization).toLinearEquiv
  let b := e.toLinearMap.comp (a.comp j)
  have hbi : Function.Injective b := e.injective.comp (hai.comp hji)
  have hbK k x : b (((realStandardRep n es).quotient R hR.1) k x) =
      (Q).subquotient.realPlaceCompactRepresentation v k (b x) := by
    change e (a (j (((realStandardRep n es).quotient R hR.1) k x))) = _
    exact (congrArg (fun y => e (a y)) (hjK k x)).trans
      (congrArg e (OperatorRealization.realPlaceParameter_compact haK k (j x)))
  have hbL X x : b (RealLeviDuality.quotLie (realStandardLie n es) R hR.2 X x) =
      (Q).subquotient.realPlaceLieAction v X (b x) := by
    change e (a (j (RealLeviDuality.quotLie (realStandardLie n es) R hR.2 X x))) = _
    have haLie := CuspidalBlockInduction.intertwines_complexification_of_real a
      (realStandardLie n xs).toLinearMap (T.realization.realPlaceLieAction v).toLinearMap
      (OperatorRealization.realPlaceParameter_lie haL) X (j x)
    exact (congrArg (fun y => e (a y)) (hjL X x)).trans (congrArg e haLie)
  let := hJ.1
  exact ⟨ds, fun i => (hds i).1, es, hes,
    OperatorSubquotient.hasRealPlaceLanglandsQuotient_of_quotient hn
      (LocalFactor.Archimedean.isRealLanglandsOrdered_iff.mpr ho) hJ R.mkQ_surjective
      (quotientProjection_mem_gkHoms hR) (nonzero_of_injective hbi) ⟨hbK, hbL⟩⟩

private theorem singleBlockComplex (v : CP) :
    ∃ ds : Fin 1 → List ComplexCharacterData, (∀ i, (T₁ i).realization.HasComplexPlaceParameter v (ds i)) ∧
      ∃ es : List ComplexCharacterData, es.Perm (List.ofFn ds).flatten ∧ (Q).subquotient.HasComplexPlaceLanglandsQuotient v es := by
  obtain ⟨ds, es, hds, hes, hn, ho, R, hR, hJ, W, hW, q, hq⟩ :=
    hasComplexIsobaricPlaceQuotient (r := r) singleton_rank T₁ v
  let xs := (List.ofFn ds).flatten
  have hp : T.realization.HasComplexPlaceParameter v xs := by
    rw [show xs = ds 0 from singleton_flatten ds]
    exact (hds 0).1
  have hstd : IsIrreducibleGKModule (complexStandardRep n xs) (complexStandardLie n xs) := by
    rw [show xs = ds 0 from singleton_flatten ds]
    exact (hds 0).2
  obtain ⟨j, hji, hjK, hjL⟩ := inverse_of_irreducibleGKSubquotient hstd hJ hq
  obtain ⟨_, a, hai, haK, haL⟩ := hp
  let e := (OperatorRealization.toSubquotientEquiv F n T.realization).toLinearEquiv
  let b := e.toLinearMap.comp (a.comp j)
  have hbi : Function.Injective b := e.injective.comp (hai.comp hji)
  have hbK k x : b (((complexStandardRep n es).quotient R hR.1) k x) =
      (Q).subquotient.complexPlaceCompactRepresentation v k (b x) := by
    change e (a (j (((complexStandardRep n es).quotient R hR.1) k x))) = _
    exact (congrArg (fun y => e (a y)) (hjK k x)).trans
      (congrArg e (OperatorRealization.complexPlaceParameter_compact haK k (j x)))
  have hbL X x : b (RealLeviDuality.quotLie (complexStandardLie n es) R hR.2 X x) =
      (Q).subquotient.complexPlaceLieAction v X (b x) := by
    change e (a (j (RealLeviDuality.quotLie (complexStandardLie n es) R hR.2 X x))) = _
    have haLie := CuspidalBlockInduction.intertwines_complexification_of_real a
      (complexStandardLie n xs).toLinearMap (T.realization.complexPlaceLieAction v).toLinearMap
      (OperatorRealization.complexPlaceParameter_lie haL) X (j x)
    exact (congrArg (fun y => e (a y)) (hjL X x)).trans (congrArg e haLie)
  let := hJ.1
  exact ⟨ds, fun i => (hds i).1, es, hes,
    OperatorSubquotient.hasComplexPlaceLanglandsQuotient_of_quotient hn ho hJ R.mkQ_surjective
      (quotientProjection_mem_gkHoms hR) (nonzero_of_injective hbi) ⟨hbK, hbL⟩⟩

local instance singleBlockFiniteTopology (v : FinitePlace F) (j : ℕ) :
    TopologicalSpace (GeneralLinear j (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology j

/-- In the single-block case the zero-denominator quotient of the original
cuspidal realization contains the isobaric constituents at all places. -/
theorem singleCuspidalBlock_isobaric
    (P : ∀ i : Fin 1, CuspidalSpectralPresentation.{u, uQ} (T₁ i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i)) :
    (Q).IsCuspidalIsobaricSum (m := fun _ => r) T₁ P h := by
  refine ⟨?_, singleBlockReal T, singleBlockComplex T⟩
  intro v
  let A (i : Fin 1) := ((P i).localComponent v).padicObject (h i v).1 (h i v).2
  have ha (i : Fin 1) := Classification.multisegmentHeadExhaustion.{u, u}
    (padicField v) (padicField v).canonicalTopologicalData n (A i).obj (A i).property.1
  choose a ha using ha
  refine ⟨A 0, ⟨a, fun i => (ha i).2, ?_⟩,
    CuspidalInducedSingleBlock.cuspidalLocalInclusion (P 0) (h 0) v,
    CuspidalInducedSingleBlock.cuspidalLocalInclusion_injective (P 0) (h 0) v⟩
  rw [Fin.sum_univ_one]
  exact (ha 0).2

end Single

/-- The all-places target restricted to a family of one cuspidal block. -/
def CuspidalIsobaricSingleBlockStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r k : ℕ) (m : Fin k → ℕ), k = 1 → ∑ i, (m i + 1) = r + 1 →
    ∀ (T : ∀ i, CuspidalOperatorRealization F (m i))
      (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
      (h : ∀ i, HasIrreducibleAdmissibleComponents (P i)),
      ∃ Q : IrreducibleOperatorSubquotient F r, (Q).IsCuspidalIsobaricSum T P h

/-- Isobaric automorphy at every place in the single-block case. -/
theorem cuspidalIsobaricSingleBlock : CuspidalIsobaricSingleBlockStatement.{u, uQ} := by
  intro F _ _ _ r k m hk hm T P h
  subst k
  have hsize : m (0 : Fin 1) = r := by
    rw [Fin.sum_univ_one] at hm
    exact Nat.succ.inj hm
  have heq : m = fun _ => r := funext fun i => (congrArg m (Fin.eq_zero i)).trans hsize
  subst m
  let T₀ := T 0
  have hT : T = fun _ => T₀ := funext fun i => congrArg T (Fin.eq_zero i)
  revert P h
  rw [hT]
  intro P h
  exact ⟨T₀.toIrreducibleSubquotient, singleCuspidalBlock_isobaric T₀ P h⟩

end Langlands.Global
