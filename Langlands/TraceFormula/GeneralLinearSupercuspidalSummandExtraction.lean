import Langlands.TraceFormula.DeterminantUnitOccurrence
import Langlands.TraceFormula.IsotypicTrace.CuspidalOccurrenceReduction
import Langlands.TraceFormula.UnitarySchurHilbertSumStatement
import Langlands.TraceFormula.GlobalizationTensor

/-! # Extraction from simultaneous determinant-unit occurrences -/

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.Global.PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions
open Langlands.TraceFormula.GlobalizationTensor (matrixPlaceInclusion)

namespace Langlands.TraceFormula

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

set_option hygiene false in
local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

local instance globalizationExtractionIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance globalizationExtractionSmooth : Smooth (GLG).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option maxHeartbeats 800000 in
private theorem commute_matrixPlaceInclusion_scalar (v : Langlands.Global.FinitePlace K)
    (b : (v.adicCompletion K)ˣ) (g : AdelicGroupPoints K GLG) :
    Commute (matrixPlaceInclusion K n v (GeneralLinear.scalar b)) g := by
  let E : PlaceGroupPoints K GLG (.inr v) ≃ₜ* GeneralLinear n (v.adicCompletion K) :=
    GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K)
      (placeCompletion K (.inr v))
  obtain ⟨y, h, rfl, hcomm⟩ := IsotypicTrace.exists_split K GLG v g
  change Commute (ofPlace K GLG (.inr v) (E.symm (GeneralLinear.scalar b)))
    (ofPlace K GLG (.inr v) y * h)
  have hy : Commute (E.symm (GeneralLinear.scalar b)) y := by
    change E.symm (GeneralLinear.scalar b) * y = y * E.symm (GeneralLinear.scalar b)
    apply E.injective
    rw [map_mul, map_mul, E.apply_symm_apply]
    exact (Subgroup.mem_center_iff.mp (GeneralLinear.scalarToCenter (n := n) b).property (E y)).symm
  exact (hy.map (ofPlace K GLG (.inr v))).mul_right (hcomm _)

variable (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive GLG)
  (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ GLG)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
  (hc : IsCentral i) [(Measure.haar : Measure (normOneSubgroup K GLG)).IsMulRightInvariant]

set_option hygiene false in
local notation "S" => fullAEL2CuspidalSubmodule K GLG hPD hG T i hi I e hc
set_option hygiene false in
local notation "πc" => fullAEL2CuspidalBoundedRightAction K GLG hPD hG T i hi I e hc

set_option maxHeartbeats 1200000 in
private theorem projection_intertwines (P : Submodule ℂ S) [CompleteSpace P]
    (hPinv : ∀ a, ∀ x ∈ P, πc a x ∈ P) (a : AdelicGroupPoints K GLG) (x : S) :
    P.orthogonalProjectionOnto (πc a x) =
      IsotypicTrace.restrictAction πc P hPinv a (P.orthogonalProjectionOnto x) := by
  apply Subtype.ext
  change P.starProjection (πc a x) = πc a (P.starProjection x)
  apply P.eq_starProjection_of_mem_of_inner_eq_zero (hPinv a _ (P.starProjection_apply_mem x))
  intro y hy
  let z := πc a⁻¹ y
  have hz : z ∈ P := hPinv _ y hy
  have hza : πc a z = y := by
    change πc a (πc a⁻¹ y) = y
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [← hza, ← map_sub]
  exact ((fullAEL2CuspidalRightTranslate K GLG hPD hG T i hi I e hc a).inner_map_map _ _).trans
    (P.starProjection_inner_eq_zero x z hz)

private theorem schur_unitNonzeroScalar {M E : Type u} [Group M] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (hSchur : UnitarySchurHilbertSumStatement.{u,u}) (R : M →* (E →L[ℂ] E))
    (hRnorm : ∀ g x, ‖R g x‖ = ‖x‖)
    (hRirr : ∀ Q : Submodule ℂ E, IsClosed (Q : Set E) →
      (∀ a, ∀ x ∈ Q, R a x ∈ Q) → Q = ⊥ ∨ Q = ⊤)
    (c : M) (hcomm : ∀ g, Commute c g) (x : E) (hx : x ≠ 0) :
    ∃ b : ℂˣ, ∀ y, R c y = (b : ℂ) • y := by
  obtain ⟨b, hb⟩ := hSchur.1 E M R hRnorm hRirr (R c) (fun g => by
    change R c * R g = R g * R c
    rw [← map_mul, ← map_mul, (hcomm g).eq])
  have hb0 : b ≠ 0 := by
    intro he
    have hzero := congrArg (fun A : E →L[ℂ] E => A x) hb
    simp only [he, zero_smul, zero_apply] at hzero
    exact hx (norm_eq_zero.mp ((hRnorm c x).symm.trans (by rw [hzero, norm_zero])))
  exact ⟨Units.mk0 b hb0, fun y => congrArg (fun A : E →L[ℂ] E => A y) hb⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
/-- A common vector in the ranges of determinant-unit intertwiners survives in one
irreducible summand of a dense cuspidal sum, together with all of the prescribed types. -/
theorem extract_supercuspidalSummand_of_determinantUnitOccurrence
    (hn : 0 < n) (hSchur : UnitarySchurHilbertSumStatement.{u,u})
    (A : Set (Submodule ℂ S))
    (hA : ∀ P ∈ A, P ≠ ⊥ ∧ IsClosed (P : Set S) ∧
      (∀ a, ∀ x ∈ P, πc a x ∈ P) ∧
      ∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
        (∀ a, ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P)
    (hTotal : (⨆ P : A, P.val).topologicalClosure = ⊤)
    (Sc : Finset (Langlands.Global.FinitePlace K)) (vaux : Langlands.Global.FinitePlace K)
    (V : Langlands.Global.FinitePlace K → Type w) [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (ρ : ∀ v : Langlands.Global.FinitePlace K,
      Representation ℂ (GeneralLinear n (v.adicCompletion K)) (V v))
    (hρ : ∀ v ∈ Sc, (ρ v).IsIrreducible ∧ IsAdmissible (ρ v))
    (x : S) (hx : x ≠ 0)
    (hfix : ∀ v : Langlands.Global.FinitePlace K, v ∉ Sc → v ≠ vaux →
      ∀ g ∈ FiniteAdelicGL.localIntegral K n v, πc (matrixPlaceInclusion K n v g) x = x)
    (hj : ∀ v ∈ Sc, ∃ j : V v →ₗ[ℂ] S, (∃ y, j y = x) ∧
      ∀ g, Valued.v (GeneralLinear.determinant g : v.adicCompletion K) = 1 →
        ∀ y, j (ρ v g y) = πc (matrixPlaceInclusion K n v g) (j y)) :
    ∃ (P : Submodule ℂ S) (_ : CompleteSpace P), P ≠ ⊥ ∧
      (∀ a, ∀ x ∈ P, πc a x ∈ P) ∧
      (∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
        (∀ a, ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) ∧
      (∃ x ∈ P, x ≠ 0 ∧ ∀ v : Langlands.Global.FinitePlace K, v ∉ Sc → v ≠ vaux →
        ∀ g ∈ FiniteAdelicGL.localIntegral K n v, πc (matrixPlaceInclusion K n v g) x = x) ∧
      ∀ v ∈ Sc, ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
        (∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 → χ t = 1) ∧
        ∃ j : V v →ₗ[ℂ] P, j ≠ 0 ∧ ∀ g y,
          (j (Langlands.twist (χ.comp GeneralLinear.determinant) (ρ v) g y) : S) =
            πc (matrixPlaceInclusion K n v g) (j y) := by
  obtain ⟨p, y, hy, hxy⟩ := IsotypicTrace.exists_inner_ne_zero (fun P : A => P.val) hTotal x hx
  let P := p.val
  obtain ⟨hP0, hPclosed, hPinv, hPirr⟩ := hA P p.property
  let : NormedAddCommGroup S := Submodule.normedAddCommGroup S
  let : InnerProductSpace ℂ S := Submodule.innerProductSpace S
  let : NormedAddCommGroup P := Submodule.normedAddCommGroup P
  let : InnerProductSpace ℂ P := Submodule.innerProductSpace P
  let : CompleteSpace P := hPclosed.completeSpace_coe
  let xP := P.orthogonalProjectionOnto x
  have hxP : xP ≠ 0 := by
    intro h0
    apply hxy
    rw [← P.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨y, hy⟩, show P.orthogonalProjectionOnto x = 0 from h0,
      inner_zero_right]
  have hproj := projection_intertwines K n hPD hG T i hi I e hc P hPinv
  refine ⟨P, inferInstance, hP0, hPinv, hPirr, ⟨(xP : S), xP.property, ?_, ?_⟩, ?_⟩
  · intro h
    exact hxP (Subtype.ext h)
  · intro v hv haux g hg
    have h := hproj (matrixPlaceInclusion K n v g) x
    rw [hfix v hv haux g hg] at h
    exact (congrArg Subtype.val h).symm
  · intro v hv
    obtain ⟨j, ⟨z, hz⟩, hjeq⟩ := hj v hv
    let R := IsotypicTrace.restrictAction πc P hPinv
    let κ := matrixPlaceInclusion K n v
    let τ : Representation ℂ (GeneralLinear n (v.adicCompletion K)) P :=
      ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp (R.comp κ)
    let jP := P.orthogonalProjectionOnto.toLinearMap.comp j
    have hPj0 : jP ≠ 0 := by
      intro he
      apply hxP
      have hz' := LinearMap.congr_fun he z
      change P.orthogonalProjectionOnto (j z) = 0 at hz'
      rwa [hz] at hz'
    have hPj (g : GeneralLinear n (v.adicCompletion K))
        (hg : Valued.v (GeneralLinear.determinant g : v.adicCompletion K) = 1) (y' : V v) :
        jP (ρ v g y') = τ g (jP y') := by
      change P.orthogonalProjectionOnto (j (ρ v g y')) = R (κ g) (P.orthogonalProjectionOnto (j y'))
      rw [hjeq g hg]
      exact hproj (κ g) (j y')
    have hRnorm (g : AdelicGroupPoints K GLG) (y' : P) : ‖R g y'‖ = ‖y'‖ :=
      norm_fullAEL2CuspidalBoundedRightAction K GLG hPD hG T i hi I e hc g y'
    have hRirr := IsotypicTrace.restrictAction_irreducible πc P hPinv hPirr
    have hscalar (a : (v.adicCompletion K)ˣ) : ∃ b : ℂˣ,
        ∀ y' : P, τ (GeneralLinear.scalar a) y' = (b : ℂ) • y' := by
      exact schur_unitNonzeroScalar hSchur R hRnorm hRirr (κ (GeneralLinear.scalar a))
        (commute_matrixPlaceInclusion_scalar K n v a) xP hxP
    obtain ⟨χ, hχ, Tv, hTv0, hTveq⟩ := exists_unramifiedDeterminantTwist_intertwiner K v n hn
      (ρ v) (hρ v hv).2 (hρ v hv).1 τ hscalar jP hPj0 hPj
    exact ⟨χ, hχ, Tv, hTv0, fun g z => congrArg Subtype.val (hTveq g z)⟩

end Langlands.TraceFormula
