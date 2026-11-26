import Langlands.TraceFormula.UnitarySchurHilbertSumStatement
import Langlands.TraceFormula.IsotypicTrace.RestrictAction
import Langlands.Representation.Archimedean.HilbertIntertwinerEvaluation
import Langlands.Representation.Archimedean.UnitaryCommutant

/-!
# Schur's lemma and irreducible subspaces of Hilbert sums

A summand projection that is nonzero on an irreducible invariant subspace can be
normalized to an equivariant linear isometric equivalence onto that summand.
-/

noncomputable section

namespace Langlands.TraceFormula

open ContinuousLinearMap (adjoint)

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {M : Type v} [Group M]

private theorem action_inner (ρ : M →* (E →L[ℂ] E)) (hρ : ∀ a x, ‖ρ a x‖ = ‖x‖)
    (a : M) (x y : E) : inner ℂ (ρ a x) (ρ a y) = inner ℂ x y :=
  (LinearMap.norm_map_iff_inner_map_map (ρ a)).mp (hρ a) x y

private theorem scalarCommutant [CompleteSpace E] (ρ : M →* (E →L[ℂ] E))
    (hρ : ∀ a x, ‖ρ a x‖ = ‖x‖)
    (hirr : ∀ Q : Submodule ℂ E, IsClosed (Q : Set E) →
      (∀ a, ∀ x ∈ Q, ρ a x ∈ Q) → Q = ⊥ ∨ Q = ⊤)
    (B : E →L[ℂ] E) (hB : ∀ a, B ∘L ρ a = ρ a ∘L B) :
    ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ E := by
  by_cases hE : Nontrivial E
  · exact Archimedean.exists_eq_scalar_of_unitary_commute ρ (action_inner ρ hρ) ⟨hE, hirr⟩ B hB
  · let : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    exact ⟨0, ContinuousLinearMap.ext fun _ => Subsingleton.elim _ _⟩

private theorem exists_summand_projection_ne_zero [CompleteSpace E]
    {A : Set (Submodule ℂ E)} [∀ P : A, CompleteSpace (P : Submodule ℂ E)]
    (hSum : IsHilbertSum ℂ (fun P : A => (P : Submodule ℂ E))
      (fun P => (P : Submodule ℂ E).subtypeₗᵢ)) {x : E} (hx : x ≠ 0) :
    ∃ P : A, (P : Submodule ℂ E).orthogonalProjectionOnto x ≠ 0 := by
  classical
  by_contra! h
  let e := hSum.linearIsometryEquiv
  have hz : e x = 0 := by
    apply lp.ext
    funext P
    change e x P = 0
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    have hcoord := e.symm.inner_map_map (lp.single 2 P (e x P)) (e x)
    change inner ℂ (hSum.linearIsometryEquiv.symm (lp.single 2 P (e x P))) (e.symm (e x)) = _
      at hcoord
    rw [hSum.linearIsometryEquiv_symm_apply_single, e.symm_apply_apply, lp.inner_single_left]
      at hcoord
    rw [← hcoord]
    change inner ℂ (P.val.subtypeL (e x P)) x = 0
    rw [← ContinuousLinearMap.adjoint_inner_right, P.val.adjoint_subtypeL, h P, inner_zero_right]
  exact hx (e.injective (hz.trans e.map_zero.symm))

/-- A topologically irreducible isometric action has scalar commutant, and every nonzero
irreducible closed invariant subspace of a Hilbert sum of irreducibles is unitarily equivalent to
one of its summands. -/
theorem unitarySchurHilbertSum : UnitarySchurHilbertSumStatement.{u, v} := by
  constructor
  · intro E _ _ _ M _ ρ hρ hirr B hB
    exact scalarCommutant ρ hρ hirr B hB
  · intro E _ _ _ M _ ρ hρ A _ hA hSum Q hQne hQclosed hQ hQirr
    let : CompleteSpace Q := hQclosed.completeSpace_coe
    let : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQne
    obtain ⟨x, hx⟩ := exists_ne (0 : Q)
    have hxE : (x : E) ≠ 0 := fun h => hx (Subtype.ext h)
    obtain ⟨P, hxP⟩ := exists_summand_projection_ne_zero hSum hxE
    obtain ⟨hP, hPirr⟩ := hA P.val P.property
    let ρQ := IsotypicTrace.restrictAction ρ Q hQ
    let ρP := IsotypicTrace.restrictAction ρ P.val hP
    have hinner := action_inner ρ hρ
    have hinnerQ := IsotypicTrace.restrictAction_inner ρ Q hQ hinner
    have hinnerP := IsotypicTrace.restrictAction_inner ρ P.val hP hinner
    -- The projection is the adjoint of the equivariant inclusion.
    let inclusionP : Archimedean.boundedIntertwiners ρP ρ := ⟨P.val.subtypeL, fun _ _ => rfl⟩
    have hproj (a : M) (z : E) :
        P.val.orthogonalProjectionOnto (ρ a z) = ρP a (P.val.orthogonalProjectionOnto z) := by
      have h := Archimedean.adjoint_mem_boundedIntertwiners ρP ρ hinnerP hinner inclusionP a z
      change adjoint P.val.subtypeL (ρ a z) = ρP a (adjoint P.val.subtypeL z) at h
      simpa only [Submodule.adjoint_subtypeL] using h
    let T : Q →L[ℂ] P.val := P.val.orthogonalProjectionOnto ∘L Q.subtypeL
    have hT (a : M) (z : Q) : T (ρQ a z) = ρP a (T z) := hproj a z
    have hTadj (a : M) (z : P.val) : adjoint T (ρP a z) = ρQ a (adjoint T z) :=
      Archimedean.adjoint_mem_boundedIntertwiners ρQ ρP hinnerQ hinnerP ⟨T, hT⟩ a z
    obtain ⟨c, hc⟩ := scalarCommutant ρQ (fun a z => hρ a z)
      (IsotypicTrace.restrictAction_irreducible ρ Q hQ hQirr) (adjoint T ∘L T) (fun a =>
        ContinuousLinearMap.ext fun z => by
          change adjoint T (T (ρQ a z)) = ρQ a (adjoint T (T z))
          rw [hT, hTadj])
    have hTne : T ≠ 0 := fun h => hxP (congrArg (fun S : Q →L[ℂ] P.val => S x) h)
    -- The scalar Gram operator forces the same norm ratio at every vector.
    have hcNorm : ‖c‖ = ‖T‖ ^ 2 := by
      simpa only [hc, norm_smul, ContinuousLinearMap.norm_id, mul_one, pow_two]
        using T.norm_adjoint_comp_self
    have hnorm (z : Q) : ‖T z‖ = ‖T‖ * ‖z‖ := by
      have hinnerT : inner ℂ (T z) (T z) = c * inner ℂ z z := by
        rw [← T.adjoint_inner_right]
        change inner ℂ z ((adjoint T ∘L T) z) = _
        rw [hc, smul_apply, ContinuousLinearMap.id_apply, inner_smul_right]
      apply (sq_eq_sq₀ (norm_nonneg (T z)) (mul_nonneg (norm_nonneg T) (norm_nonneg z))).mp
      simpa only [inner_self_eq_norm_sq_to_K, norm_mul, norm_pow, RCLike.norm_ofReal,
        abs_norm, hcNorm, mul_pow] using congrArg norm hinnerT
    let s : ℂ := (‖T‖⁻¹ : ℝ)
    have hs : ‖s‖ = ‖T‖⁻¹ :=
      (Complex.norm_real _).trans (Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg T)))
    have hnorm_ne : ‖T‖ ≠ 0 := (norm_ne_zero_iff (a := T)).mpr hTne
    let U : Q →ₗᵢ[ℂ] P.val :=
      { toLinearMap := s • T.toLinearMap
        norm_map' := fun z => by
          change ‖s • T z‖ = ‖z‖
          rw [norm_smul, hs, hnorm, ← mul_assoc, inv_mul_cancel₀ hnorm_ne, one_mul] }
    have hU (a : M) (z : Q) : U (ρQ a z) = ρP a (U z) := by
      change s • T (ρQ a z) = ρP a (s • T z)
      rw [hT, map_smul]
    have hclosed : IsClosed (U.toLinearMap.range : Set P.val) :=
      U.isometry.isUniformInducing.isComplete_range.isClosed
    have hinv : ∀ a, ∀ z ∈ U.toLinearMap.range, ρP a z ∈ U.toLinearMap.range := by
      rintro a _ ⟨z, rfl⟩
      exact ⟨ρQ a z, hU a z⟩
    rcases IsotypicTrace.restrictAction_irreducible ρ P.val hP hPirr _ hclosed hinv with hr | hr
    · exfalso
      apply hx
      apply U.injective
      have hmem : U x ∈ U.toLinearMap.range := ⟨x, rfl⟩
      rw [hr, Submodule.mem_bot] at hmem
      simpa only [map_zero] using hmem
    · refine ⟨P.val, P.property, LinearIsometryEquiv.ofSurjective U (LinearMap.range_eq_top.mp hr),
        fun a z => congrArg Subtype.val (hU a z)⟩

end Langlands.TraceFormula
