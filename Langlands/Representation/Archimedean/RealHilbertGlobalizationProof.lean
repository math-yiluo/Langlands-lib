import Langlands.Representation.Archimedean.RealFrobeniusCharacter
import Langlands.Representation.Archimedean.HilbertGlobalizationStatement
import Langlands.Representation.Archimedean.RealFrobeniusHilbertAdmissibility
import Langlands.Representation.Archimedean.RealFrobeniusSmoothDensity
import Langlands.Representation.Archimedean.RealPrincipalSeriesSubrepresentationProof
import Langlands.Representation.Archimedean.SmoothHilbertExponential
import Langlands.Representation.Archimedean.SmoothHilbertTransport

/-! # Hilbert globalization of real general linear GK modules -/

noncomputable section

open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

universe uV uH

@[instance_reducible]
private def uliftInnerProductSpace (E : Type uH) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    InnerProductSpace ℂ (ULift.{uV} E) where
  toNormedSpace := ULift.normedSpace
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner x := InnerProductSpace.norm_sq_eq_re_inner x.down
  conj_inner_symm x y := InnerProductSpace.conj_inner_symm x.down y.down
  add_left x y z := InnerProductSpace.add_left x.down y.down z.down
  smul_left x y c := InnerProductSpace.smul_left x.down y.down c

section Transport

variable {F : Type} [RCLike F] {n : ℕ} {E E' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) F) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) F) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {R : Langlands.GeneralLinear n F →* (E →L[ℂ] E)} (T : E ≃L[ℂ] E')
  {e : V ≃ₗ[ℂ] smoothHilbertKFinite F n R}

local notation "S" => transportRepresentation T R
local notation "I" => matrixModel F n

private theorem isSmoothHilbertGlobalization_transport (h : IsSmoothHilbertGlobalization F n R ρ π e) :
    IsSmoothHilbertGlobalization F n S ρ π (e.trans (smoothHilbertKFiniteTransport F n T R)) := by
  let A := smoothHilbertGlobalizationMap F n R e
  let B := derivativeSmoothTransport I T R
  have hB : smoothHilbertGlobalizationMap F n S (e.trans (smoothHilbertKFiniteTransport F n T R)) =
      B.toLinearMap.comp A := rfl
  obtain ⟨⟨hc, hi, ha⟩, hd, hk, hl, -⟩ := h
  refine ⟨⟨IsContinuousRepresentation.transport T R hc, IsTopologicallyIrreducible.transport T R hi,
    IsAdmissible.transport T R ha⟩, ?_, ?_, ?_, hasSmoothHilbertExponentialDerivatives F n S⟩
  · rw [hB]
    exact B.surjective.denseRange.comp hd (continuous_derivativeSmoothTransport I T R)
  · intro k v
    rw [hB]
    change B (A (ρ k v)) = _
    rw [show A (ρ k v) = _ from hk k v]
    exact derivativeSmoothTransport_representation I T R (Unitary.toUnits k) (A v)
  · intro X v
    rw [hB]
    change B (A (π (1 ⊗ₜ X) v)) = _
    rw [show A (π (1 ⊗ₜ X) v) = _ from hl X v]
    exact derivativeSmoothTransport_operator I T R X (A v)

end Transport

set_option maxHeartbeats 600000 in
private theorem exists_uliftGlobalization {n : ℕ} {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
    {R : Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E)} {e : V ≃ₗ[ℂ] smoothHilbertKFinite ℝ n R}
    (h : IsSmoothHilbertGlobalization ℝ n R ρ π e) :
    ∃ (H : Type uV) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (S : Langlands.GeneralLinear n ℝ →* (H →L[ℂ] H))
      (e' : V ≃ₗ[ℂ] smoothHilbertKFinite ℝ n S), IsSmoothHilbertGlobalization ℝ n S ρ π e' := by
  let H := ULift.{uV} E
  let _ : InnerProductSpace ℂ H := uliftInnerProductSpace E
  let T : E ≃L[ℂ] H := (ContinuousLinearEquiv.ulift (R₁ := ℂ)).symm
  let S := transportRepresentation T R
  let e' := e.trans (smoothHilbertKFiniteTransport ℝ n T R)
  let liftCompatibility := isSmoothHilbertGlobalization_transport (F := ℝ) (n := n) (E := E) (E' := H)
    (R := R) (e := e) (ρ := ρ) (π := π) T
  have h' := liftCompatibility h
  refine ⟨H, ?_⟩
  refine ⟨ULift.normedAddCommGroup, ?_⟩
  refine ⟨‹InnerProductSpace ℂ H›, ?_⟩
  refine ⟨ULift.instCompleteSpace, ?_⟩
  refine ⟨S, ?_⟩
  refine ⟨e', ?_⟩
  exact h'

section Frobenius

open RealPrincipalSeriesHilbert

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ℓ : V →ₗ[ℂ] ℂ} {a : Fin n → ℂ} {eps : Fin n → Fin 2}
  (hgk : IsRealGKModule n ρ π) (hℓ : IsRealJacquetFunctional n ρ π ℓ a eps)
  (hi : IsIrreducibleGKModule ρ π) (ha : IsAdmissibleGKModule ρ) (h₀ : ℓ ≠ 0)

local notation "W" => (frobeniusClosure hgk hℓ : Type)
local notation "R" => frobeniusClosureRepresentation hgk hℓ

include hgk hℓ hi ha h₀ in
set_option maxHeartbeats 1200000 in
private theorem exists_hilbertGlobalization_of_isRealJacquetFunctional :
    ∃ (H : Type uV) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (S : Langlands.GeneralLinear n ℝ →* (H →L[ℂ] H))
      (e : V ≃ₗ[ℂ] smoothHilbertKFinite ℝ n S), IsSmoothHilbertGlobalization ℝ n S ρ π e := by
  obtain ⟨e, he⟩ := RealPrincipalSeriesHilbert.exists_frobeniusEquiv_globalization hgk hℓ hi ha h₀
  have hW : CompleteSpace W := (isClosed_frobeniusClosure hgk hℓ).isComplete.completeSpace_coe
  let liftGlobalization := @exists_uliftGlobalization n W
    (Submodule.normedAddCommGroup (frobeniusClosure hgk hℓ))
    (Submodule.innerProductSpace (frobeniusClosure hgk hℓ)) hW
  exact @liftGlobalization V ‹AddCommGroup V› ‹Module ℂ V› ρ π R e he

end Frobenius

/-- Real general linear Hilbert globalization with the genuine smooth topology. -/
theorem realHilbertGlobalization : RealHilbertGlobalizationStatement.{uV} := by
  intro r V _ _ ρ π hgk hirr hadm
  have hj := realJacquetModuleFinite_of_finiteDimensional_of_nonvanishing
    (realJacquetFiniteDimensional_of_finiteGeneration
      RealJacquetFiniteGeneration.realJacquetFiniteGeneration)
    (RealJacquetNonvanishing.realJacquetNonvanishingSubquotientReduction realPrincipalSeriesSubquotient)
  obtain ⟨hfin, hne⟩ := hj (r + 1) V ρ π hgk hirr hadm
  obtain ⟨ℓ, a, eps, h₀, hℓ⟩ := exists_isRealJacquetFunctional hgk hfin hne
  exact exists_hilbertGlobalization_of_isRealJacquetFunctional hgk hℓ hirr hadm h₀

end Langlands.Archimedean
