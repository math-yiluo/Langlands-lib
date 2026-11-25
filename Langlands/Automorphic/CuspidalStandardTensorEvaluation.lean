import Langlands.Automorphic.ArchimedeanStandardAdmissibleProof
import Langlands.Automorphic.ArchimedeanTensorEvaluation
import Langlands.Automorphic.CuspidalArchimedeanComponentIrreducibleProof

/-! # Tensor evaluation at a cuspidal standard-module parameter -/

noncomputable section

open scoped TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Archimedean Langlands.Global Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

section Evaluation

variable {K L V W : Type*} [Group K] [TopologicalSpace K] [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ K V} {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
  {κ : Representation ℂ K W} {ψ : L →ₗ⁅ℂ⁆ Module.End ℂ W}

private theorem densityHyp (hirr : IsIrreducibleGKModule ρ π) (hadm : IsAdmissibleGKModule ρ)
    (hfin : ∀ x, FiniteVectors.IsFiniteVector ρ x)
    (hcont : ∀ (x : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k : K => ℓ (ρ k x)) :
    GKModuleDensity.Hyp ρ π where
  irreducible := hirr
  admissible := hadm
  finite x := ⟨FiniteVectors.orbitSpan ρ x, FiniteVectors.self_mem_orbitSpan ρ x, hfin x,
    fun k _ h => (FiniteVectors.orbitSubrepresentation ρ x).apply_mem_toSubmodule k h⟩
  continuous := hcont

private theorem evaluation_bijective_of_embedding (h : GKModuleDensity.Hyp ρ π)
    (A : V →ₗ[ℂ] W) (hA : A ∈ gkHoms ρ π κ ψ) (hAinj : Function.Injective A)
    (hIso : ∀ (D : Submodule ℂ W) (hD : PlaceComponent.IsIrreducible κ ψ D),
      IsGKIsotypic (PlaceComponent.restrictCompact hD.2.1) (PlaceComponent.restrictLie hD.2.1)
        κ ψ) :
    Function.Bijective (GKTensorEvaluation.evaluation ρ π κ ψ) := by
  let : Nontrivial V := h.irreducible.1
  have hTop : PlaceComponent.IsIrreducible ρ π (⊤ : Submodule ℂ V) :=
    ⟨top_ne_bot, ⟨fun _ _ _ => Submodule.mem_top, fun _ _ _ => Submodule.mem_top⟩,
      fun U _ hU => h.irreducible.2 U hU.1 hU.2⟩
  have hRange0 : LinearMap.range A ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    intro hr
    have hm := LinearMap.mem_range_self A x
    rw [hr, Submodule.mem_bot] at hm
    exact hx (hAinj (hm.trans (map_zero A).symm))
  have hRange : PlaceComponent.IsIrreducible κ ψ (LinearMap.range A) := by
    rw [← Submodule.map_top]
    exact PlaceComponent.isIrreducible_map A hA.1 hA.2 hTop
      (by simpa only [Submodule.map_top] using hRange0)
  let a := A.rangeRestrict
  have haK (k : K) (x : V) :
      a (ρ k x) = PlaceComponent.restrictCompact hRange.2.1 k (a x) :=
    Subtype.ext (hA.1 k x)
  have haL (X : L) (x : V) :
      a (π X x) = PlaceComponent.restrictLie hRange.2.1 X (a x) :=
    Subtype.ext (hA.2 X x)
  refine ⟨GKTensorEvaluation.evaluation_injective ρ π κ ψ h, LinearMap.range_eq_top.mp ?_⟩
  apply top_unique
  have hSpan := hIso (LinearMap.range A) hRange
  unfold IsGKIsotypic at hSpan
  rw [← hSpan]
  refine iSup₂_le fun f hf => ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := A.surjective_rangeRestrict y
  let g : GKTensorEvaluation.Multiplicity ρ π κ ψ := ⟨f.comp a, by
    refine ⟨fun k x => ?_, fun X x => ?_⟩
    · change f (a (ρ k x)) = κ k (f (a x))
      rw [haK, hf.1]
    · change f (a (π X x)) = ψ X (f (a x))
      rw [haL, hf.2]⟩
  exact ⟨x ⊗ₜ[ℂ] g, rfl⟩

end Evaluation

private theorem intertwines_complexification
    {L V W : Type*} [AddCommGroup L] [Module ℝ L]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : ℂ ⊗[ℝ] L →ₗ[ℂ] Module.End ℂ V) (ψ : ℂ ⊗[ℝ] L →ₗ[ℂ] Module.End ℂ W)
    (A : V →ₗ[ℂ] W) (h : ∀ X x, A (π (1 ⊗ₜ X) x) = ψ (1 ⊗ₜ X) (A x))
    (Y : ℂ ⊗[ℝ] L) (x : V) : A (π Y x) = ψ Y (A x) := by
  induction Y using TensorProduct.inductionOn with
  | tmul c X =>
    have he : c ⊗ₜ[ℝ] X = c • (1 ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he]
    simp only [map_smul, LinearMap.smul_apply, h]
  | add X Y hX hY => simp only [map_add, LinearMap.add_apply, hX, hY]

universe u

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- At either kind of infinite place, a standard-module parameter of an actual
cuspidal realization gives a bijective tensor evaluation onto the realization.
The multiplicity factor consists of all simultaneous compact and Lie intertwiners
from that standard module to the realization. -/
def CuspidalStandardTensorEvaluationStatement (T : CuspidalOperatorRealization F r) : Prop :=
  (∀ (v : {v : NumberField.InfinitePlace F // v.IsReal}) (ds : List RealBlock),
    T.realization.HasRealPlaceParameter v ds →
      Function.Bijective (GKTensorEvaluation.evaluation (realStandardRep (r + 1) ds)
        (realStandardLie (r + 1) ds) (T.realization.realPlaceCompactRepresentation v)
        (T.realization.realPlaceLieAction v))) ∧
  ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex}) (ds : List ComplexCharacterData),
    T.realization.HasComplexPlaceParameter v ds →
      Function.Bijective (GKTensorEvaluation.evaluation (complexStandardRep (r + 1) ds)
        (complexStandardLie (r + 1) ds) (T.realization.complexPlaceCompactRepresentation v)
        (T.realization.complexPlaceLieAction v))

namespace CuspidalOperatorRealization

/-- Isotypy gives surjectivity of tensor evaluation, and density for the irreducible
admissible standard module gives injectivity. -/
theorem standardTensorEvaluation (T : CuspidalOperatorRealization F r) :
    CuspidalStandardTensorEvaluationStatement T := by
  constructor
  · intro v ds hp
    have hgk := isRealGKModule_realStandardModule (r + 1) ds
    have hd := densityHyp (T.isIrreducibleRealStandard v ds hp)
      (realStandardAdmissible (r + 1) ds) hgk.1 hgk.2.1
    obtain ⟨_, A, hA, hK, hL⟩ := hp
    exact evaluation_bijective_of_embedding hd A
      ⟨OperatorRealization.realPlaceParameter_compact hK,
        intertwines_complexification _ _ A (OperatorRealization.realPlaceParameter_lie hL)⟩
      hA (fun _ hD => T.isRealPlaceIsotypic_restrict v hD)
  · intro v ds hp
    have hgk := isComplexGKModule_complexStandardModule (r + 1) ds
    have hd := densityHyp (T.isIrreducibleComplexStandard v ds hp)
      (complexStandardAdmissible (r + 1) ds) hgk.1 hgk.2.1
    obtain ⟨_, A, hA, hK, hL⟩ := hp
    exact evaluation_bijective_of_embedding hd A
      ⟨OperatorRealization.complexPlaceParameter_compact hK,
        intertwines_complexification _ _ A (OperatorRealization.complexPlaceParameter_lie hL)⟩
      hA (fun _ hD => T.isComplexPlaceIsotypic_restrict v hD)

end CuspidalOperatorRealization
end Langlands.Automorphic
