import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.BaseChange.DistinguishedCompletionGlobalization
import Langlands.BaseChange.SupercuspidalExistenceStatement
import Langlands.Global.CompletionPadic
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport

/-! # Local choices for the conductor globalization -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uF uE uV

namespace Langlands.BaseChange

open GeneralLinear Global Global.AdelicFunctoriality Global.CompletionPadic TraceFormula
open scoped Classical FiniteExtension

/-- The known cyclic globalization and supercuspidal existence propositions
give the distinguished completion, two split supercuspidal places and a
separate split auxiliary place. The family prescribes the original action
at the distinguished place through the field isomorphism. -/
def ConductorGlobalizationChoicesStatement : Prop :=
  CyclicFieldGlobalizationStatement.{uF, uE} →
  SupercuspidalExistenceStatement.{0, uV} →
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type uE) [Field E] [TopologicalSpace E] [ValuativeRel E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear (r + 1) F) V), π.IsIrreducible → IsSupercuspidal π →
    ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : NumberField K) (_ : NumberField L)
      (_ : Algebra K L) (σK : L ≃ₐ[K] L) (_ : IsGalois K L),
      IsCyclicAlgebra σK l ∧
      (∀ w : NumberField.InfinitePlace K, IsCyclicShiftSplit K L w.Completion σK l) ∧
      ∃ (v₀ v₁ v₂ vaux : FinitePlace K) (w₀ : FinitePlacesAbove L v₀)
        (hw : ∀ w : FinitePlacesAbove L v₀, w = w₀)
        (a : F ≃+* v₀.adicCompletion K) (b : E ≃+* w₀.1.adicCompletion L),
        Continuous a ∧ Continuous a.symm ∧ Continuous b ∧ Continuous b.symm ∧
        (∀ x : F, b (algebraMap F E x) = algebraMap (v₀.adicCompletion K) (w₀.1.adicCompletion L) (a x)) ∧
        (∀ x : E, b (σ x) = uniquePlaceCompletionAutEquiv w₀ hw σK (b x)) ∧
        v₁ ≠ v₀ ∧ v₂ ≠ v₀ ∧ v₁ ≠ v₂ ∧ vaux ∉ ({v₀, v₁, v₂} : Finset (FinitePlace K)) ∧
        IsCyclicShiftSplit K L (v₁.adicCompletion K) σK l ∧
        IsCyclicShiftSplit K L (v₂.adicCompletion K) σK l ∧
        IsCyclicShiftSplit K L (vaux.adicCompletion K) σK l ∧
        ∃ (W : FinitePlace K → Type uV) (_ : ∀ v, AddCommGroup (W v)) (_ : ∀ v, Module ℂ (W v))
          (ρ : ∀ v : FinitePlace K, Representation ℂ (GeneralLinear (r + 1) (v.adicCompletion K)) (W v)),
          (∀ v, (ρ v).IsIrreducible ∧ IsSupercuspidal (ρ v)) ∧
          Nonempty (Representation.Equiv (π.comp (Matrix.GeneralLinearGroup.map a.symm.toRingHom)) (ρ v₀))

set_option maxHeartbeats 10000000 in
theorem conductorGlobalizationChoices : ConductorGlobalizationChoicesStatement.{uF, uE, uV} := by
  classical
  intro hglob hex F _ _ _ _ _ E _ _ _ _ _ _ σ l hcyc r V _ _ π hi hs
  obtain ⟨K, L, fK, fL, nK, nL, aKL, σK, hcycK, hInf, hDist, hsplit, -⟩ :=
    hglob F E σ l hcyc (Field.toIsField E)
  let : IsGalois K L := hcycK.isGalois
  obtain ⟨v₀, φ, ψ, hφ, hφ', hφψ, hσ, hψ⟩ := hDist
  obtain ⟨w₀, hw, -, b, hb, hb', hab, hσb⟩ :=
    distinguishedCompletionGlobalization K L v₀ σK F E σ φ ψ hφ hφ' hφψ hσ hψ
  obtain ⟨v₁, h₁, -, hs₁⟩ := hsplit {v₀} 0
  obtain ⟨v₂, h₂, -, hs₂⟩ := hsplit {v₀, v₁} 0
  obtain ⟨vaux, haux, -, hsaux⟩ := hsplit {v₀, v₁, v₂} 0
  have hn₁ : v₁ ≠ v₀ := by simpa only [Finset.mem_singleton] using h₁
  have hn₂ : v₂ ≠ v₀ ∧ v₂ ≠ v₁ := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using h₂
  refine ⟨K, L, fK, fL, nK, nL, aKL, σK, inferInstance, hcycK, hInf,
    v₀, v₁, v₂, vaux, w₀, hw, φ.symm, b, hφ', hφ, hb, hb', hab, hσb,
    hn₁, hn₂.1, hn₂.2.symm, haux, hs₁, hs₂, hsaux, ?_⟩
  let R₀ : Representation ℂ (GeneralLinear (r + 1) (v₀.adicCompletion K)) V :=
    π.comp (Matrix.GeneralLinearGroup.map φ.toRingHom)
  have hs₀ : IsSupercuspidal R₀ := isSupercuspidal_comp_fieldEquiv (r + 1) φ hφ hφ' π hs
  have hi₀ : R₀.IsIrreducible := (isIrreducible_comp_continuousMulEquiv_iff π
    (fieldEquiv (r + 1) φ hφ hφ')).mpr hi
  have hfamily (v : FinitePlace K) :
      ∃ (D : Type uV) (_ : AddCommGroup D) (_ : Module ℂ D)
        (S : Representation ℂ (GeneralLinear (r + 1) (v.adicCompletion K)) D),
        (S.IsIrreducible ∧ IsSupercuspidal S) ∧
        ∀ hv : v = v₀, Nonempty ((show Representation ℂ (GeneralLinear (r + 1) (v.adicCompletion K)) V
          from hv.symm ▸ R₀).Equiv S) := by
    by_cases hv : v = v₀
    · subst v
      exact ⟨V, inferInstance, inferInstance, R₀, ⟨hi₀, hs₀⟩, fun _ => ⟨Representation.Equiv.refl _⟩⟩
    · let : ValuativeRel (v.adicCompletion K) := (topologicalData v).valuativeRel
      let : IsNonarchimedeanLocalField (v.adicCompletion K) := (topologicalData v).localField
      obtain ⟨D, dAdd, dModule, S, -, hiS, hsS, -⟩ := hex (v.adicCompletion K) (r + 1) (Nat.succ_pos r)
      exact ⟨D, dAdd, dModule, S, ⟨hiS, hsS⟩, fun h => False.elim (hv h)⟩
  choose W Wadd Wmodule ρ hρ h₀ using hfamily
  exact ⟨W, Wadd, Wmodule, ρ, hρ, h₀ v₀ rfl⟩

end Langlands.BaseChange
