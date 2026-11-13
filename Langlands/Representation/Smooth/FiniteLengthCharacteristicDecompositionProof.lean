import Langlands.Representation.Smooth.FiniteLengthCharacteristicDecompositionStatement
import Langlands.Representation.Intertwining.PQFiniteLengthAction
import Langlands.Representation.Smooth.CentralOperatorExpansionProof
import Langlands.Representation.Exponents.FiniteActionSpectrumProof
import Mathlib.LinearAlgebra.Eigenspace.Pi

/-!
# Characteristic decomposition in finite length

Renard III.1.10, Proposition, finite-length case, obtained from the finite
central operator span and simultaneous generalized eigenspace independence.
-/

noncomputable section

namespace Langlands

universe uG uV

/-- The finite-length characteristic decomposition for every central subgroup. -/
theorem finiteLengthCharacteristicDecomposition :
    FiniteLengthCharacteristicDecompositionStatement.{uG, uV} := by
  intro G _ _ _ _ _ _ _ Z hZ A hfl
  let : CommGroup Z :=
    { (inferInstance : Group Z) with
      mul_comm := fun z t => Subtype.ext (Subgroup.mem_center_iff.mp (hZ t.property) z) }
  let c : Z →* Subgroup.center G :=
    { toFun := fun z => ⟨z.val, hZ z.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let τ : Representation ℂ Z A := A.representation.comp Z.subtype
  have hfin : Module.Finite ℂ (Submodule.span ℂ (Set.range τ)) :=
    PQFiniteLengthAction.centralActionSpan_finite A.representation c A.isSmooth hfl
  let : IsNoetherian (MonoidAlgebra ℂ G) A.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
  have hfg : Module.Finite (MonoidAlgebra ℂ G) A.representation.asModule := inferInstance
  have hc : Continuous c := continuous_subtype_val.subtype_mk _
  have hloc : IsLocallyConstant (fun z : Z => τ z) :=
    centralAction_isLocallyConstant A.representation c hc A.isSmooth hfg
  obtain ⟨hS, -, hspanS⟩ := finiteActionCommutativeSpectrum Z A τ hfin hloc
  have hi : iSupIndep (fun χ : Z →* ℂˣ =>
      (generalizedCommutativeCharacterSpace τ χ).toSubmodule) := by
    have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
      (fun z : Z => τ z)
      (fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (by
        change Commute (τ j) (τ i)
        exact (show Commute j i from mul_comm j i).map τ) μ)
    let charValue : (Z →* ℂˣ) → (Z → ℂ) := fun χ z => (χ z : ℂ)
    have hinj : Function.Injective charValue := by
      intro χ ψ h
      apply MonoidHom.ext
      intro z
      apply Units.ext
      exact congrFun h z
    apply (hind.comp hinj).mono
    intro χ v hv
    obtain ⟨n, hn⟩ := (mem_generalizedCommutativeCharacterSpace τ χ v).mp hv
    change v ∈ ⨅ z : Z, Module.End.maxGenEigenspace (τ z) (χ z : ℂ)
    rw [Submodule.mem_iInf]
    intro z
    exact Module.End.mem_genEigenspace_top.mpr ⟨n, hn z⟩
  have hspan : (⨆ χ : Z →* ℂˣ,
      (generalizedCommutativeCharacterSpace τ χ).toSubmodule) = ⊤ := by
    apply top_unique
    rw [← hspanS]
    exact iSup_le fun χ => iSup_le fun _ =>
      le_iSup (fun ψ : Z →* ℂˣ => (generalizedCommutativeCharacterSpace τ ψ).toSubmodule) χ
  have hsupport : {χ : Z →* ℂˣ |
      (generalizedCommutativeCharacterSpace τ χ).toSubmodule ≠ ⊥}.Finite :=
    hS.subset (fun χ hχ => hi.mem_of_biSup_eq_top hspanS hχ)
  have heq (χ : Z →* ℂˣ) :
      (generalizedCommutativeCharacterSpace τ χ).toSubmodule =
        ⨆ m : ℕ, ⨅ z : Z,
          LinearMap.ker ((A.representation (z : G) - (χ z : ℂ) • LinearMap.id) ^ m) := by
    change (⨆ m : ℕ, (commutativeCharacterSpace τ χ m).toSubmodule) = _
    apply iSup_congr
    intro m
    ext v
    change v ∈ commutativeCharacterSpace τ χ m ↔ _
    rw [mem_commutativeCharacterSpace]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  dsimp only
  simp_rw [← heq]
  exact ⟨hi, hspan, hsupport⟩

end Langlands
