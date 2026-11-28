import Langlands.BaseChange.TwistedCharacter.UnramifiedTraceFamily
import Langlands.BaseChange.TwistedCharacter.GLInducedTest
import Langlands.BaseChange.SigmaLiftTransport
import Langlands.Representation.Category.UniverseLift
import Langlands.BaseChange.SigmaOrbitDiscreteness

/-! # Induced twisted traces of equivalent inducing representations -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis MeasureTheory

universe u v w x

section Transport

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E)
  {n : ℕ} (B : BlockShape n)

/-- Transport of a Levi σ-intertwiner along an equivalence of Levi representations. -/
def leviIntertwinerTransport {X : Type w} [AddCommGroup X] [Module ℂ X]
    {Y : Type x} [AddCommGroup Y] [Module ℂ Y]
    {Ξ : Representation ℂ (B.Levi E) X} {Ψ : Representation ℂ (B.Levi E) Y}
    (A : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom)) (e : Ξ.Equiv Ψ) :
    Ψ.Equiv (Ψ.comp (leviAut σ B).toMonoidHom) :=
  (e.symm.trans A).trans (Representation.Equiv.mk e.toLinearEquiv
    (fun m => e.toIntertwiningMap.isIntertwining' (leviAut σ B m)))

omit [TopologicalSpace F] [ValuativeRel E] [IsNonarchimedeanLocalField E] [IsModuleTopology F E] in
/-- The tensor factors of a σ-stable external tensor product of irreducible block
representations are σ-stable. -/
theorem blockFactors_sigmaStable
    (A : ∀ i, SmoothRep.{0, v, max v w} ℂ (GeneralLinear (B.size i) E))
    (hA : ∀ i, (A i).IsIrreducible)
    (h : IsLeviSigmaStable σ B (B.blockTensor (fun i => (A i).representation))) :
    ∀ i, Nonempty ((A i).representation.Equiv
      ((A i).representation.comp (entrywiseAut σ (B.size i)).toMonoidHom)) := by
  classical
  obtain ⟨e⟩ := h
  let ρ (i : Fin B.length) := (A i).representation
  let ρ' (i : Fin B.length) := (ρ i).comp (entrywiseAut σ (B.size i)).toMonoidHom
  have e' : (FiniteTensor.external ρ).Equiv (FiniteTensor.external ρ') :=
    e.trans (equivOfRepresentationEq (blockTensor_comp_leviAut σ B ρ))
  intro i
  obtain ⟨h'⟩ := CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient
    ((CuspidalSupport.isIrreducible_comp_mulEquiv_iff (ρ i) (entrywiseAut σ _)).mpr (hA i)) (hA i)
    (FiniteTensor.isSubquotient_factor_of_external ρ' ρ hA
      (WeylBranchPieces.IsSubquotient.of_equiv e'.symm) i)
  exact ⟨h'.symm⟩

omit [TopologicalSpace F] [IsModuleTopology F E] in
/-- Unnormalized parabolic induction of an admissible Levi representation is admissible. -/
theorem isAdmissible_smoothInduced_levi {X : Type w} [AddCommGroup X] [Module ℂ X]
    (Ξ : Representation ℂ (B.Levi E) X) (hΞ : IsAdmissible Ξ) :
    IsAdmissible (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))) := by
  let T := LocalFieldData.ofInstances E
  let : CompactSpace (Induction.LeftQuotient (B.parabolic E)) :=
    AllField.Parabolic.parabolicQuotientCompact E T B
  exact Induction.smoothInduced_isAdmissible_of_compactSpace _ _
    ((AllField.Parabolic.leviInflationAdmissibility E T B _ _).mpr hΞ)

variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  (μ : Measure (GeneralLinear n E)) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- Equivalent inducing representations with transported σ-intertwiners have the same induced
twisted trace. -/
theorem twistedDistribution_inducedSigma_of_equiv {X : Type w} [AddCommGroup X] [Module ℂ X]
    {Y : Type x} [AddCommGroup Y] [Module ℂ Y]
    (Ξ : Representation ℂ (B.Levi E) X) (Ψ : Representation ℂ (B.Levi E) Y)
    (e : Ξ.Equiv Ψ) (A : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom))
    (hI : IsAdmissible (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))))
    (hJ : IsAdmissible (Induction.smoothInduced (B.parabolic E) (Ψ.comp (B.leviProjection E)))) :
    twistedDistribution μ _ hI (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ A).toLinearMap =
      twistedDistribution μ _ hJ (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ψ
        (leviIntertwinerTransport σ B A e)).toLinearMap := by
  let eP : Representation.Equiv (Ξ.comp (B.leviProjection E)) (Ψ.comp (B.leviProjection E)) :=
    Representation.Equiv.mk e.toLinearEquiv
      (fun q => e.toIntertwiningMap.isIntertwining' (B.leviProjection E q))
  let eI := Induction.smoothInducedEquiv (B.parabolic E) eP
  rw [← twistedDistribution_eq_of_equivalent μ hI hJ eI]
  congr 1

omit [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)] in
theorem inverseHalfModulus_leviAut (m : B.Levi E) :
    ((LocalFieldData.ofInstances E).leviHalfModulus B)⁻¹ (leviAut σ B m) =
      ((LocalFieldData.ofInstances E).leviHalfModulus B)⁻¹ m := by
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, leviHalfModulus_leviAut]

/-- An unnormalized induced twisted trace is the normalized induced twisted trace of the
inducing representation twisted by the inverse half modulus. -/
theorem twistedDistribution_inducedSigma_eq_normalized {Y : Type x} [AddCommGroup Y] [Module ℂ Y]
    (Ψ : Representation ℂ (B.Levi E) Y) (AΨ : Ψ.Equiv (Ψ.comp (leviAut σ B).toMonoidHom))
    (hJ : IsAdmissible (Induction.smoothInduced (B.parabolic E) (Ψ.comp (B.leviProjection E))))
    (hN : IsAdmissible ((LocalFieldData.ofInstances E).normalizedParabolicInduced B
      (twist ((LocalFieldData.ofInstances E).leviHalfModulus B)⁻¹ Ψ))) :
    twistedDistribution μ _ hJ (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ψ AΨ).toLinearMap =
      twistedDistribution μ _ hN (normalizedParabolicSigmaIntertwiner σ B
        (twist ((LocalFieldData.ofInstances E).leviHalfModulus B)⁻¹ Ψ)
        (twistTwistedIntertwiner (leviAut σ B) ((LocalFieldData.ofInstances E).leviHalfModulus B)⁻¹
          (inverseHalfModulus_leviAut σ B) AΨ)).toLinearMap := by
  let κ := (LocalFieldData.ofInstances E).leviHalfModulus B
  have h : Ψ = twist κ (twist κ⁻¹ Ψ) := (twist_twist_inv κ Ψ).symm
  exact twistedDistribution_inducedSigma_congr σ B μ h AΨ
    (twistTwistedIntertwiner (leviAut σ B) κ (leviHalfModulus_leviAut σ B)
      (twistTwistedIntertwiner (leviAut σ B) κ⁻¹ (inverseHalfModulus_leviAut σ B) AΨ)) rfl hJ hN

end Transport

end Langlands.BaseChange
