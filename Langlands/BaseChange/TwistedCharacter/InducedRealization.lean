import Langlands.BaseChange.TwistedInductionSpans
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Smooth.SmallRealizationProof

/-! # Changing the carrier universe of actual twisted inducing data -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis MeasureTheory TopologicalSpace

universe u v z w

variable {F : Type u} [CommRing F] [TopologicalSpace F]
  {E : Type v} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
  [Algebra F E] [IsModuleTopology F E] {n : ℕ} (σ : E ≃ₐ[F] E)
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  (μ : Measure (GeneralLinear n E)) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- When the Levi is separable, an actual proper induced trace from an
irreducible admissible stable pair belongs to the proper-induction span
with inducing carriers in any prescribed universe. -/
theorem twistedDistribution_mem_sigmaProperInducedSpan_of_separable
    (B : BlockShape n) (hB : 2 ≤ B.length) [SeparableSpace (B.Levi E)]
    {X : Type w} [AddCommGroup X] [Module ℂ X]
    (Ξ : Representation ℂ (B.Levi E) X) (hΞ : IsAdmissible Ξ) (hΞirr : Ξ.IsIrreducible)
    (A : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom))
    (hI : IsAdmissible (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E)))) :
    twistedDistribution μ _ hI (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ A).toLinearMap ∈
      sigmaProperInducedSpan.{u,v,z} σ μ := by
  obtain ⟨R, hRirr, ⟨e⟩⟩ := exists_irreducible_smoothRep_equiv_of_separable.{v,w,z}
    (SmoothRep.of Ξ hΞ.1) hΞirr
  let ρ := R.representation
  let θ := leviAut σ B
  let eθ : Representation.Equiv (Ξ.comp θ.toMonoidHom) (ρ.comp θ.toMonoidHom) :=
    Representation.Equiv.mk e.toLinearEquiv (fun g => e.isIntertwining' (θ g))
  let A' : ρ.Equiv (ρ.comp θ.toMonoidHom) := (e.symm.trans A).trans eθ
  let P := B.parabolic E
  let p := B.leviProjection E
  let ep : Representation.Equiv (Ξ.comp p) (ρ.comp p) :=
    Representation.Equiv.mk e.toLinearEquiv (fun g => e.isIntertwining' (p g))
  let eI := Induction.smoothInducedEquiv P ep
  let T := TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ A
  let T' := TwistedPaleyWiener.inducedSigmaIntertwiner σ B ρ A'
  have hI' := isAdmissible_of_equiv eI hI
  have htrace : twistedDistribution μ _ hI T.toLinearMap =
      twistedDistribution μ _ hI' T'.toLinearMap := by
    refine twistedDistribution_eq_of_equivariant μ _ hI _ hI' _ _ eI.toLinearEquiv
      (fun g v => eI.toIntertwiningMap.isIntertwining _ _ g v) ?_
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change Induction.eval P (ρ.comp p) (eI (T f)) g =
      Induction.eval P (ρ.comp p) (T' (eI f)) g
    let x := Induction.eval P (Ξ.comp p) f ((entrywiseAut σ n).symm g)
    change e (A x) = e (A (e.symm (e x)))
    rw [e.symm_apply_apply]
  change twistedDistribution μ _ hI T.toLinearMap ∈ _
  rw [htrace]
  exact twistedDistribution_mem_sigmaProperInducedSpan σ μ B hB ρ
    (isAdmissible_of_equiv e hΞ) hRirr A' hI'

end Langlands.BaseChange
