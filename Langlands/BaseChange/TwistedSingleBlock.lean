import Langlands.BaseChange.TwistedPseudoCoefficientOrbitSeparation
import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.Classification.InverseTransposeAnalyticProof

/-! # Regularity on the one-block family by evaluation at the identity -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear

universe u v z

section SingleBlock

variable {F : Type u} [CommRing F] [TopologicalSpace F]
  {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {n : ℕ} (σ : E ≃ₐ[F] E) (B : BlockShape n) (hB : B.length = 1)
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  (μ : Measure (GeneralLinear n E)) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  {X : Type z} [AddCommGroup X] [Module ℂ X]

local notation "θ" => entrywiseAut σ n
local notation "e" => B.singleBlockLeviEquivContinuous hB E

omit [TopologicalSpace F] [IsModuleTopology F E] [MeasurableSpace (GeneralLinear n E)]
  [BorelSpace (GeneralLinear n E)] [T2Space (GeneralLinear n E)]
  [LocallyCompactSpace (GeneralLinear n E)] [TotallyDisconnectedSpace (GeneralLinear n E)] in
private theorem singleBlock_sigma (g : GeneralLinear n E) :
    (e).symm (θ g) = leviAut σ B ((e).symm g) := by
  apply (e).injective
  change e ((e).symm (θ g)) = B.leviEmbedding E (leviAut σ B ((e).symm g))
  rw [(e).apply_symm_apply, ← entrywiseAut_leviEmbedding]
  exact congrArg θ ((e).apply_symm_apply g).symm

/-- Evaluation at the identity transports the twisting operator on a one-block induction
exactly, not just up to scalar. -/
theorem twistedDistribution_singleBlock (Ξ : Representation ℂ (B.Levi E) X)
    (BΞ : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom))
    (hI : IsAdmissible (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))))
    (hρ : IsAdmissible (Ξ.comp (e).symm.toMonoidHom)) :
    twistedDistribution μ _ hI (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ BΞ).toLinearMap =
      twistedDistribution μ _ hρ BΞ.toLinearMap := by
  let ev := Induction.smoothInducedTopEquiv (B.parabolic E) (B.singleBlock_parabolic_eq_top hB E)
    (Ξ.comp (B.leviProjection E)) (Ξ.comp (e).symm.toMonoidHom)
    (fun p => rfl) hρ.1
  refine twistedDistribution_eq_of_equivariant μ _ hI _ hρ _ _ ev.toLinearEquiv
    (fun g f => ev.toIntertwiningMap.isIntertwining _ _ g f) ?_
  intro f
  change Induction.eval _ _ (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ BΞ f) 1 = BΞ (Induction.eval _ _ f 1)
  rw [TwistedPaleyWiener.eval_inducedSigmaIntertwiner, map_one]

variable (L N : Submodule ℂ (Distribution (GeneralLinear n E)))
  (Φ : Module.Dual ℂ (Distribution (GeneralLinear n E))) (f₀ : SchwartzBruhat (GeneralLinear n E))

include hB

/-- A spectral splitting stable under invariant unramified twists establishes regularity
of a one-block family. Its values are those of the orbit component on character multiples
of the fixed test `f₀`. -/
theorem exists_oneBlock_regular_of_spectrum_split
    (hL : ∀ (ψ : GeneralLinear n E →* ℂˣ) (hψ : IsUnramifiedCharacter ψ),
      (∀ g, ψ (θ g) = ψ g) → L.map (characterTwistDistribution ψ hψ.isOpen_ker) ≤ L)
    (hN : ∀ (ψ : GeneralLinear n E →* ℂˣ) (hψ : IsUnramifiedCharacter ψ),
      (∀ g, ψ (θ g) = ψ g) → N.map (characterTwistDistribution ψ hψ.isOpen_ker) ≤ N)
    (hagree : ∀ d ∈ L, Φ d = d f₀) (hkill : ∀ d ∈ N, Φ d = 0)
    (hspan : twistedSpectrumSpan.{v,z} μ θ (fun _ _ _ _ => True) ≤ L ⊔ N)
    (Ξ : Representation ℂ (B.Levi E) X) (hΞ : IsAdmissible Ξ) (hirr : Ξ.IsIrreducible)
    (BΞ : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom)) :
    ∃ (s : Finset (B.Levi E)) (c : B.Levi E → ℂ),
      ∀ (ψ : B.Levi E →* ℂˣ), IsUnramifiedCharacter ψ →
        ∀ (hψ : ∀ m, ψ (leviAut σ B m) = ψ m)
          (hI : IsAdmissible (Induction.smoothInduced (B.parabolic E)
            ((twist ψ Ξ).comp (B.leviProjection E)))),
          Φ (twistedDistribution μ _ hI (TwistedPaleyWiener.inducedSigmaIntertwiner σ B (twist ψ Ξ)
            (twistTwistedIntertwiner (leviAut σ B) ψ hψ BΞ)).toLinearMap) =
            ∑ m ∈ s, c m * (ψ m : ℂ) := by
  let ρ : Representation ℂ (GeneralLinear n E) X := Ξ.comp (e).symm.toMonoidHom
  have hρ := isAdmissible_comp_continuousMulEquiv Ξ (e).symm hΞ
  have hρirr := (isIrreducible_comp_continuousMulEquiv_iff Ξ (e).symm).mpr hirr
  let A : SigmaIntertwiner σ n ρ := Representation.Equiv.mk BΞ.toLinearEquiv (fun g => by
    change BΞ.toLinearMap ∘ₗ Ξ ((e).symm g) = Ξ ((e).symm (θ g)) ∘ₗ BΞ.toLinearMap
    rw [singleBlock_sigma σ B hB]
    exact BΞ.isIntertwining' ((e).symm g))
  obtain ⟨dL, hdL, dN, hdN, hd⟩ := Submodule.mem_sup.mp (hspan
    (twistedDistribution_mem_twistedSpectrumSpan μ θ (fun _ _ _ _ => True) hρ hρirr trivial A))
  obtain ⟨s, c, hc⟩ := exists_regular_characterTwistDistribution dL f₀
  refine ⟨s.map (e).symm.toEquiv.toEmbedding, fun m => c (e m), fun ψ hψ hψσ hI => ?_⟩
  let ψG := ψ.comp (e).symm.toMonoidHom
  have hunr : IsUnramifiedCharacter ψG := hψ.comp_of_continuous _ (e).symm.continuous
  have hinv (g : GeneralLinear n E) : ψG (θ g) = ψG g := by
    change ψ ((e).symm (θ g)) = ψ ((e).symm g)
    rw [singleBlock_sigma σ B hB, hψσ]
  let D := characterTwistDistribution ψG hunr.isOpen_ker
  have hL' : D dL ∈ L := hL ψG hunr hinv (Submodule.mem_map_of_mem hdL)
  have hN' : D dN ∈ N := hN ψG hunr hinv (Submodule.mem_map_of_mem hdN)
  have htwAdm := (isAdmissible_twist_iff ψG ρ hunr.isOpen_ker).mpr hρ
  have hdist : twistedDistribution μ _ hI (TwistedPaleyWiener.inducedSigmaIntertwiner σ B
      (twist ψ Ξ) (twistTwistedIntertwiner (leviAut σ B) ψ hψσ BΞ)).toLinearMap =
        twistedDistribution μ (twist ψG ρ) htwAdm A.toLinearMap :=
    twistedDistribution_singleBlock σ B hB μ (twist ψ Ξ) _ hI htwAdm
  rw [hdist, twistedDistribution_twist_eq_comp μ ρ hρ A.toLinearMap ψG hunr.isOpen_ker htwAdm]
  change Φ (D (twistedDistribution μ ρ hρ A.toLinearMap)) = _
  rw [← hd, map_add D, map_add Φ, hagree _ hL', hkill _ hN', add_zero, hc ψG hunr, Finset.sum_map]
  refine Finset.sum_congr rfl fun g _ => ?_
  change c g * (ψ ((e).symm g) : ℂ) = c (e ((e).symm g)) * (ψ ((e).symm g) : ℂ)
  rw [(e).apply_symm_apply]

end SingleBlock

end Langlands.BaseChange
