import Langlands.BaseChange.TwistedCharacter.SupportSelection
import Langlands.BaseChange.TwistedCharacter.OrbitTriangularSeparation
import Langlands.BaseChange.TwistedCharacter.Devissage
import Langlands.BaseChange.TwistedPseudoCoefficientSupportProjection

/-! # Separation of the orbit from the compact-level complement over a p-adic field -/

noncomputable section

namespace Langlands.BaseChange

open CategoryTheory Classification GeneralLinear HarmonicAnalysis MeasureTheory
open PadicField.TopologicalData

universe u v z

section Padic

variable {F : Type u} [Field F] [TopologicalSpace F] {p : ℕ} [Fact p.Prime]
  {E : PadicField.{v} p} [Algebra F E.Carrier] (T : E.TopologicalData)
  (hModule : letI := T.topology; IsModuleTopology F E.Carrier)
  (σ : E.Carrier ≃ₐ[F] E.Carrier)

set_option maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- A proper σ-induced twisted trace from an irreducible admissible inducing representation
lies in the span of the selected irreducible classes or in the span of the others. All
irreducible subquotients of the induced representation have one supercuspidal support. -/
theorem properInduced_mem_selection_or_complement {n : ℕ} (hn : 0 < n)
    (s : Multiset (CuspidalDatum.{z, v} T)) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := hModule
    ∀ [T2Space (GeneralLinear n E.Carrier)]
      [LocallyCompactSpace (GeneralLinear n E.Carrier)]
      [TotallyDisconnectedSpace (GeneralLinear n E.Carrier)]
      [MeasurableSpace (GeneralLinear n E.Carrier)] [BorelSpace (GeneralLinear n E.Carrier)]
      (μ : Measure (GeneralLinear n E.Carrier)) [IsFiniteMeasureOnCompacts μ]
      [μ.IsMulLeftInvariant]
      (B : BlockShape n) {X : Type z} [AddCommGroup X] [Module ℂ X]
      (Ξ : Representation ℂ (B.Levi E.Carrier) X), IsAdmissible Ξ → Ξ.IsIrreducible →
      ∀ (A : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom))
        (h : IsAdmissible (Induction.smoothInduced (B.parabolic E.Carrier)
          (Ξ.comp (B.leviProjection E.Carrier)))),
        twistedDistribution μ _ h (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ A).toLinearMap ∈
            twistedSpectrumSpan μ (entrywiseAut σ n) (supportTwistSelection T n s) ∨
          twistedDistribution μ _ h
              (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ A).toLinearMap ∈
            twistedSpectrumSpan.{v,z} μ (entrywiseAut σ n)
              (fun W _ _ π => ¬ supportTwistSelection T n s W π) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  intro _ _ _ _ _ μ _ _ B X _ _ Ξ hΞ hirr A h
  let := T.generalLinearTopologicalGroup n
  let := T.generalLinearSecondCountableTopology n
  let θ := entrywiseAut σ n
  let Ξu := universeLiftRepresentation.{v} Ξ
  let κ := (LocalFieldData.ofInstances E.Carrier).leviHalfModulus B
  have hκinv : IsOpen ((κ⁻¹).ker : Set (B.Levi E.Carrier)) := by
    have hk : (κ⁻¹).ker = κ.ker := by
      ext m
      simp
    rw [hk]
    exact (LocalFieldData.ofInstances E.Carrier).isOpen_ker_leviHalfModulus B
  let Ξ0 := twist κ⁻¹ Ξu
  have hΞ0 : IsAdmissible Ξ0 :=
    (isAdmissible_twist_iff _ _ hκinv).mpr ((isAdmissible_universeLift_iff Ξ).mpr hΞ)
  have hirr0 : Ξ0.IsIrreducible :=
    (isIrreducible_twist_iff _ _).mpr ((isIrreducible_universeLift_iff Ξ).mpr hirr)
  obtain ⟨Af, hAfirr, -, ⟨eΞ⟩⟩ :=
    CuspidalSupport.padicLeviAdmissibleFactorization.{v, max v z} p E T n hn B
      (SmoothRep.of Ξ0 hΞ0.1) hirr0 hΞ0
  let Xs := (T.normalizedProductInductionFunctor B).obj Af
  let eLevi : Ξ.Equiv (twist κ (B.blockTensor fun i => (Af i).representation)) :=
    (universeLiftEquiv.{v} Ξ).trans
      ((equivOfRepresentationEq (twist_twist_inv κ Ξu).symm).trans (twistEquiv κ eΞ))
  let eP : Representation.Equiv (Ξ.comp (B.leviProjection E.Carrier))
      ((twist κ (B.blockTensor fun i => (Af i).representation)).comp
        (B.leviProjection E.Carrier)) :=
    Representation.Equiv.mk eLevi.toLinearEquiv
      (fun q => eLevi.toIntertwiningMap.isIntertwining' (B.leviProjection E.Carrier q))
  let eI : (Induction.smoothInduced (B.parabolic E.Carrier)
      (Ξ.comp (B.leviProjection E.Carrier))).Equiv Xs.representation :=
    Induction.smoothInducedEquiv (B.parabolic E.Carrier) eP
  have hXadm : Xs.IsAdmissible := isAdmissible_of_equiv eI h
  have hXfin : Xs.HasFiniteLength :=
    irreducibleProductFiniteLength.{v, max v z} E T n hn B Af hAfirr
  obtain ⟨s', hs'⟩ := exists_supercuspidalSupport_of_normalizedProduct.{v, z} T B Af hAfirr
  let A' := SigmaIntertwiner.transport (σ := σ)
    (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ A) eI
  have hd : twistedDistribution μ _ h (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ A).toLinearMap =
      twistedDistribution μ Xs.representation hXadm A'.toLinearMap :=
    (twistedDistribution_eq_of_equivalent μ h hXadm eI _).symm
  have hshrink (L : Submodule ℂ (Distribution (GeneralLinear n E.Carrier)))
      (hmem : ∀ (D : SmoothRep.{0, v, max v z} ℂ (GeneralLinear n E.Carrier)), D.IsIrreducible →
        SmoothRep.IsSubquotient D Xs → ∀ (Dz : SmoothRep.{0, v, z} ℂ (GeneralLinear n E.Carrier))
          (hDz : Dz.IsAdmissible), Dz.IsIrreducible →
          Nonempty (Dz.representation.Equiv D.representation) →
          ∀ ADz : Dz.representation.Equiv (Dz.representation.comp θ.toMonoidHom),
            twistedDistribution μ Dz.representation hDz ADz.toLinearMap ∈ L) :
      twistedDistribution μ Xs.representation hXadm A'.toLinearMap ∈ L := by
    refine twistedDistribution_mem_of_finiteLength.{v, max v z} μ θ L Xs hXadm hXfin A' ?_
    intro D hD hDirr hsub AD
    obtain ⟨Dz, hDzirr, ⟨eD⟩⟩ :=
      exists_irreducible_smoothRep_equiv_of_separable.{v, max v z, z} D hDirr
    have hDz : IsAdmissible Dz.representation := isAdmissible_of_equiv eD hD
    rw [← twistedDistribution_eq_of_equivalent μ hD hDz eD AD.toLinearMap]
    exact hmem D hDirr hsub Dz hDz hDzirr ⟨eD.symm⟩ (SigmaIntertwiner.transport (σ := σ) AD eD)
  rw [hd]
  by_cases hQ : ∃ c : ℂˣ, s'.map (CuspidalDatum.characterTwist (unramifiedFieldCharacter T c)) = s
  · left
    refine hshrink _ fun D hDirr hsub Dz hDz hDzirr he ADz => ?_
    exact twistedDistribution_mem_twistedSpectrumSpan μ θ _ hDz hDzirr
      ((supportTwistSelection_iff T hn s s' D hDirr (hs' D hDirr hsub) Dz.representation
        he.some).mpr hQ) ADz
  · right
    refine hshrink _ fun D hDirr hsub Dz hDz hDzirr he ADz => ?_
    exact twistedDistribution_mem_twistedSpectrumSpan μ θ _ hDz hDzirr
      (fun hS => hQ ((supportTwistSelection_iff T hn s s' D hDirr (hs' D hDirr hsub)
        Dz.representation he.some).mp hS)) ADz

set_option maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Over a p-adic field, the orbit span of a σ-discrete series is disjoint from the complementary
span at one compact open level. -/
theorem exists_compact_disjoint_twistedOrbitSpan_complement_padic {n : ℕ} (hn : 0 < n)
    {d : ℕ} (hd : 0 < d) (hσ : σ ^ d = 1)
    {W : Type z} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GeneralLinear n E.Carrier) W)
    (hτ : letI := T.topology; letI := T.valuativeRel; letI := T.localField;
      IsSigmaDiscreteSeries σ n τ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := hModule
    ∀ [T2Space (GeneralLinear n E.Carrier)]
      [LocallyCompactSpace (GeneralLinear n E.Carrier)]
      [TotallyDisconnectedSpace (GeneralLinear n E.Carrier)]
      [MeasurableSpace (GeneralLinear n E.Carrier)] [BorelSpace (GeneralLinear n E.Carrier)]
      (μ : Measure (GeneralLinear n E.Carrier)) [μ.IsHaarMeasure],
      ∃ J : OpenSubgroup (GeneralLinear n E.Carrier),
        IsCompact (J : Set (GeneralLinear n E.Carrier)) ∧
        Disjoint (twistedOrbitSpan μ (entrywiseAut σ n) τ)
          (twistedPseudoCoefficientComplementSpan σ μ τ J) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := hModule
  intro _ _ _ _ _ μ _
  let := T.generalLinearTopologicalGroup n
  have hSep := disjoint_twistedOrbitSpan_otherTempered_sup_properInduced T hModule σ hn hd hσ τ hτ μ
  have hθ := exists_compact_openSubgroup_symm_mem (entrywiseAut σ n) (continuous_entrywiseAut σ n)
    d hd (by
      intro g
      change (⇑(entrywiseAut σ n))^[d] g = g
      rw [entrywiseAut_iterate_eq_pow, hσ, entrywiseAut_one_apply])
  have hτs : IsSmooth τ := hτ.1.1
  let τu := SmoothRep.of (universeLiftRepresentation.{v} τ) ((isSmooth_universeLift_iff τ).mpr hτs)
  have hτu : τu.IsIrreducible := (isIrreducible_universeLift_iff τ).mpr hτ.2.1
  obtain ⟨k₀, ρ₀, hρ₀⟩ := glSupercuspidalEmbedding.{z, v} p E T n hn τu hτu
  have hsτ : T.IsSupercuspidalSupport τu (List.ofFn ρ₀ : Multiset _) :=
    ⟨k₀, ρ₀, rfl, hρ₀.isCuspidalConstituent⟩
  obtain ⟨J, hJc, hvis⟩ := exists_compact_fixed_of_supportTwistSelection T hModule σ hn hθ
    (List.ofFn ρ₀ : Multiset _) hsτ.sum_rank
  refine ⟨J, hJc, ?_⟩
  exact disjoint_twistedOrbitSpan_complement_of_support σ μ τ hθ
    (supportTwistSelection T n (List.ofFn ρ₀ : Multiset _))
    (fun e h => supportTwistSelection_of_equiv T _ e h) J
    (fun W _ _ π _ horb => supportTwistSelection_of_isUnramifiedTwistOf T hn _ τ hτs hsτ _ π horb)
    (fun W _ _ π _ hS => hvis W π hS)
    (fun B _ W _ _ Ξ hΞ hirr A h =>
      properInduced_mem_selection_or_complement T hModule σ hn _ μ B Ξ hΞ hirr A h) hSep

end Padic

end Langlands.BaseChange
