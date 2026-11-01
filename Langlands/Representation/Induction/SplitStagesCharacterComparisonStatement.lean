import Langlands.Representation.Induction.SplitStagesCharacterIntegrand

/-! Natural character-localized compact induction in split stages. -/

noncomputable section

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure QuotientIntegration HarmonicAnalysis

universe uG uL uV uW

/-- The actual character-localized split-stages comparison, with its canonical
inverse-weighted integral and naturality for independent coefficient carriers. -/
def SplitStagesCharacterComparisonStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G],
  ∀ (L : Type uL) [Group L] [TopologicalSpace L] [IsTopologicalGroup L],
  ∀ (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (hr : Continuous r) (hs : Continuous s)
    (P H : Subgroup G) (hker : r.ker ≤ P) (hHP : H ≤ P)
    (hP : IsClosed (P : Set G)) (hH : IsClosed (H : Set G))
    (hsH : ∀ l : P.comap s, s (l : L) ∈ H)
    (θ : SmoothCharacter ℂ r.ker)
    (hθ : SplitKernelLocalization.SectionInvariant r s θ.toMonoidHom),
  ∀ [LocallyCompactSpace (splitStagesRetraction r s hrs P hker).ker]
    [MeasurableSpace (splitStagesRetraction r s hrs P hker).ker]
    [BorelSpace (splitStagesRetraction r s hrs P hker).ker]
    [MeasurableSpace
      ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)]
    [BorelSpace
      ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)]
    [MeasurableSpace (LeftQuotient
      ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))]
    [BorelSpace (LeftQuotient
      ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))],
  ∀ (ν : Measure (LeftQuotient
      ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype)))
    [IsFiniteMeasureOnCompacts ν]
    (μN : Measure (splitStagesRetraction r s hrs P hker).ker)
    (μI : Measure
      ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype))
    [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
    [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI],
  ∀ (_hCompatible : IsCompatible
      ((H.subgroupOf P).comap (splitStagesRetraction r s hrs P hker).ker.subtype) μN μI ν)
    (_hN : IsClosed (r.ker : Set G))
    (_hBasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧ (U : Set G) ⊆ O)
    (_hKernelBasis : ∀ O : Set (splitStagesRetraction r s hrs P hker).ker,
      IsOpen O → (1 : (splitStagesRetraction r s hrs P hker).ker) ∈ O →
        ∃ U : OpenSubgroup (splitStagesRetraction r s hrs P hker).ker,
          IsCompact (U : Set (splitStagesRetraction r s hrs P hker).ker) ∧
            (U : Set (splitStagesRetraction r s hrs P hker).ker) ⊆ O),
  ∀ (V : Type uV) (W : Type uW) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ H V) (hσ : IsSmooth σ)
    (τ : Representation ℂ H W) (hτ : IsSmooth τ),
    let K := P.comap s
    let rP := splitStagesRetraction r s hrs P hker
    let sP := s.subgroupComap P
    let HP := H.subgroupOf P
    let φ := MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP)
    let θP := (SplitStagesCharacter.kernelCharacter r s hrs P hker θ).toMonoidHom
    let hθP := SplitStagesCharacter.sectionInvariant r s hrs P hker θ hθ
    let hsHP := SplitStagesCharacter.section_mem s P H hsH
    let hHPclosed := SplitStagesCharacter.subgroup_closed P H hH
    let χ := Jacquet.complexCharacter (splitKernelHaarRatio rP sP HP hsHP hHPclosed)
    let κσ := twist χ (SplitKernelLocalization.subgroupAction
      rP sP θP hθP HP hsHP (σ.comp φ))
    let κτ := twist χ (SplitKernelLocalization.subgroupAction
      rP sP θP hθP HP hsHP (τ.comp φ))
    ∃ Eσ : Representation.Equiv
        (SplitKernelLocalization.localizedAction r s θ.toMonoidHom hθ (compactInduced H σ))
        (compactInduced K κσ),
    ∃ Eτ : Representation.Equiv
        (SplitKernelLocalization.localizedAction r s θ.toMonoidHom hθ (compactInduced H τ))
        (compactInduced K κτ),
      (∀ (f : CompactFunctions H σ) (l : L),
        eval K κσ (Eσ (Jacquet.Localization.mk (compactInduced H σ)
            r.ker θ.toMonoidHom f)).val l =
          AlgebraicIntegral.integral ν
            (SplitStagesCharacter.integrand r s hrs hr hs P H hker hHP hP hH hsH θ σ hσ f l)) ∧
      (∀ (f : CompactFunctions H τ) (l : L),
        eval K κτ (Eτ (Jacquet.Localization.mk (compactInduced H τ)
            r.ker θ.toMonoidHom f)).val l =
          AlgebraicIntegral.integral ν
            (SplitStagesCharacter.integrand r s hrs hr hs P H hker hHP hP hH hsH θ τ hτ f l)) ∧
      (∀ (T : σ.IntertwiningMap τ)
          (z : Jacquet.Localization.Coinvariants (compactInduced H σ) r.ker θ.toMonoidHom),
        Eτ (SplitKernelLocalization.sectionMap r s θ.toMonoidHom hθ
            (compactInducedMap H T) z) =
          compactInducedMap K
            (twistIntertwining χ (SplitKernelLocalization.subgroupMap
              rP sP θP hθP HP hsHP (restrictAlongMap φ T))) (Eσ z))

end Langlands.Induction
