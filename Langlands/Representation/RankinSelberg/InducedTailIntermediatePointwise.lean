import Langlands.Representation.RankinSelberg.InducedTailIntermediateComparison
import Langlands.Representation.RankinSelberg.InducedTailIntermediateIntegrands
import Langlands.Representation.Whittaker.LowerBlockLocalizationProof
import Langlands.Representation.Whittaker.TwoBlockExtensionStatement

/-! # Conditional localized pointwise intermediate-tail comparison -/

noncomputable section

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear Whittaker HarmonicAnalysis Topology

universe uF uV uW uV₁ uV₂

/-- Conditional use of the exact extension theorem in the actual canonical
induction. The diagonal lower chart and extension matrix are compared by their
explicit rank reindexings, retaining both independent block universes. -/
theorem exists_canonical_diagonal_extension_of_extension
    (hext : TwoBlockWhittakerExtensionStatement.{uF, uV₁, uV₂})
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology;
      UnitaryAdditiveCharacter F.Carrier)
    (a n d c₀ : ℕ) (ha : a + 1 = d + (c₀ + 1))
    {V₁ : Type uV₁} [AddCommGroup V₁] [Module ℂ V₁]
    {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V₂)
    (hπ₁ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType a (standardCharacter ψ a) π₁)
    (hπ₂ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType n (standardCharacter ψ n) π₂) :
    letI := F.canonicalTopologicalData.topology
    let π₁' : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier)
        (ULift.{uV₂} V₁) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₁
    let π₂' : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier)
        (ULift.{uV₁} V₂) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₂
    let ξ := F.canonicalNormalizedProductInduced
      (Shahidi.twoBlocks (a + 1) (n + 1) (Nat.succ_pos a) (Nat.succ_pos n))
      (Shahidi.pairFamily π₁' π₂')
    ∀ W₂ ∈ whittakerSet ψ n π₂,
      ∀ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier),
        ∃ W ∈ whittakerSet ψ (a + 1 + n) ξ,
          ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
            W.val (reindex
              (finCongr (by omega : (n + 1) + d + (c₀ + 1) = (a + 1) + (n + 1)))
              (lowerBlockLocalization (c₀ + 1) g 0 1)) =
              W₂.val g * Φ (lastRow g) *
                (Real.rpow
                  (F.canonicalTopologicalData.normalizedAbs (Matrix.det g.val))
                  (((d + (c₀ + 1) : ℕ) : ℝ) / 2) : ℂ) := by
  let := F.canonicalTopologicalData.topology
  dsimp only
  intro W₂ hW₂ Φ
  obtain ⟨W, hW, hformula⟩ := hext p F ψ a n π₁ π₂ hπ₁ hπ₂ W₂ hW₂ Φ
  refine ⟨W, hW, ?_⟩
  intro g
  rw [lowerBlockLocalization_diagonal_fullRank n d (c₀ + 1) a ha g, hformula g]
  rw [ha]

/-- Given a diagonal extension and a cutoff
for the specified inverse test coefficient, choose actual compact open
localizers and an actual coefficient with the complete weighted pointwise
comparison. The extension, cutoff and full Whittaker-type hypotheses remain
explicit: this is not the closed intermediate-tail span theorem. -/
theorem exists_localized_pointwise_comparison
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (n d c₀ : ℕ) (hd : 0 < d) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ
        (Langlands.GeneralLinear ((n + 1) + d + (c₀ + 1)) F.Carrier) V),
      IsOfWhittakerType (n + 1 + d + c₀)
        (standardCharacter ψ (n + 1 + d + c₀)) π →
      ∀ W ∈ whittakerSet ψ (n + 1 + d + c₀) π,
      ∀ (Wtail : WhittakerFunctions ψ n)
        (E : Type uW) [AddCommGroup E] [Module ℂ E]
        (σ : Representation ℂ
          (Langlands.GeneralLinear (n + d + 1) F.Carrier) E),
        IsSmooth σ →
        ∀ Wtest ∈ inverseWhittakerSet ψ (n + d) σ,
        ∀ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier),
          (∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
            W.val (lowerBlockLocalization (c₀ + 1) g 0 1) =
              Wtail.val g * Φ (lastRow g) *
                (Real.rpow
                  (F.canonicalTopologicalData.normalizedAbs (Matrix.det g.val))
                  (((d + (c₀ + 1) : ℕ) : ℝ) / 2) : ℂ)) →
          (∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
            Wtest.val (appendIdentity n d g) * Φ (lastRow g) =
              Wtest.val (appendIdentity n d g)) →
          ∃ Ω₁ : AddSubgroup (Matrix (Fin d) (Fin (n + 1)) F.Carrier),
            ∃ Ω₂ : Subgroup (lowerTriangularSubgroup d F.Carrier),
              IsCompact (Ω₁ : Set (Matrix (Fin d) (Fin (n + 1)) F.Carrier)) ∧
              IsOpen (Ω₁ : Set (Matrix (Fin d) (Fin (n + 1)) F.Carrier)) ∧
              IsCompact (Ω₂ : Set (lowerTriangularSubgroup d F.Carrier)) ∧
              IsOpen (Ω₂ : Set (lowerTriangularSubgroup d F.Carrier)) ∧
              ∃ W₀ ∈ whittakerSet ψ (n + 1 + d + c₀) π,
                ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier)
                  (x : Matrix (Fin d) (Fin (n + 1)) F.Carrier)
                  (h : lowerTriangularSubgroup d F.Carrier) (s : ℂ),
                  W₀.val (lowerBlockLocalization (c₀ + 1) g x h) *
                    Wtest.val (reindex (finCongr (by omega)) (lowerBlockPair g x h)) *
                    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
                      (reindex (finCongr (by omega : (n + 1) + d = n + d + 1))
                        (lowerBlockPair g x h)) (s - ((c₀ + 1 : ℕ) : ℂ) / 2) *
                    ((F.canonicalTopologicalData.normalizedAbs (Matrix.det g.val) ^
                      (-(d : ℤ)) : ℝ) : ℂ) =
                    (Wtail.val g * Wtest.val (appendIdentity n d g) *
                      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
                        g (s - (d : ℂ) / 2)) *
                    ((Ω₁ : Set (Matrix (Fin d) (Fin (n + 1)) F.Carrier)).indicator
                        (fun _ => (1 : ℂ)) x *
                      (Ω₂ : Set (lowerTriangularSubgroup d F.Carrier)).indicator
                        (fun _ => (1 : ℂ)) h) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  intro ψ V _ _ π hπ W hW Wtail E _ _ σ hσ Wtest hWtest Φ hext hcut
  obtain ⟨Ux, Uh, hUx, hUh, htest⟩ :=
    exists_lowerBlockPair_test_neighborhoods
      (by omega : (n + 1) + d = (n + d) + 1) ψ σ hσ Wtest hWtest
  let D : Set (lowerTriangularSubgroup d F.Carrier) :=
    {h | F.canonicalTopologicalData.normalizedAbs (Matrix.det h.val.val) = 1}
  have hD : D ∈ 𝓝 (1 : lowerTriangularSubgroup d F.Carrier) :=
    lowerTriangular_det_one_nhds F.canonicalTopologicalData d
  obtain ⟨Ω₁, Ω₂, hΩ₁c, hΩ₁o, hΩ₁sub, hΩ₂c, hΩ₂o, hΩ₂sub, W₀, hW₀, hloc⟩ :=
    lowerBlockWhittakerLocalization p F ψ (n + 1) d c₀ (Nat.succ_pos n) hd V π hπ W hW
      Ux (Uh ∩ D) hUx (Filter.inter_mem hUh hD)
  refine ⟨Ω₁, Ω₂, hΩ₁c, hΩ₁o, hΩ₂c, hΩ₂o, W₀, hW₀, ?_⟩
  intro g x h s
  by_cases hp : x ∈ Ω₁ ∧ h ∈ Ω₂
  · have htest' :
        Wtest.val (reindex (finCongr (by omega)) (lowerBlockPair g x h)) =
          Wtest.val (appendIdentity n d g) := by
      rw [htest g x h (hΩ₁sub hp.1) (hΩ₂sub hp.2).1,
        lowerBlockPair_eq_appendIdentity]
    rw [(hloc g x h).1 hp, htest', determinantWeight_reindex,
      determinantWeight_lowerBlockPair
        (normalizedAbsoluteValue F.canonicalTopologicalData) g x h (hΩ₂sub hp.2).2,
      hext g]
    simp only [Set.indicator_of_mem hp.1, Set.indicator_of_mem hp.2, mul_one]
    calc
      _ = (Wtail.val g * (Wtest.val (appendIdentity n d g) * Φ (lastRow g))) *
          ((Real.rpow
            (F.canonicalTopologicalData.normalizedAbs (Matrix.det g.val))
            (((d + (c₀ + 1) : ℕ) : ℝ) / 2) : ℂ) *
            determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
              g (s - ((c₀ + 1 : ℕ) : ℂ) / 2) *
            ((F.canonicalTopologicalData.normalizedAbs (Matrix.det g.val) ^
              (-(d : ℤ)) : ℝ) : ℂ)) := by ring
      _ = _ := by
        rw [hcut g]
        exact congrArg (fun z : ℂ => Wtail.val g * Wtest.val (appendIdentity n d g) * z)
          (extensionWeight_density_cancel
            (normalizedAbsoluteValue F.canonicalTopologicalData) g d (c₀ + 1) s)
  · rw [(hloc g x h).2 hp]
    rcases not_and_or.mp hp with hx | hh
    · simp [Set.indicator_of_notMem hx]
    · simp [Set.indicator_of_notMem hh]

/-- A diagonal extension for each Schwartz function, together with full
Whittaker type, yields an equality of the actual full and reversed-character
tail integrands. The cutoff is supplied by the published cutoff theorem.
The density remains an explicit pointwise multiplier. -/
theorem exists_localized_integrand_comparison
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (n d c₀ k : ℕ) (hd : d = k + 1) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.valuativeExtension
    letI := F.canonicalTopologicalData.moduleTopology
    letI := F.canonicalTopologicalData.localField
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ
        (Langlands.GeneralLinear ((n + 1) + d + (c₀ + 1)) F.Carrier) V),
      IsOfWhittakerType (n + 1 + d + c₀)
        (standardCharacter ψ (n + 1 + d + c₀)) π →
      ∀ (Wtail : WhittakerFunctions ψ n)
        (E : Type uW) [AddCommGroup E] [Module ℂ E]
        (σ : Representation ℂ
          (Langlands.GeneralLinear (n + d + 1) F.Carrier) E),
        IsSmooth σ →
        ∀ Wtest ∈ inverseWhittakerSet ψ (n + d) σ,
          (∀ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier),
            ∃ W ∈ whittakerSet ψ (n + 1 + d + c₀) π,
              ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
                W.val (lowerBlockLocalization (c₀ + 1) g 0 1) =
                  Wtail.val g * Φ (lastRow g) *
                    (Real.rpow
                      (F.canonicalTopologicalData.normalizedAbs (Matrix.det g.val))
                      (((d + (c₀ + 1) : ℕ) : ℝ) / 2) : ℂ)) →
          ∃ Ω₁ : AddSubgroup (Matrix (Fin d) (Fin (n + 1)) F.Carrier),
            ∃ Ω₂ : Subgroup (lowerTriangularSubgroup d F.Carrier),
              IsCompact (Ω₁ : Set (Matrix (Fin d) (Fin (n + 1)) F.Carrier)) ∧
              IsOpen (Ω₁ : Set (Matrix (Fin d) (Fin (n + 1)) F.Carrier)) ∧
              IsCompact (Ω₂ : Set (lowerTriangularSubgroup d F.Carrier)) ∧
              IsOpen (Ω₂ : Set (lowerTriangularSubgroup d F.Carrier)) ∧
              ∃ W₀ ∈ whittakerSet ψ (n + 1 + d + c₀) π,
                ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier)
                  (x : Matrix (Fin d) (Fin (n + 1)) F.Carrier)
                  (h : lowerTriangularSubgroup d F.Carrier) (s : ℂ)
                  (rFull : Matrix (Fin 0) (Fin (n + d + 1)) F.Carrier)
                  (rTail : Matrix (Fin 0) (Fin (n + 1)) F.Carrier),
                  unequalRankIntegrand ψ
                    (normalizedAbsoluteValue F.canonicalTopologicalData) 0 c₀
                    (whittakerRankCast ψ (by omega) W₀) Wtest s rFull
                    (Quotient.mk _
                      (reindex (finCongr (by omega : (n + 1) + d = n + d + 1))
                        (lowerBlockPair g x h))) *
                    ((F.canonicalTopologicalData.normalizedAbs (Matrix.det g.val) ^
                      (-(d : ℤ)) : ℝ) : ℂ) =
                  unequalRankIntegrand (ψ.scale (-1))
                    (normalizedAbsoluteValue F.canonicalTopologicalData) 0 k
                    (inverseAsScaledStandard ψ
                      (inverseWhittakerRankCast ψ
                        (by omega : n + d = n + (0 + k + 1)) Wtest))
                    (standardAsScaledInverse ψ Wtail) s rTail (Quotient.mk _ g) *
                    ((Ω₁ : Set (Matrix (Fin d) (Fin (n + 1)) F.Carrier)).indicator
                        (fun _ => (1 : ℂ)) x *
                      (Ω₂ : Set (lowerTriangularSubgroup d F.Carrier)).indicator
                        (fun _ => (1 : ℂ)) h) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.valuativeExtension
  let := F.canonicalTopologicalData.moduleTopology
  let := F.canonicalTopologicalData.localField
  intro ψ V _ _ π hπ Wtail E _ _ σ hσ Wtest hWtest hextall
  have hRank : n + d = n + (0 + k + 1) := by omega
  let σ' : Representation ℂ
      (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) E :=
    hRank ▸ σ
  let Wtest' := inverseWhittakerRankCast ψ hRank Wtest
  have hσ' : IsSmooth σ' := representationRankCast_isSmooth hRank σ hσ
  have hWtest' : Wtest' ∈ inverseWhittakerSet ψ (n + (0 + k + 1)) σ' :=
    inverseWhittakerRankCast_mem ψ hRank σ hWtest
  obtain ⟨Φ, _, hcut'⟩ :=
    inverse_zeroRow_cutoff F F.canonicalTopologicalData n k ψ E σ' hσ' Wtest' hWtest'
  have hcut : ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      Wtest.val (appendIdentity n d g) * Φ (lastRow g) =
        Wtest.val (appendIdentity n d g) := by
    intro g
    simpa only [Wtest', inverseWhittakerRankCast_appendIdentity] using hcut' g
  obtain ⟨W, hW, hext⟩ := hextall Φ
  obtain ⟨Ω₁, Ω₂, hΩ₁c, hΩ₁o, hΩ₂c, hΩ₂o, W₀, hW₀, hcomp⟩ :=
    exists_localized_pointwise_comparison p F n d c₀ (by omega)
      ψ V π hπ W hW Wtail E σ hσ Wtest hWtest Φ hext hcut
  refine ⟨Ω₁, Ω₂, hΩ₁c, hΩ₁o, hΩ₂c, hΩ₂o, W₀, hW₀, ?_⟩
  intro g x h s rFull rTail
  rw [full_unequalRankIntegrand_lowerBlockPair,
    reversedTail_unequalRankIntegrand_of_gap_eq ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) n d k hd]
  exact hcomp g x h s

end Langlands.RankinSelberg.InducedTailIntermediate
