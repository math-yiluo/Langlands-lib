import Langlands.BaseChange.TwistedPaleyWienerStatement
import Langlands.BaseChange.TwistedPseudoCoefficientSpectralConstruction
import Langlands.BaseChange.TwistedPseudoCoefficientSmallRank
import Langlands.BaseChange.SigmaLiftTransport
import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Group.GL.LocalFieldTopology

/-!
# Twisted pseudo-coefficients killing properly induced twisted characters

The spectral construction of Henniart–Lemaire (2011), II.5.13, produces a linear functional on
the distributions on `GL_n(E)` that is `1` at the twisted character of a σ-discrete series
`(τ, A)`, vanishes at the twisted characters of the other tempered representations with the
same central character, and vanishes on the span of the twisted characters of the
representations properly induced from σ-stable irreducible admissible representations of
standard Levi subgroups. Realizing that functional by the twisted trace Paley–Wiener theorem
gives a twisted pseudo-coefficient of `(τ, A)` whose twisted traces vanish on the irreducible
properly induced representations (Henniart–Lemaire 2011, II.5.13, Remarque, and II.5.14,
proof of Proposition 2 (1)). This module proves that consequence of the twisted trace
Paley–Wiener theorem and the spectral splitting of the twisted-character space.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear TopologicalSpace

/-- The functional of Henniart–Lemaire II.5.13 with its vanishing on proper inductions: in
ranks at least two, a compactly dominated functional, regular on all induced families, with
value `1` at `Θ^A_τ`, vanishing at the twisted characters of the tempered irreducible
representations with central character `χ` not isomorphic to `τ`, and vanishing on the span
`sigmaProperInducedSpan` of the twisted characters of proper inductions of irreducible
admissible σ-stable representations of standard Levi subgroups. -/
def TwistedProperInducedFunctionalExistenceStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) → 2 ≤ n →
    haveI : Module.Finite F E := hE.1
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ),
      IsSigmaDiscreteSeries σ n τ →
      ∀ χ : Subgroup.center (GeneralLinear n E) →* ℂˣ, HasCentralCharacterRep τ χ →
      ∀ (A : SigmaIntertwiner σ n τ) (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure],
        ∃ Φ : Module.Dual ℂ (Distribution (GeneralLinear n E)),
          IsCompactlyDominatedFunctional.{v, uW} (entrywiseAut σ n) μ Φ ∧
          IsSigmaInducedRegularFunctional.{u, v, uW} σ μ Φ ∧
          Φ (twistedDistribution μ τ hτ A.toLinearMap) = 1 ∧
          (∀ (W' : Type uW) [AddCommGroup W'] [Module ℂ W']
            (τ' : Representation ℂ (GeneralLinear n E) W') (hτ' : IsAdmissible τ'),
            τ'.IsIrreducible → IsTemperedRep τ' → HasCentralCharacterRep τ' χ →
            IsEmpty (τ'.Equiv τ) → ∀ A' : SigmaIntertwiner σ n τ',
              Φ (twistedDistribution μ τ' hτ' A'.toLinearMap) = 0) ∧
          ∀ d ∈ sigmaProperInducedSpan.{u, v, uW} σ μ, Φ d = 0

/-- The spectral splitting gives the functional of Henniart–Lemaire II.5.13 together with its
vanishing on the properly induced span: interpolate on the unramified twist orbit of `τ`,
extend by zero on the complement span (which contains `sigmaProperInducedSpan`), and use the
two twist-stable spaces to prove regularity. -/
theorem twistedProperInducedFunctionalExistence_of_spectrumSplitting.{u, v, uW}
    (hsplit : TwistedPseudoCoefficientSpectrumSplittingStatement.{u, v, uW}) :
    TwistedProperInducedFunctionalExistenceStatement.{u, v, uW} := by
  classical
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE hn
  let : Module.Finite F E := hE.1
  let : MeasurableSpace (GeneralLinear n E) := borel _
  let : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let := generalLinear_t2Space_of_finite F E n
  let := generalLinear_locallyCompactSpace_of_finite F E n
  let := generalLinear_totallyDisconnectedSpace_of_finite F E n
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField_of_isModuleTopology F E
  let T := LocalFieldData.ofInstances E
  let θ := entrywiseAut σ n
  have hθ := exists_compact_openSubgroup_symm_mem θ (continuous_entrywiseAut σ n) l hE.pos (by
    intro g
    change (⇑(entrywiseAut σ n))^[l] g = g
    rw [entrywiseAut_iterate_eq_pow, hE.pow_eq_one, entrywiseAut_one_apply])
  let i : Fin n := ⟨0, by omega⟩
  intro W _ _ τ hτ hdisc χ hχ A μ _
  obtain ⟨f₀, hf₁, hf₀⟩ := exists_twistOrbit_test_values μ θ hθ
    (finite_unramifiedCharacter_trivialCenter E i) τ hτ hdisc.2.1 χ hχ A
  obtain ⟨J, hJ, hDisjoint, hspan⟩ := hsplit F E σ l n hE hn W τ hdisc μ
  let L := twistedOrbitSpan μ θ τ
  let N := twistedPseudoCoefficientComplementSpan σ μ τ J
  let fL : Module.Dual ℂ L :=
    { toFun := fun d => d.val f₀
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨Φ, hΦ, hzero⟩ := exists_dual_agreeOn_of_disjoint L N hDisjoint fL
  have hagree (d : Distribution (GeneralLinear n E)) (hd : d ∈ L) : Φ d = d f₀ := hΦ ⟨d, hd⟩
  have hother (d : Distribution (GeneralLinear n E))
      (hd : d ∈ twistedOtherEssentiallyTemperedSpan μ θ τ) : Φ d = 0 :=
    hzero d ((le_sup_left.trans le_sup_left : twistedOtherEssentiallyTemperedSpan μ θ τ ≤ N) hd)
  have hproper (d : Distribution (GeneralLinear n E))
      (hd : d ∈ sigmaProperInducedSpan.{u, v, uW} σ μ) : Φ d = 0 :=
    hzero d ((le_sup_right.trans le_sup_left : sigmaProperInducedSpan.{u, v, uW} σ μ ≤ N) hd)
  have hLmap (ψ : GeneralLinear n E →* ℂˣ) (hψ : IsUnramifiedCharacter ψ)
      (hinv : ∀ g, ψ (θ g) = ψ g) :
      L.map (characterTwistDistribution ψ hψ.isOpen_ker) ≤ L :=
    characterTwistDistribution_map_twistedOrbitSpan_le μ θ ψ hψ hinv τ
  have hNmap (ψ : GeneralLinear n E →* ℂˣ) (hψ : IsUnramifiedCharacter ψ)
      (hinv : ∀ g, ψ (θ g) = ψ g) :
      N.map (characterTwistDistribution ψ hψ.isOpen_ker) ≤ N := by
    unfold N twistedPseudoCoefficientComplementSpan
    rw [Submodule.map_sup, Submodule.map_sup]
    exact sup_le_sup (sup_le_sup
      (characterTwistDistribution_map_twistedOtherEssentiallyTemperedSpan_le μ θ ψ hψ hinv τ)
      (characterTwistDistribution_map_sigmaProperInducedSpan_le σ μ i ψ hψ hinv))
      (characterTwistDistribution_map_twistedInvisibleSpan_le μ θ ψ hψ hinv J hJ)
  refine ⟨Φ, ⟨J, hJ, ?_⟩, ?_, ?_, ?_, hproper⟩
  · intro V _ _ π hπ hirr hfix Bπ
    apply hzero
    apply (le_sup_right : twistedInvisibleSpan.{v, uW} μ θ J ≤ N)
    exact twistedDistribution_mem_twistedSpectrumSpan μ θ _ hπ hirr hfix Bπ
  · intro B X _ _ Ξ hΞ hΞirr BΞ
    by_cases hB : 2 ≤ B.length
    · refine ⟨∅, 0, fun ψ hψ hψσ hI => ?_⟩
      let : IsTopologicalGroup (B.Levi E) := T.leviTopologicalGroup B
      let : T2Space (B.Levi E) := T.leviT2Space B
      let : LocallyCompactSpace (B.Levi E) := T.leviLocallyCompactSpace B
      have : ∀ j : Fin B.length, TotallyDisconnectedSpace (GeneralLinear (B.size j) E) :=
        fun j => generalLinear_totallyDisconnectedSpace_of_finite F E (B.size j)
      have : TotallyDisconnectedSpace (B.Levi E) := inferInstance
      rw [Finset.sum_empty]
      exact hproper _ (twistedDistribution_mem_sigmaProperInducedSpan σ μ B hB (twist ψ Ξ)
        ((isAdmissible_twist_iff ψ Ξ hψ.isOpen_ker).mpr hΞ) ((isIrreducible_twist_iff ψ Ξ).mpr hΞirr)
        (twistTwistedIntertwiner (leviAut σ B) ψ hψσ BΞ) hI)
    · have hBne : B.length ≠ 0 := by
        intro h
        let : IsEmpty (Fin B.length) := ⟨fun j => (Nat.not_lt_zero j.val) (h ▸ j.isLt)⟩
        have hh := B.sum_eq
        rw [Finset.univ_eq_empty, Finset.sum_empty] at hh
        omega
      exact exists_oneBlock_regular_of_spectrum_split σ B (by omega) μ L N Φ f₀
        hLmap hNmap hagree hzero hspan Ξ hΞ hΞirr BΞ
  · exact (hagree _ (twistedDistribution_mem_twistedSpectrumSpan μ θ _ hτ hdisc.2.1
      (IsUnramifiedTwistOf.refl θ τ) A)).trans hf₁
  · intro V _ _ π hπ hπirr hπtemp hχπ hne Bπ
    by_cases hOrb : IsUnramifiedTwistOf θ τ π
    · have hmem : twistedDistribution μ π hπ Bπ.toLinearMap ∈ L :=
        twistedDistribution_mem_twistedSpectrumSpan μ θ _ hπ hπirr hOrb Bπ
      exact (hagree _ hmem).trans (hf₀ V π hπ hχπ hne hOrb Bπ)
    · apply hother
      apply twistedDistribution_mem_twistedSpectrumSpan μ θ _ hπ hπirr _ Bπ
      refine ⟨hOrb, 1, fun _ _ _ _ => rfl, fun _ => rfl, ?_⟩
      simpa only [twist_one] using hπtemp

/-- Existence of twisted pseudo-coefficients killing properly induced twisted characters
(Henniart–Lemaire II.5.13–II.5.14, clauses (a) and (b) of
`TwistedCuspidalPseudoCoefficientExistenceStatement`). For `0 < n`, a σ-discrete series `τ` of
`GL_n(E)` on a carrier in `Type uW` with central character `χ`, `A : τ ≅ τ^σ` and a Haar
measure `μ`, there is `φ ∈ C^∞_c(GL_n(E))` that is a twisted pseudo-coefficient of `(τ, A)`
and whose twisted traces vanish on every irreducible admissible representation
unnormalizedly induced from an irreducible admissible σ-stable representation (carrier in
`Type uW`) of a proper standard Levi subgroup, for every σ-intertwiner. -/
def TwistedProperInducedPseudoCoefficientExistenceStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l : ℕ) (hE : IsCyclicAlgebra σ l) (n : ℕ),
    0 < n →
    haveI : Module.Finite F E := hE.1
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GeneralLinear n E) W)
      (hτ : IsAdmissible τ), IsSigmaDiscreteSeries σ n τ →
      ∀ χ : Subgroup.center (GeneralLinear n E) →* ℂˣ, HasCentralCharacterRep τ χ →
      ∀ (A : SigmaIntertwiner σ n τ) (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure],
      ∃ φ : SchwartzBruhat (GeneralLinear n E),
        IsTwistedPseudoCoefficient μ (entrywiseAut σ n) χ τ hτ A φ ∧
        ∀ B : BlockShape n, 2 ≤ B.length →
          ∀ (X : Type uW) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (B.Levi E) X),
            IsAdmissible Ξ → Ξ.IsIrreducible → IsLeviSigmaStable σ B Ξ →
            (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))).IsIrreducible →
            ∀ (h : IsAdmissible
                (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))))
              (A' : SigmaIntertwiner σ n
                (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E)))),
              twistedDistribution μ
                (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))) h
                A'.toLinearMap φ = 0

/-- The twisted trace Paley–Wiener theorem and the spectral splitting give twisted
pseudo-coefficients killing properly induced twisted characters. In ranks zero and one the
group is commutative, a normalized indicator gives the pseudo-coefficient, and there is no
proper standard Levi subgroup. In ranks at least two the functional of
`twistedProperInducedFunctionalExistence_of_spectrumSplitting` is realized by trace
Paley–Wiener; a properly induced irreducible representation is replaced by an equivalent
realization on a carrier in `Type uW` (the group is second countable) before the realization
and the vanishing on `sigmaProperInducedSpan` are applied. -/
theorem twistedProperInducedPseudoCoefficientExistence_of_spectrumSplitting.{u, v, uW}
    (hPW : TwistedTracePaleyWienerStatement.{u, v, uW})
    (hsplit : TwistedPseudoCoefficientSpectrumSplittingStatement.{u, v, uW}) :
    TwistedProperInducedPseudoCoefficientExistenceStatement.{u, v, uW} := by
  classical
  intro F _ _ _ _ _ E _ _ _ _ _ σ l hE n hn
  let : Module.Finite F E := hE.1
  let : MeasurableSpace (GeneralLinear n E) := borel _
  let : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let := generalLinear_t2Space_of_finite F E n
  let := generalLinear_locallyCompactSpace_of_finite F E n
  let := generalLinear_totallyDisconnectedSpace_of_finite F E n
  intro W _ _ τ hτ hdisc χ hχ A μ _
  by_cases hn1 : n ≤ 1
  · obtain ⟨φ, hφ⟩ := exists_isTwistedPseudoCoefficient_of_center_eq_top μ
      (generalLinear_mem_center_of_rank_le_one hn1) (entrywiseAut σ n) τ hτ hdisc.2.1 χ hχ A
    refine ⟨φ, hφ, fun B hB => ?_⟩
    have := B.length_le
    omega
  have hn2 : 2 ≤ n := by omega
  obtain ⟨Φ, hc, hr, h1, h0, hproper⟩ :=
    twistedProperInducedFunctionalExistence_of_spectrumSplitting hsplit
      F E σ l n hE hn2 W τ hτ hdisc χ hχ A μ
  obtain ⟨φ, hφ⟩ := hPW F E σ l n hE μ Φ hc hr
  refine ⟨φ, ⟨hχ, (hφ W τ hτ hdisc.2.1 A).trans h1, ?_⟩, ?_⟩
  · intro W' _ _ τ' hτ' hirr' htemp' hχ' hne A'
    exact (hφ W' τ' hτ' hirr' A').trans (h0 W' τ' hτ' hirr' htemp' hχ' hne A')
  · intro B hB X _ _ Ξ hΞ hΞirr hΞσ hIirr hI A'
    obtain ⟨BΞ⟩ := hΞσ
    have := LocalFieldTopology.secondCountableTopology F
    have := generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := E) n
    obtain ⟨R, hRirr, ⟨e⟩⟩ := exists_irreducible_smoothRep_equiv_of_separable.{v, _, uW}
      (SmoothRep.of _ hI.1) hIirr
    let ρ := R.representation
    have hρ : IsAdmissible ρ := isAdmissible_of_equiv e hI
    have htrace := twistedDistribution_eq_of_equivalent μ hI hρ e A'.toLinearMap
    rw [← htrace, ← SigmaIntertwiner.transport_toLinearMap A' e, hφ _ ρ hρ hRirr]
    exact hproper _ (twistedDistribution_mem_sigmaProperInducedSpan_of_equiv σ μ B hB Ξ hΞ hΞirr
      BΞ hρ hRirr (A'.transport e) e)

end Langlands.BaseChange
