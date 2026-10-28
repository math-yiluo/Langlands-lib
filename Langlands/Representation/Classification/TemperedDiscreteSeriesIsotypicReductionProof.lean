import Langlands.Representation.Classification.TemperedDiscreteSeriesIsotypicReductionStatement
import Langlands.Representation.Classification.TemperedCoefficientPairing
import Langlands.Representation.Smooth.IsotypicProjector
import Langlands.Group.GL.LeviCentralQuotientMeasure
import Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-!
# Discrete-series isotypic projectors from exponents below two

For a tempered `ρ` and an irreducible square-integrable `σ` with one central
character, an `L^r` bound with `r < 2` on the `σ`-coefficients makes every
coefficient product integrable over the central quotient by Hölder's
inequality. The integrated products give intertwiners in both directions; a
dual basis of `Hom(σ, ρ)` then gives the isotypic projector, and a quotient of
its kernel onto `σ` would produce a nonzero intertwiner `σ → ρ` killed by the
projector.
-/

noncomputable section

namespace Langlands

open MeasureTheory Representation

universe uG uF uV uW

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- An `L^r` bound with `1 < r < 2` on the `σ`-coefficients and temperedness of
`ρ` make every smooth coefficient product integrable. -/
theorem pairingIntegrable_of_lt_two
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    (cρ : UnitaryCentralCharacter ρ) (cσ : UnitaryCentralCharacter σ)
    (hχ : cρ.character = cσ.character)
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
    (hρ : IsTemperedModCenter ρ μ) (hσ : IsSmooth σ)
    (hlt : ∀ (ℓ : SmoothDual σ) (w : W), ∃ r : ℝ, 1 < r ∧ r < 2 ∧
      MemLp (cσ.coefficientNorm ℓ w) (ENNReal.ofReal r) μ) :
    cρ.PairingIntegrable cσ hχ μ := by
  intro ℓ w η v
  obtain ⟨r, hr1, hr2, hr⟩ := hlt ℓ w
  obtain ⟨c, hc⟩ := hρ.2
  have hconj : 2 < r.conjExponent := by
    rw [Real.conjExponent, lt_div_iff₀ (by linarith)]
    linarith
  have hρr : MemLp (cρ.coefficientNorm η v) (ENNReal.ofReal r.conjExponent) μ := by
    have h := hc η v (r.conjExponent - 2) (by linarith)
    have he : (2 : ℝ) + (r.conjExponent - 2) = r.conjExponent := by ring
    rw [he] at h
    rwa [cρ.coefficientNorm_eq c]
  exact cρ.integrable_pairingKernel cσ hχ ℓ w η v μ (hσ w) (hρ.1.1 v) hr1 hr hρr

/-- Every nonzero intertwiner `f : σ → ρ` is detected by the functional
`b(u, -)` through an intertwiner `ρ → σ` built from the coefficient pairing. -/
theorem exists_intertwiningMap_rightFunctional_ne_zero
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    {μ : Measure (G ⧸ Subgroup.center G)} [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure]
    {cρ : UnitaryCentralCharacter ρ} {cσ : UnitaryCentralCharacter σ}
    {hχ : cρ.character = cσ.character}
    (hρ : IsSmooth ρ) (hσ : IsAdmissible σ) (hirr : σ.IsIrreducible)
    (hint : cρ.PairingIntegrable cσ hχ μ) (b : InvariantPositiveForm σ) {u : W}
    (hu : u ≠ 0) (hL2 : MemLp (cσ.coefficientNorm (b.rightFunctional u) u) 2 μ)
    (f : σ.IntertwiningMap ρ) (hf : f ≠ 0) :
    ∃ r : ρ.IntertwiningMap σ, b.rightFunctional u (r (f u)) ≠ 0 := by
  have hfi : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  obtain ⟨ξ, hξ⟩ := contragredientMap_surjective_of_injective_of_compact_cofinal hcof
    hσ.1 hρ f hfi (b.toSmoothDual hσ.1 u)
  obtain ⟨S, hS⟩ :=
    UnitaryCentralCharacter.exists_intertwiningMap_of_coefficientPairing_right hcof hρ hσ
      hint u ξ
  refine ⟨S, ?_⟩
  have hx : ∀ g : G, ξ.1 (ρ g (f u)) = b.inner u (σ g u) := by
    intro g
    have h := congrArg (fun φ : SmoothDual σ => φ.1 (σ g u)) hξ
    change ξ.1 (f (σ g u)) = b.inner u (σ g u) at h
    rwa [f.isIntertwining] at h
  have h := hS (b.toSmoothDual hσ.1 u) (f u)
  change b.rightFunctional u (S (f u)) = _ at h
  rw [h]
  exact UnitaryCentralCharacter.coefficientPairing_ne_zero hσ.1 hirr b hu hL2 ξ (f u) hx

/-- Generic form of the isotypic projector theorem: compact open subgroups are
cofinal, the Haar measure on the central quotient is unimodular, and the
`σ`-coefficients lie in `L^r` for some `1 < r < 2`. -/
theorem temperedDiscreteSeriesIsotypic_of_lt_two
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    [μ.IsInvInvariant]
    (cρ : UnitaryCentralCharacter ρ) (cσ : UnitaryCentralCharacter σ)
    (hρ : IsTemperedModCenter ρ μ) (hirr : σ.IsIrreducible)
    (hσ : IsSquareIntegrableModCenter σ μ) (hχ : cρ.character = cσ.character)
    (hlt : ∀ (ℓ : SmoothDual σ) (w : W), ∃ r : ℝ, 1 < r ∧ r < 2 ∧
      MemLp (cσ.coefficientNorm ℓ w) (ENNReal.ofReal r) μ) :
    ∃ P : ρ.IntertwiningMap ρ, P.comp P = P ∧
      P.range = (⨆ f : σ.IntertwiningMap ρ, f.range) ∧
      ∀ K : Subrepresentation P.ker.toRepresentation,
        ¬ ∃ q : K.toRepresentation.IntertwiningMap σ, Function.Surjective q := by
  have hρs : IsSmooth ρ := hρ.1.1
  have hσs : IsSmooth σ := hσ.1.1
  have hint := pairingIntegrable_of_lt_two cρ cσ hχ μ hρ hσs hlt
  have : Module.Finite ℂ (σ.IntertwiningMap ρ) :=
    finite_intertwiningMap_of_finiteType σ ρ hσs
      (moduleFinite_asModule_of_isIrreducible σ hirr) hρ.1
  obtain ⟨c, hc⟩ := hσ.2
  have hL2 : ∀ (ℓ : SmoothDual σ) (w : W), MemLp (cσ.coefficientNorm ℓ w) 2 μ := by
    intro ℓ w
    rw [cσ.coefficientNorm_eq c]
    exact hc ℓ w
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_nonzero_smoothDual_of_irreducible_compact_cofinal hcof σ hσs hirr
  let b := cσ.coefficientProductForm hσs hirr ℓ₁.1 hℓ₁ μ (hL2 ℓ₁)
  have : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) σ.asModule
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  have hbu : b.rightFunctional u u ≠ 0 := fun h => hu (b.definite u h)
  have hLu : MemLp (cσ.coefficientNorm (b.rightFunctional u) u) 2 μ :=
    hL2 (b.toSmoothDual hσs u) u
  obtain ⟨P, hfix, hmem⟩ := exists_isotypicProjector_of_nondegenerate hσ.1 hirr
    (b.rightFunctional u) hbu
    (fun f hf => exists_intertwiningMap_rightFunctional_ne_zero hcof hρs hσ.1 hirr hint b hu
      hLu f hf)
  obtain ⟨hPP, hPrange⟩ := isotypicProjector_of_fixes P hfix hmem
  refine ⟨P, hPP, hPrange, ?_⟩
  rintro K ⟨q, hq⟩
  let ι : K.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := P.ker.toSubmodule.subtype ∘ₗ K.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hPι : ∀ k, P (ι k) = 0 := fun k => (k : P.ker.toSubmodule).2
  have hKs : IsSmooth K.toRepresentation := isSmooth_of_injective ι hι hρs
  obtain ⟨k₀, hk₀⟩ := hq u
  obtain ⟨ξ, hξ⟩ := contragredientMap_surjective_of_injective_of_compact_cofinal hcof hKs hρs
    ι hι (contragredientMap q (b.toSmoothDual hσs u))
  obtain ⟨R, hR⟩ :=
    UnitaryCentralCharacter.exists_intertwiningMap_of_coefficientPairing_left hcof hσs hρ.1
      hint (b.toSmoothDual hσs u) (ι k₀)
  have hPR : ∀ w, P (R w) = 0 := by
    intro w
    by_contra hne
    obtain ⟨η, hη⟩ := exists_smoothDual_apply_ne_zero_of_compact_cofinal hcof ρ hρs hne
    apply hη
    have h := hR (contragredientMap P η) w
    change η.1 (P (R w)) = _ at h
    rw [h]
    have hk : ∀ x, cρ.pairingKernel cσ hχ (b.toSmoothDual hσs u : Module.Dual ℂ W) w
        (contragredientMap P η : Module.Dual ℂ V) (ι k₀) x = 0 := by
      intro x
      induction x using Quotient.inductionOn with
      | h g =>
        change _ * η.1 (P (ρ g (ι k₀))) = 0
        rw [P.isIntertwining, hPι, map_zero, map_zero, mul_zero]
    unfold UnitaryCentralCharacter.coefficientPairing
    simp only [hk, integral_zero]
  have hR0 : ∀ w, R w = 0 := by
    intro w
    have h := congrArg (fun φ : σ.IntertwiningMap ρ => φ w) (hfix R)
    simp only [IntertwiningMap.comp_apply] at h
    rw [← h]
    exact hPR w
  have hx : ∀ g : G, ξ.1 (ρ g (ι k₀)) = b.inner u (σ g u) := by
    intro g
    have h := congrArg
      (fun φ : SmoothDual K.toRepresentation => φ.1 (K.toRepresentation g k₀)) hξ
    change ξ.1 (ι (K.toRepresentation g k₀)) = b.inner u (q (K.toRepresentation g k₀)) at h
    rwa [ι.isIntertwining, q.isIntertwining, hk₀] at h
  apply UnitaryCentralCharacter.coefficientPairing_ne_zero (cρ := cρ) (hχ := hχ) hσs hirr b hu
    hLu ξ (ι k₀) hx
  rw [← hR ξ u, hR0, map_zero]

end Generic

/-- Integrability of discrete-series coefficients below exponent two implies the
tempered discrete-series isotypic projector statement. -/
theorem glTemperedDiscreteSeriesIsotypicReduction :
    GLTemperedDiscreteSeriesIsotypicReductionStatement.{uF, uV, uW} := by
  intro hP1 p _ F T
  let := T.topology
  intro n hn B
  let := T.leviTopology B
  have := T.leviTopologicalGroup B
  intro M Q _ _ μ _ V _ _ W _ _ ρ σ cρ cσ hρ hirr hσ hχ
  obtain ⟨hR, hI⟩ := T.leviCentralQuotientHaar_unimodular B μ
  exact temperedDiscreteSeriesIsotypic_of_lt_two
    (UnitaryDualJacquetSupport.levi_compactOpen_cofinal T B) μ cρ cσ hρ hirr hσ hχ
    (hP1 p F T n hn B μ W σ hirr hσ cσ)

end Langlands
