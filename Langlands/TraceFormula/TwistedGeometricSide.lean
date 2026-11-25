import Langlands.TraceFormula.TwistedGeometricUnfolding
import Langlands.TraceFormula.SingleOrbitGeometricTrace
import Langlands.TraceFormula.AbstractSimpleTwistedStatement
import Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceStatement
import Langlands.Analysis.Local.QuotientInStages

/-!
# The geometric side of the simple twisted trace formula

For a discrete subgroup `Γ` of a Hausdorff, locally compact, second countable group `G` with a
two-sided Haar measure, a continuous `θ` with `θ Γ ⊆ Γ`, `f ∈ C_c(G, ℂ)` satisfying the support
condition of `twistedGeometricSide_unfolding`, and representatives `r i` of the relevant
`Γ`-`θ`-conjugacy classes:

`∫_{Γ \ G} K(x, x) dν = ∑ i, vol((Γ ∩ C_{r i}) \ C_{r i}) · TO_{r i}(f)`

for any compatible measures on `C_{r i} \ G` and `(Γ ∩ C_{r i}) \ C_{r i}` with finite volumes
(`hasSum_twistedOrbitalIntegral_of_isCompatible`). The module states this in the forms used by
`TwistedGeometricMeasures` (`hasSum_twistedGeometricMeasures_term`,
`integral_twistedKernelDiagonal_eq_sum_term`, `integral_twistedKernelDiagonal_expansion`), derives
the conclusion of `AbstractSimpleTwistedTraceFormulaStatement` from the hypothesis that the trace is
the integral of the diagonal of the kernel
(`abstractSimpleTwistedTraceFormula_of_trace_eq_integral`), and reduces that statement to
`AbstractTwistedKernelDiagonalTraceStatement`
(`abstractSimpleTwistedTraceFormula_of_kernelDiagonalTrace`).
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory MeasureTheory.Measure Topology
open Langlands.QuotientIntegration Langlands.BaseChange Langlands.Analysis.OperatorIdeals
open scoped ENNReal NNReal CompactlySupported

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- For a discrete `Γ` and a closed subgroup `K`, a measure on `(Γ ⊓ K) \ G` compatible with
`(μG, Measure.count)` exists (`compatibleMeasureExists`). -/
private theorem exists_isCompatible_count_inf (μG : Measure G) [μG.IsHaarMeasure]
    [μG.IsMulRightInvariant] (Γ : Subgroup G) [DiscreteTopology Γ] (K : Subgroup G) :
    ∃ ν : Measure (LeftQuotient (Γ ⊓ K)), IsCompatible (Γ ⊓ K) μG Measure.count ν := by
  have hd : IsDiscrete ((Γ ⊓ K : Subgroup G) : Set G) :=
    (SetLike.isDiscrete_iff_discreteTopology.mpr ‹DiscreteTopology Γ›).mono inf_le_left
  have : DiscreteTopology (Γ ⊓ K : Subgroup G) := SetLike.isDiscrete_iff_discreteTopology.mp hd
  have hRc : IsClosed ((Γ ⊓ K : Subgroup G) : Set G) := Subgroup.isClosed_of_discreteTopology
  have : SecondCountableTopology (Γ ⊓ K : Subgroup G) :=
    TopologicalSpace.Subtype.secondCountableTopology ((Γ ⊓ K : Subgroup G) : Set G)
  have : (Measure.count : Measure (Γ ⊓ K : Subgroup G)).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hK => Measure.count_apply_lt_top.mpr hK.finite_of_discrete
      toIsMulLeftInvariant := inferInstance
      open_pos := fun _ _ hU => Measure.count_ne_zero hU }
  exact compatibleMeasureExists (Γ ⊓ K) hRc μG Measure.count

/-- **The geometric side**, for any compatible measures. Under the hypotheses of
`twistedGeometricSide_unfolding` (with `μG` also right invariant), let `μC i` be a right-invariant
measure on `C_{r i} = twistedCentralizer θ (r i)`, finite on compacts, `νC i` compatible with
`(μG, μC i)` on `C_{r i} \ G` and `νΓC i` compatible with `(μC i, Measure.count)` on
`(Γ.subgroupOf C_{r i}) \ C_{r i}`, of finite total mass. Then the twisted orbit functions are
integrable and

`HasSum (fun i => (νΓC i univ).toReal * TO_{r i}(f)) (∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν)`. -/
theorem hasSum_twistedOrbitalIntegral_of_isCompatible (μG : Measure G) [μG.IsHaarMeasure]
    [μG.IsMulRightInvariant] (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) (hν : IsCompatible Γ μG Measure.count ν)
    {Θ : Type*} [FunLike Θ G G] [MonoidHomClass Θ G G]
    (θ : Θ) (hθ : Continuous θ) (hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : C_c(G, ℂ))
    (hsupp : ∃ C : Set G, IsCompact C ∧
      ∀ x : G, ∀ γ ∈ Γ, f (x⁻¹ * γ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y)
    {ι : Type*} (r : ι → Γ)
    (hr : ∀ i j, IsTwistedConjugate Γ θ (r i : G) (r j : G) → i = j)
    (hcover : ∀ γ : Γ, (∃ x : G, f (x⁻¹ * (γ : G) * θ x) ≠ 0) →
      ∃ i, IsTwistedConjugate Γ θ (r i : G) (γ : G))
    [∀ i, MeasurableSpace (LeftQuotient (twistedCentralizer θ (r i : G)))]
    [∀ i, BorelSpace (LeftQuotient (twistedCentralizer θ (r i : G)))]
    [∀ i, MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (r i : G))))]
    [∀ i, BorelSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (r i : G))))]
    (μC : ∀ i, Measure (twistedCentralizer θ (r i : G)))
    [∀ i, (μC i).IsMulRightInvariant] [∀ i, IsFiniteMeasureOnCompacts (μC i)]
    (νC : ∀ i, Measure (LeftQuotient (twistedCentralizer θ (r i : G))))
    (νΓC : ∀ i, Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (r i : G)))))
    (hνC : ∀ i, IsCompatible (twistedCentralizer θ (r i : G)) μG (μC i) (νC i))
    (hνΓC : ∀ i, IsCompatible (Γ.subgroupOf (twistedCentralizer θ (r i : G))) (μC i)
      Measure.count (νΓC i))
    (hfin : ∀ i, νΓC i Set.univ ≠ ⊤) :
    HasSum (fun i => ((νΓC i Set.univ).toReal : ℂ) * twistedOrbitalIntegral θ (r i : G) (νC i) f)
        (∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν) ∧
      ∀ i, Integrable (twistedOrbitFunction θ (r i : G) f) (νC i) := by
  choose νr hνr using fun i => exists_isCompatible_count_inf μG Γ
    (twistedCentralizer θ (r i : G))
  obtain ⟨hsum, hint⟩ :=
    twistedGeometricSide_unfolding μG Γ ν hν θ hθ hθΓ f hsupp r hr hcover νr hνr
  have hstage : ∀ i,
      (Integrable (descend (Γ ⊓ twistedCentralizer θ (r i : G))
          (fun x => f (x⁻¹ * (r i : G) * θ x))
          (apply_twistedConj_left_mul_of_le inf_le_right ⇑f)) (νr i) ↔
        Integrable (twistedOrbitFunction θ (r i : G) f) (νC i)) ∧
      ∫ q, descend (Γ ⊓ twistedCentralizer θ (r i : G)) (fun x => f (x⁻¹ * (r i : G) * θ x))
          (apply_twistedConj_left_mul_of_le inf_le_right ⇑f) q ∂νr i =
        ((νΓC i Set.univ).toReal : ℂ) * twistedOrbitalIntegral θ (r i : G) (νC i) f := by
    intro i
    have : DiscreteTopology (Γ ⊓ twistedCentralizer θ (r i : G) : Subgroup G) :=
      SetLike.isDiscrete_iff_discreteTopology.mp
        ((SetLike.isDiscrete_iff_discreteTopology.mpr ‹DiscreteTopology Γ›).mono inf_le_left)
    have hC : IsClosed (twistedCentralizer θ (r i : G) : Set G) :=
      isClosed_eq ((continuous_inv.mul continuous_const).mul hθ) continuous_const
    have hΛ' : ∀ x : twistedCentralizer θ (r i : G),
        x ∈ Γ.subgroupOf (twistedCentralizer θ (r i : G)) ↔
          (x : G) ∈ Γ ⊓ twistedCentralizer θ (r i : G) :=
      fun x => ⟨fun h => Subgroup.mem_inf.2 ⟨h, x.2⟩, fun h => (Subgroup.mem_inf.1 h).1⟩
    have hFm : Measurable fun x : G => f (x⁻¹ * (r i : G) * θ x) :=
      (f.continuous.comp ((continuous_inv.mul continuous_const).mul hθ)).measurable
    have hF := apply_twistedConj_left_mul_of_le
      (le_refl (twistedCentralizer θ (r i : G))) (⇑f)
    refine ⟨(hνr i).integrable_descend_iff_of_le hC inf_le_right hΛ' (hνC i) (hνΓC i) (hfin i)
      (fun x => f (x⁻¹ * (r i : G) * θ x)) hFm hF, ?_⟩
    rw [(hνr i).integral_descend_eq_smul_of_le hC inf_le_right hΛ' (hνC i) (hνΓC i) (hfin i)
      (fun x => f (x⁻¹ * (r i : G) * θ x)) hFm hF, Complex.real_smul]
    rfl
  refine ⟨?_, fun i => (hstage i).1.1 (hint i)⟩
  have hfun : (fun i => ((νΓC i Set.univ).toReal : ℂ) *
      twistedOrbitalIntegral θ (r i : G) (νC i) f) =
      fun i => ∫ q, descend (Γ ⊓ twistedCentralizer θ (r i : G))
        (fun x => f (x⁻¹ * (r i : G) * θ x))
        (apply_twistedConj_left_mul_of_le inf_le_right ⇑f) q ∂νr i :=
    funext fun i => ((hstage i).2).symm
  rw [hfun]
  exact hsum

/-- **The geometric side with `TwistedGeometricMeasures`.** With the data of
`twistedGeometricSide_unfolding` for `θ : G →* G`, and measures `d i` of the geometric terms with
finite rational volumes:

`HasSum (fun i => (d i).term f) (∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν)`, and every
`twistedOrbitFunction θ (r i) f` is integrable for `(d i).orbital`. -/
theorem hasSum_twistedGeometricMeasures_term (μG : Measure G) [μG.IsHaarMeasure]
    [μG.IsMulRightInvariant] (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) (hν : IsCompatible Γ μG Measure.count ν)
    (θ : G →* G) (hθ : Continuous θ) (hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : C_c(G, ℂ))
    (hsupp : ∃ C : Set G, IsCompact C ∧
      ∀ x : G, ∀ γ ∈ Γ, f (x⁻¹ * γ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y)
    {ι : Type*} (r : ι → Γ)
    (hr : ∀ i j, IsTwistedConjugate Γ θ (r i : G) (r j : G) → i = j)
    (hcover : ∀ γ : Γ, (∃ x : G, f (x⁻¹ * (γ : G) * θ x) ≠ 0) →
      ∃ i, IsTwistedConjugate Γ θ (r i : G) (γ : G))
    (d : ∀ i, TwistedGeometricMeasures Γ θ (r i : G) μG)
    (hfin : ∀ i, (d i).rational Set.univ ≠ ⊤) :
    HasSum (fun i => (d i).term f) (∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν) ∧
      ∀ i, Integrable (twistedOrbitFunction θ (r i : G) f) (d i).orbital := by
  have : ∀ i, (d i).centralizer.IsMulRightInvariant := fun i => (d i).rightInvariant
  have : ∀ i, IsFiniteMeasureOnCompacts (d i).centralizer := fun i => (d i).finiteOnCompacts
  exact hasSum_twistedOrbitalIntegral_of_isCompatible μG Γ ν hν θ hθ hθΓ f hsupp r hr hcover
    (fun i => (d i).centralizer) (fun i => (d i).orbital) (fun i => (d i).rational)
    (fun i => (d i).orbital_compatible) (fun i => (d i).rational_compatible) hfin

/-- **The finite geometric expansion.** For finitely many representatives `r : Fin m → Γ`, the
integral of the diagonal of the twisted kernel is `∑ j, (d j).term f`: the hypothesis
`t = ∑ j, (d j).term f` of `SingleOrbitGeometricTraceStatement` with
`t = ∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν`. -/
theorem integral_twistedKernelDiagonal_eq_sum_term (μG : Measure G) [μG.IsHaarMeasure]
    [μG.IsMulRightInvariant] (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) (hν : IsCompatible Γ μG Measure.count ν)
    (θ : G →* G) (hθ : Continuous θ) (hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : C_c(G, ℂ))
    (hsupp : ∃ C : Set G, IsCompact C ∧
      ∀ x : G, ∀ γ ∈ Γ, f (x⁻¹ * γ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y)
    {m : ℕ} (r : Fin m → Γ)
    (hr : ∀ i j, IsTwistedConjugate Γ θ (r i : G) (r j : G) → i = j)
    (hcover : ∀ γ : Γ, (∃ x : G, f (x⁻¹ * (γ : G) * θ x) ≠ 0) →
      ∃ i, IsTwistedConjugate Γ θ (r i : G) (γ : G))
    (d : ∀ j, TwistedGeometricMeasures Γ θ (r j : G) μG)
    (hfin : ∀ j, (d j).rational Set.univ ≠ ⊤) :
    ∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν = ∑ j, (d j).term f :=
  ((hasSum_twistedGeometricMeasures_term μG Γ ν hν θ hθ hθΓ f hsupp r hr hcover d
    hfin).1.unique (hasSum_fintype _)).trans rfl

/-- **The hypothesis of `SingleOrbitGeometricTraceStatement`.** If every choice of measures for the
listed terms has finite rational volumes, then
`t = ∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν` satisfies the trace hypothesis of
`SingleOrbitGeometricTraceStatement`: for every `d`, the volumes are finite and
`t = ∑ j, (d j).term f`. -/
theorem integral_twistedKernelDiagonal_expansion (μG : Measure G) [μG.IsHaarMeasure]
    [μG.IsMulRightInvariant] (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) (hν : IsCompatible Γ μG Measure.count ν)
    (θ : G →* G) (hθ : Continuous θ) (hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : C_c(G, ℂ))
    (hsupp : ∃ C : Set G, IsCompact C ∧
      ∀ x : G, ∀ γ ∈ Γ, f (x⁻¹ * γ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y)
    {m : ℕ} (r : Fin m → Γ)
    (hr : ∀ i j, IsTwistedConjugate Γ θ (r i : G) (r j : G) → i = j)
    (hcover : ∀ γ : Γ, (∃ x : G, f (x⁻¹ * (γ : G) * θ x) ≠ 0) →
      ∃ i, IsTwistedConjugate Γ θ (r i : G) (γ : G))
    (hfinite : ∀ d : ∀ j, TwistedGeometricMeasures Γ θ (r j : G) μG,
      ∀ j, (d j).rational Set.univ ≠ ⊤) :
    ∀ d : ∀ j, TwistedGeometricMeasures Γ θ (r j : G) μG,
      (∀ j, (d j).rational Set.univ ≠ ⊤) ∧
        ∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν = ∑ j, (d j).term f :=
  fun d => ⟨hfinite d, integral_twistedKernelDiagonal_eq_sum_term μG Γ ν hν θ hθ hθΓ f hsupp r
    hr hcover d (hfinite d)⟩

/-- **The abstract simple twisted trace formula from the trace of the kernel.** Under the
hypotheses of `AbstractSimpleTwistedTraceFormulaStatement` (its support condition is the argument
`hsupp`, placed here after the others) and the hypothesis `htrace` that the trace of `R(f) ∘ I_θ`
is the integral over `Γ \ G` of the diagonal of the twisted kernel, its conclusion holds:
`tr (R(f) ∘ I_θ) = ∑ i, vol((Γ ∩ C_{r i}) \ C_{r i}) · TO_{r i}(f)`. -/
theorem abstractSimpleTwistedTraceFormula_of_trace_eq_integral
    (μG : Measure G) [μG.IsHaarMeasure] [μG.IsMulRightInvariant]
    (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) (hν : IsCompatible Γ μG Measure.count ν)
    (θ : G ≃ₜ* G) (hθΓ : ∀ x : G, θ x ∈ Γ ↔ x ∈ Γ)
    (_hθμ : MeasurePreserving θ μG μG)
    (hθν : MeasurePreserving (quotientAutomorphism Γ θ hθΓ).symm ν ν)
    (π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
    (hπnorm : ∀ (g : G) (φ : Lp ℂ 2 ν), ‖π g φ‖ = ‖φ‖)
    (hπmeas : ∀ φ : Lp ℂ 2 ν, AEStronglyMeasurable (fun g => π g φ) μG)
    (_hπ : ∀ (g : G) (φ : Lp ℂ 2 ν),
      (π g φ : LeftQuotient Γ → ℂ) =ᵐ[ν] fun q => φ (rightTranslate Γ g q))
    (f : C_c(G, ℂ))
    (_htc : IsTraceClass ((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
      (twistOperator Γ θ hθΓ ν hθν)))
    (n : ℕ) (r : Fin n → Γ)
    (hr : ∀ i j, IsTwistedConjugate Γ θ (r i : G) (r j : G) → i = j)
    (hcover : ∀ γ ∈ Γ, (∃ x : G, f (x⁻¹ * γ * θ x) ≠ 0) →
      ∃ i, IsTwistedConjugate Γ θ (r i : G) γ)
    [∀ i, MeasurableSpace (LeftQuotient (twistedCentralizer θ (r i : G)))]
    [∀ i, BorelSpace (LeftQuotient (twistedCentralizer θ (r i : G)))]
    [∀ i, MeasurableSpace
      (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (r i : G))))]
    [∀ i, BorelSpace
      (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (r i : G))))]
    (μC : ∀ i, Measure (twistedCentralizer θ (r i : G)))
    [∀ i, (μC i).IsMulRightInvariant] [∀ i, IsFiniteMeasureOnCompacts (μC i)]
    [∀ i, (μC i).IsOpenPosMeasure]
    (νC : ∀ i, Measure (LeftQuotient (twistedCentralizer θ (r i : G))))
    (νΓC : ∀ i, Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ (r i : G)))))
    (hνC : ∀ i, IsCompatible (twistedCentralizer θ (r i : G)) μG (μC i) (νC i))
    (hνΓC : ∀ i, IsCompatible (Γ.subgroupOf (twistedCentralizer θ (r i : G))) (μC i)
      Measure.count (νΓC i))
    (hfin : ∀ i, νΓC i Set.univ ≠ ⊤)
    (_hint : ∀ i, Integrable (twistedOrbitFunction θ (r i : G) f) (νC i))
    (hsupp : ∃ C : Set G, IsCompact C ∧
      ∀ x : G, ∀ γ ∈ Γ, f (x⁻¹ * γ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y)
    (htrace : operatorTrace ((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
      (twistOperator Γ θ hθΓ ν hθν)) =
      ∫ q, twistedKernelDiagonal Γ θ (fun γ hγ => (hθΓ γ).2 hγ) f q ∂ν) :
    operatorTrace ((Langlands.Analysis.integratedIsometricAction μG π hπnorm hπmeas f
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).comp
      (twistOperator Γ θ hθΓ ν hθν)) =
      ∑ i, ((νΓC i Set.univ).toReal : ℂ) * twistedOrbitalIntegral θ (r i : G) (νC i) f := by
  rw [htrace]
  have h := (hasSum_twistedOrbitalIntegral_of_isCompatible μG Γ ν hν θ θ.continuous
    (fun γ hγ => (hθΓ γ).2 hγ) f hsupp r hr (fun γ hγ => hcover γ γ.2 hγ) μC νC νΓC hνC hνΓC
    hfin).1
  exact h.unique (hasSum_fintype _)

/-- **The abstract simple twisted trace formula from the kernel identity.** The trace of
`R(f) ∘ I_θ` being the integral of the diagonal of its kernel
(`AbstractTwistedKernelDiagonalTraceStatement`), the geometric side gives
`AbstractSimpleTwistedTraceFormulaStatement`. -/
theorem abstractSimpleTwistedTraceFormula_of_kernelDiagonalTrace :
    AbstractTwistedKernelDiagonalTraceStatement.{u} →
      AbstractSimpleTwistedTraceFormulaStatement.{u} := by
  intro hK G _ _ _ _ _ _ _ _ μG _ _ Γ _ _ _ ν hν θ hθΓ hθμ hθν π hπnorm hπmeas hπ f htc hsupp n r
    hr hcover _ _ _ _ μC _ _ _ νC νΓC hνC hνΓC hfin hint
  exact abstractSimpleTwistedTraceFormula_of_trace_eq_integral μG Γ ν hν θ hθΓ hθμ hθν π hπnorm
    hπmeas hπ f htc n r hr hcover μC νC νΓC hνC hνΓC hfin hint hsupp
    (hK μG Γ ν hν θ hθΓ hθμ hθν π hπnorm hπmeas hπ f htc)

end Langlands.TraceFormula
