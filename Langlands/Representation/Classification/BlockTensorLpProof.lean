import Langlands.Representation.Classification.BlockTensorLpStatement
import Langlands.Representation.Tensor.SmoothDual
import Langlands.Representation.Tensor.SmoothDualSurjectivityProof
import Langlands.Representation.Tensor.UnitaryCentralCharacter
import Langlands.Representation.MatrixCoefficient.NormRegularityProof
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Group.Center.FiniteProduct
import Langlands.Group.GL.CentralQuotientTopologyProof
import Langlands.Group.GL.CompactOpen
import Langlands.Analysis.HaarLpProof
import Langlands.Analysis.FiniteProductLpProof
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Common finite-exponent analytic block tensor comparison

The actual full-center quotient equivalence and Haar comparison reduce pure
coefficients to finite products. Tensor induction and admissible smooth-dual
surjectivity give preservation for all coefficients; nonzero auxiliary smooth
coefficients give reflection. The closing theorem retains the complete
published GL target and its independent field and carrier universes.
-/

noncomputable section

namespace Langlands

open MeasureTheory

universe uI uG uF uV

namespace FiniteTensor

variable {ι : Type uI} [Fintype ι]
variable {G : ι → Type uG} [∀ i, Group (G i)]
variable [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable {ρ : ∀ i, Representation ℂ (G i) (V i)}

/-- The actual descended norm of a pure coefficient is the separated product
on the actual full-center quotient, for any supplied character witnesses. -/
theorem coefficientNorm_smoothDualTensorMap_tprod
    (c : ∀ i, UnitaryCentralCharacter (ρ i))
    (d : UnitaryCentralCharacter (external ρ))
    (ℓ : ∀ i, SmoothDual (ρ i)) (v : ∀ i, V i)
    (q : (∀ i, G i) ⧸ Subgroup.center (∀ i, G i)) :
    d.coefficientNorm
        (smoothDualPairing (external ρ)
          (smoothDualTensorMap ρ (PiTensorProduct.tprod ℂ ℓ)))
        (PiTensorProduct.tprod ℂ v) q =
      ∏ i, (c i).coefficientNorm (smoothDualPairing (ρ i) (ℓ i)) (v i)
        (Langlands.Group.Center.quotientPiMulEquiv G q i) := by
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [UnitaryCentralCharacter.coefficientNorm_mk,
      Langlands.Group.Center.quotientPiMulEquiv_mk]
    rw [matrixCoefficient_smoothDualTensorMap_tprod, norm_prod]

end FiniteTensor

namespace UnitaryCentralCharacter

variable {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {W : Type uV} [AddCommGroup W] [Module ℂ W]
variable {σ : Representation ℂ H W}

/-- A coefficient nonzero at the identity remains nonzero as an a.e. class
for any measure positive on nonempty open sets. -/
theorem coefficientNorm_not_ae_zero
    (c : UnitaryCentralCharacter σ)
    (ℓ : Module.Dual ℂ W) (v : W) (hv : IsSmoothVector σ v)
    (hne : ℓ v ≠ 0)
    [MeasurableSpace (H ⧸ Subgroup.center H)]
    (μ : Measure (H ⧸ Subgroup.center H)) [μ.IsOpenPosMeasure] :
    ¬ c.coefficientNorm ℓ v =ᵐ[μ] 0 := by
  intro h
  have heq := ((c.continuous_coefficientNorm ℓ v hv).ae_eq_iff_eq
    μ continuous_zero).mp h
  have hzero := congrFun heq (QuotientGroup.mk (1 : H))
  have : ‖ℓ v‖ = 0 := by
    simpa only [coefficientNorm_mk, matrixCoefficient_apply,
      map_one, Module.End.one_apply, Pi.zero_apply] using hzero
  exact hne (norm_eq_zero.mp this)

section Closure

variable [MeasurableSpace (H ⧸ Subgroup.center H)]
variable [BorelSpace (H ⧸ Subgroup.center H)]
variable (c : UnitaryCentralCharacter σ)
variable (μ : Measure (H ⧸ Subgroup.center H)) (r : ENNReal)

/-- The triangle inequality for descended coefficient norms preserves membership
when adding functionals. Smoothness is needed only for the vector. -/
theorem memLp_coefficientNorm_add_functional
    (ℓ m : Module.Dual ℂ W) (v : W) (hv : IsSmoothVector σ v)
    (hℓ : MemLp (c.coefficientNorm ℓ v) r μ)
    (hm : MemLp (c.coefficientNorm m v) r μ) :
    MemLp (c.coefficientNorm (ℓ + m) v) r μ := by
  apply (hℓ.add hm).mono' (c.aestronglyMeasurable_coefficientNorm _ _ hv μ)
  apply Filter.Eventually.of_forall
  intro q
  rw [Real.norm_of_nonneg (c.coefficientNorm_nonneg _ _ q)]
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [Pi.add_apply, coefficientNorm_mk, matrixCoefficient_apply,
      LinearMap.add_apply]
    exact norm_add_le _ _

/-- The triangle inequality for descended coefficient norms preserves membership
when adding vectors. -/
theorem memLp_coefficientNorm_add_vector
    (ℓ : Module.Dual ℂ W) (v w : W)
    (hv : IsSmoothVector σ v) (hw : IsSmoothVector σ w)
    (hvLp : MemLp (c.coefficientNorm ℓ v) r μ)
    (hwLp : MemLp (c.coefficientNorm ℓ w) r μ) :
    MemLp (c.coefficientNorm ℓ (v + w)) r μ := by
  apply (hvLp.add hwLp).mono'
    (c.aestronglyMeasurable_coefficientNorm _ _ ((smoothVectors σ).add_mem hv hw) μ)
  apply Filter.Eventually.of_forall
  intro q
  rw [Real.norm_of_nonneg (c.coefficientNorm_nonneg _ _ q)]
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [Pi.add_apply, coefficientNorm_mk, matrixCoefficient_apply, map_add]
    exact norm_add_le _ _

omit [IsTopologicalGroup H] [BorelSpace (H ⧸ Subgroup.center H)] in
/-- Scaling a functional scales the descended norm by the scalar's absolute value. -/
theorem memLp_coefficientNorm_smul_functional
    (a : ℂ) (ℓ : Module.Dual ℂ W) (v : W)
    (h : MemLp (c.coefficientNorm ℓ v) r μ) :
    MemLp (c.coefficientNorm (a • ℓ) v) r μ := by
  have heq : c.coefficientNorm (a • ℓ) v = ‖a‖ • c.coefficientNorm ℓ v := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      simp only [coefficientNorm_mk, matrixCoefficient_apply, LinearMap.smul_apply,
        smul_eq_mul, norm_mul, Pi.smul_apply]
  rw [heq]
  exact h.const_smul ‖a‖

omit [IsTopologicalGroup H] [BorelSpace (H ⧸ Subgroup.center H)] in
/-- Scaling a vector scales the descended norm by the scalar's absolute value. -/
theorem memLp_coefficientNorm_smul_vector
    (a : ℂ) (ℓ : Module.Dual ℂ W) (v : W)
    (h : MemLp (c.coefficientNorm ℓ v) r μ) :
    MemLp (c.coefficientNorm ℓ (a • v)) r μ := by
  have heq : c.coefficientNorm ℓ (a • v) = ‖a‖ • c.coefficientNorm ℓ v := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      simp only [coefficientNorm_mk, matrixCoefficient_apply, map_smul,
        smul_eq_mul, norm_mul, Pi.smul_apply]
  rw [heq]
  exact h.const_smul ‖a‖

end Closure

end UnitaryCentralCharacter

/-- Compact-open cofinality supplies a smooth functional separating each nonzero
vector; this is the separating consequence of the published smooth bidual map. -/
theorem exists_smoothDual_pairing_ne_zero_of_ne_zero
    {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {W : Type uV} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ H W) (hσ : IsSmooth σ)
    (hcofinal : ∀ K : OpenSubgroup H, ∃ L : OpenSubgroup H,
      IsCompact (L : Set H) ∧ L ≤ K)
    (v : W) (hv : v ≠ 0) :
    ∃ ℓ : SmoothDual σ, smoothDualPairing σ ℓ v ≠ 0 := by
  by_contra! h
  apply hv
  apply smoothBidual_injective_of_compact_cofinal hcofinal σ hσ
  apply Subtype.ext
  apply LinearMap.ext
  intro ℓ
  change smoothDualPairing σ ℓ v = smoothDualPairing σ ℓ 0
  rw [h ℓ, map_zero]

/-- Nontrivial smooth factors have a smooth coefficient nonzero at the identity. -/
theorem exists_smooth_coefficient_ne_zero
    {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {W : Type uV} [AddCommGroup W] [Module ℂ W] [Nontrivial W]
    (σ : Representation ℂ H W) (hσ : IsSmooth σ)
    (hcofinal : ∀ K : OpenSubgroup H, ∃ L : OpenSubgroup H,
      IsCompact (L : Set H) ∧ L ≤ K) :
    ∃ (ℓ : SmoothDual σ) (v : W), smoothDualPairing σ ℓ v ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  obtain ⟨ℓ, hℓ⟩ := exists_smoothDual_pairing_ne_zero_of_ne_zero σ hσ hcofinal v hv
  exact ⟨ℓ, v, hℓ⟩

namespace FiniteTensor

variable {ι : Type uI} [Fintype ι]
variable {G : ι → Type uG} [∀ i, Group (G i)]
variable [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable {ρ : ∀ i, Representation ℂ (G i) (V i)}

/-- Two tensor inductions extend pure-coefficient membership to all vector tensors
and every functional in the canonical smooth-dual tensor map's image. -/
theorem memLp_coefficientNorm_smoothDualTensorMap
    (hρ : ∀ i, IsSmooth (ρ i))
    (c : UnitaryCentralCharacter (external ρ))
    [MeasurableSpace ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i))]
    [BorelSpace ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i))]
    (μ : Measure ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i))) (r : ENNReal)
    (hpure : ∀ (ℓ : ∀ i, SmoothDual (ρ i)) (v : ∀ i, V i),
      MemLp (c.coefficientNorm
        (smoothDualPairing (external ρ)
          (smoothDualTensorMap ρ (PiTensorProduct.tprod ℂ ℓ)))
        (PiTensorProduct.tprod ℂ v)) r μ)
    (x : PiTensorProduct ℂ (fun i => SmoothDual (ρ i))) (y : PiTensorProduct ℂ V) :
    MemLp (c.coefficientNorm
      (smoothDualPairing (external ρ) (smoothDualTensorMap ρ x)) y) r μ := by
  have hs := isSmooth_external ρ hρ
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a ℓ =>
    rw [map_smul, map_smul]
    apply c.memLp_coefficientNorm_smul_functional μ r a
    induction y using PiTensorProduct.induction_on with
    | smul_tprod b v =>
      exact c.memLp_coefficientNorm_smul_vector μ r b _ _ (hpure ℓ v)
    | add y z hy hz =>
      exact c.memLp_coefficientNorm_add_vector μ r _ y z (hs y) (hs z) hy hz
  | add x z hx hz =>
    rw [map_add, map_add]
    exact c.memLp_coefficientNorm_add_functional μ r _ _ y (hs y) hx hz

end FiniteTensor

namespace Group.Center

variable {ι : Type uI} [Fintype ι]
variable (G : ι → Type uG) [∀ i, Group (G i)]
variable [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
variable [∀ i, MeasurableSpace (G i ⧸ Subgroup.center (G i))]
variable [∀ i, BorelSpace (G i ⧸ Subgroup.center (G i))]
variable [∀ i, SecondCountableTopology (G i ⧸ Subgroup.center (G i))]
variable [MeasurableSpace ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i))]
variable [BorelSpace ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i))]
variable [LocallyCompactSpace ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i))]
variable [SecondCountableTopology ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i))]

/-- Membership for an arbitrary Haar normalization of the full product central
quotient is equivalent to membership after the actual product-quotient map. -/
theorem memLp_quotientPi_iff
    (ν : ∀ i, Measure (G i ⧸ Subgroup.center (G i)))
    [∀ i, (ν i).IsHaarMeasure] [∀ i, SigmaFinite (ν i)]
    (μ : Measure ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i)))
    [μ.IsHaarMeasure]
    (f : ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i)) → ℝ)
    (r : ENNReal) :
    MemLp f r μ ↔
      MemLp (f ∘ (quotientPiContinuousMulEquiv G).symm) r (Measure.pi ν) := by
  let e := quotientPiContinuousMulEquiv G
  have : (Measure.map e.symm (Measure.pi ν)).IsHaarMeasure :=
    e.symm.isHaarMeasure_map (Measure.pi ν)
  exact (haarMemLpInvariant _ μ (Measure.map e.symm (Measure.pi ν)) f r).trans
    (quotientPiMeasurableEquiv G).symm.memLp_map_measure_iff

end Group.Center

/-- The fixed-exponent coefficient predicate is independent of Haar normalization
within the supplied Borel realization of a locally compact second-countable quotient. -/
theorem isLpModCenter_iff_haar
    {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {W : Type uV} [AddCommGroup W] [Module ℂ W]
    [LocallyCompactSpace (H ⧸ Subgroup.center H)]
    [SecondCountableTopology (H ⧸ Subgroup.center H)]
    [MeasurableSpace (H ⧸ Subgroup.center H)]
    [BorelSpace (H ⧸ Subgroup.center H)]
    (σ : Representation ℂ H W)
    (μ ν : Measure (H ⧸ Subgroup.center H)) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (r : ℝ) : IsLpModCenter σ μ r ↔ IsLpModCenter σ ν r := by
  constructor
  · rintro ⟨hσ, c, hc⟩
    exact ⟨hσ, c, fun ℓ v => (haarMemLpInvariant _ μ ν _ _).mp (hc ℓ v)⟩
  · rintro ⟨hσ, c, hc⟩
    exact ⟨hσ, c, fun ℓ v => (haarMemLpInvariant _ ν μ _ _).mp (hc ℓ v)⟩

namespace FiniteTensor

variable {ι : Type uI} [Fintype ι]
variable {G : ι → Type uG} [∀ i, Group (G i)]
variable [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
variable {ρ : ∀ i, Representation ℂ (G i) (V i)}

/-- The pure coefficient formula after transporting to the actual product quotient. -/
theorem coefficientNorm_smoothDualTensorMap_tprod_comp
    (c : ∀ i, UnitaryCentralCharacter (ρ i))
    (d : UnitaryCentralCharacter (external ρ))
    (ℓ : ∀ i, SmoothDual (ρ i)) (v : ∀ i, V i) :
    (d.coefficientNorm
      (smoothDualPairing (external ρ)
        (smoothDualTensorMap ρ (PiTensorProduct.tprod ℂ ℓ)))
      (PiTensorProduct.tprod ℂ v)) ∘ (Group.Center.quotientPiContinuousMulEquiv G).symm =
      fun q => ∏ i, (c i).coefficientNorm (smoothDualPairing (ρ i) (ℓ i)) (v i) (q i) := by
  funext q
  have he : Group.Center.quotientPiMulEquiv G
      ((Group.Center.quotientPiContinuousMulEquiv G).symm q) = q :=
    (Group.Center.quotientPiMulEquiv G).apply_symm_apply q
  simpa only [Function.comp_apply, he] using
    coefficientNorm_smoothDualTensorMap_tprod c d ℓ v
      ((Group.Center.quotientPiContinuousMulEquiv G).symm q)

/- Generic analytic assembly for the actual canonical smooth-dual tensor map. -/
private theorem isLpModCenter_external_iff
    [Nonempty ι] [∀ i, Nontrivial (V i)]
    [∀ i, MeasurableSpace (G i ⧸ Subgroup.center (G i))]
    [∀ i, BorelSpace (G i ⧸ Subgroup.center (G i))]
    [∀ i, SecondCountableTopology (G i ⧸ Subgroup.center (G i))]
    [MeasurableSpace ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i))]
    [BorelSpace ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i))]
    [LocallyCompactSpace ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i))]
    [SecondCountableTopology ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i))]
    (hρ : ∀ i, IsAdmissible (ρ i))
    (hcofinal : ∀ i (K : OpenSubgroup (G i)), ∃ L : OpenSubgroup (G i),
      IsCompact (L : Set (G i)) ∧ L ≤ K)
    (hdual : Function.Surjective (smoothDualTensorMap ρ))
    (ν : ∀ i, Measure (G i ⧸ Subgroup.center (G i)))
    [∀ i, (ν i).IsHaarMeasure] [∀ i, SigmaFinite (ν i)]
    (μ : Measure ((∀ i, G i) ⧸ Subgroup.center (∀ i, G i))) [μ.IsHaarMeasure]
    (r : ℝ) (hr : 0 < r) :
    (∀ i, IsLpModCenter (ρ i) (ν i) r) ↔ IsLpModCenter (external ρ) μ r := by
  classical
  constructor
  · intro h
    have hc : ∀ i, ∃ c : UnitaryCentralCharacter (ρ i),
        ∀ (ℓ : SmoothDual (ρ i)) (v : V i),
          MemLp (c.coefficientNorm ℓ v) (ENNReal.ofReal r) (ν i) := fun i => (h i).2
    choose c hc using hc
    let d := externalUnitaryCentralCharacter c
    refine ⟨isAdmissible_external ρ hρ, d, ?_⟩
    intro ℓ y
    obtain ⟨x, rfl⟩ := hdual ℓ
    apply memLp_coefficientNorm_smoothDualTensorMap (fun i => (hρ i).1) d μ _ ?_ x y
    intro ℓ v
    apply (Group.Center.memLp_quotientPi_iff G ν μ _ _).mpr
    rw [coefficientNorm_smoothDualTensorMap_tprod_comp c d ℓ v]
    exact finiteProductMemLpPreservation ι _ ν _ r hr (fun i => hc i (ℓ i) (v i))
  · rintro ⟨_, d, hd⟩ i
    let c := restrictUnitaryCentralCharacter d
    refine ⟨hρ i, c i, ?_⟩
    intro ℓ v
    by_cases hzero : (c i).coefficientNorm ℓ v =ᵐ[ν i] 0
    · exact (memLp_congr_ae hzero).mpr MemLp.zero
    · have haux : ∀ j, ∃ (ℓ₀ : SmoothDual (ρ j)) (v₀ : V j),
          smoothDualPairing (ρ j) ℓ₀ v₀ ≠ 0 := fun j =>
        exists_smooth_coefficient_ne_zero (ρ j) (hρ j).1 (hcofinal j)
      choose ℓ₀ v₀ haux using haux
      let L := Function.update ℓ₀ i ℓ
      let w := Function.update v₀ i v
      let f := fun j => (c j).coefficientNorm (smoothDualPairing (ρ j) (L j)) (w j)
      have hmeas : ∀ j, AEStronglyMeasurable (f j) (ν j) := fun j =>
        (c j).aestronglyMeasurable_coefficientNorm _ _ ((hρ j).1 (w j)) (ν j)
      have hnonzero : ∀ j, ¬ f j =ᵐ[ν j] 0 := by
        intro j
        by_cases hj : j = i
        · subst j
          simpa only [f, L, w, Function.update_self, smoothDualPairing,
            Submodule.subtype_apply] using hzero
        · dsimp only [f, L, w]
          rw [Function.update_of_ne hj, Function.update_of_ne hj]
          exact (c j).coefficientNorm_not_ae_zero _ _ ((hρ j).1 _) (haux j) (ν j)
      have hp : MemLp (fun q => ∏ j, f j (q j)) (ENNReal.ofReal r) (Measure.pi ν) := by
        have ht := (Group.Center.memLp_quotientPi_iff G ν μ _ _).mp
          (hd (smoothDualTensorMap ρ (PiTensorProduct.tprod ℂ L))
            (PiTensorProduct.tprod ℂ w))
        change MemLp ((d.coefficientNorm
          (smoothDualPairing (external ρ)
            (smoothDualTensorMap ρ (PiTensorProduct.tprod ℂ L)))
          (PiTensorProduct.tprod ℂ w)) ∘ (Group.Center.quotientPiContinuousMulEquiv G).symm)
          (ENNReal.ofReal r) (Measure.pi ν) at ht
        rwa [coefficientNorm_smoothDualTensorMap_tprod_comp c d L w] at ht
      have hi := ((finiteProductMemLpNonzeroIff ι _ ν f hmeas hnonzero r hr).mp hp) i
      simpa only [f, L, w, Function.update_self, smoothDualPairing,
        Submodule.subtype_apply] using hi

end FiniteTensor

/- Specialize the generic assembly to the supplied actual GL topologies. -/
private theorem glBlockTensorLp_of_smoothDualSurjectivity
    (hdual : FiniteTensor.SmoothDualTensorSurjectivityStatement.{0, uF, uV}) :
    GLBlockTensorLpStatement.{uF, uV} := by
  classical
  intro p _ F T
  let := T.topology
  intro n hn B
  let := T.leviTopology B
  have := T.leviTopologicalGroup B
  intro V _ _ ρ hirr hadm r hr
  let G := fun i : Fin B.length => GeneralLinear (B.size i) F.Carrier
  let Q := fun i => G i ⧸ Subgroup.center (G i)
  have : Nonempty (Fin B.length) := ⟨(B.indexEquiv.symm ⟨0, hn⟩).1⟩
  have : ∀ i, Nontrivial (V i) := fun i => by
    have := hirr i
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact (bot_ne_top : (⊥ : Subrepresentation (ρ i)) ≠ ⊤)
      (Subrepresentation.ext (Subsingleton.elim _ _))
  have : ∀ i, IsTopologicalGroup (G i) :=
    fun i => T.generalLinearTopologicalGroup (B.size i)
  have hq : ∀ i, CentralQuotientHaarTopology (G i) :=
    fun i => (glBlockCentralQuotientTopology p F T (B.size i)).1
  have hM := (glBlockCentralQuotientTopology p F T n).2 B
  have : ∀ i, LocallyCompactSpace (Q i) := fun i => (hq i).2.2.1
  have : ∀ i, SecondCountableTopology (Q i) := fun i => (hq i).2.2.2.1
  have : LocallyCompactSpace
      (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)) := hM.2.2.1
  have : SecondCountableTopology
      (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)) := hM.2.2.2.1
  let : ∀ i, MeasurableSpace (Q i) :=
    fun i => T.centralQuotientMeasurableSpace (B.size i)
  have : ∀ i, BorelSpace (Q i) := fun i => T.centralQuotientBorelSpace (B.size i)
  have hex : ∀ i, ∃ ν : Measure (Q i), ν.IsHaarMeasure :=
    fun i => (hq i).2.2.2.2.1
  choose ν hν using hex
  have : ∀ i, (ν i).IsHaarMeasure := hν
  have : ∀ i, SigmaFinite (ν i) := fun i => (hq i).2.2.2.2.2 (ν i)
  have hcofinal : ∀ i (K : OpenSubgroup (G i)), ∃ L : OpenSubgroup (G i),
      IsCompact (L : Set (G i)) ∧ L ≤ K := by
    intro i K
    obtain ⟨L, hc, hLK⟩ :=
      T.generalLinearCompactOpen (B.size i) (K : Set (G i)) K.mem_nhds_one
    exact ⟨L, hc, hLK⟩
  have hsurj : Function.Surjective (FiniteTensor.smoothDualTensorMap ρ) :=
    hdual (Fin B.length) G V ρ hadm hcofinal
  have hpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  constructor
  · intro h _ _ μ _
    apply (FiniteTensor.isLpModCenter_external_iff hadm hcofinal
      hsurj ν μ r hpos).mp
    exact fun i => h i (ν i)
  · intro h i
    let := borel (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))
    have : BorelSpace
        (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)) := ⟨rfl⟩
    obtain ⟨μ, hμ⟩ := hM.2.2.2.2.1
    have := hμ
    have hf := (FiniteTensor.isLpModCenter_external_iff hadm hcofinal
      hsurj ν μ r hpos).mpr (h μ)
    intro η _
    exact (isLpModCenter_iff_haar (ρ i) (ν i) η r).mp (hf i)

/-- The complete finite-exponent comparison for actual irreducible admissible
GL block tensors, with every Borel Haar realization and both universes retained. -/
theorem glBlockTensorLp : GLBlockTensorLpStatement.{uF, uV} :=
  glBlockTensorLp_of_smoothDualSurjectivity
    FiniteTensor.smoothDualTensorSurjectivity.{0, uF, uV}

end Langlands
