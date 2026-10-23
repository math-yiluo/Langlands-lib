import Langlands.HarmonicAnalysis.AlgebraicIntegral
import Langlands.HarmonicAnalysis.AlgebraicIntegrand
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof

/-! # Weak integration tested by the smooth contragredient -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.SmoothWeakIntegral

universe uX uG uV uW

variable {X : Type uX} [MeasurableSpace X]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ρ : Representation ℂ G V) (μ : Measure X)

/-- A representing vector for genuine scalar integration against every smooth
functional. Scalar integrability is part of the relation. -/
def HasIntegral (f : X → V) (v : V) : Prop :=
  ∀ ℓ : SmoothDual ρ,
    MeasureTheory.Integrable (fun x => ℓ.val (f x)) μ ∧
      (∫ x, ℓ.val (f x) ∂μ) = ℓ.val v

/-- Weak integrability includes existence of a representing vector in the
original algebraic carrier, not merely existence of all scalar integrals. -/
def Integrable (f : X → V) : Prop := ∃ v, HasIntegral ρ μ f v

variable {ρ μ} {f g : X → V} {v w : V}

/-- Zero has representing vector zero, for an arbitrary measure. -/
theorem hasIntegral_zero : HasIntegral ρ μ (0 : X → V) 0 := by
  intro ℓ
  simp only [Pi.zero_apply, map_zero]
  exact ⟨integrable_zero _ _ _, integral_zero _ _⟩

/-- Addition is inherited from the genuine scalar Bochner integral. -/
theorem HasIntegral.add (hf : HasIntegral ρ μ f v) (hg : HasIntegral ρ μ g w) :
    HasIntegral ρ μ (f + g) (v + w) := by
  intro ℓ
  simp only [Pi.add_apply, map_add]
  exact ⟨(hf ℓ).1.add (hg ℓ).1,
    (integral_add (hf ℓ).1 (hg ℓ).1).trans (by rw [(hf ℓ).2, (hg ℓ).2])⟩

/-- Complex homogeneity is inherited from the scalar integral. -/
theorem HasIntegral.smul (c : ℂ) (hf : HasIntegral ρ μ f v) :
    HasIntegral ρ μ (c • f) (c • v) := by
  intro ℓ
  simp only [Pi.smul_apply, map_smul]
  exact ⟨(hf ℓ).1.smul c, (integral_smul c _).trans (by rw [(hf ℓ).2])⟩

/-- The actual functions admitting a representing vector form a submodule. -/
def integrableSubmodule (ρ : Representation ℂ G V) (μ : Measure X) :
    Submodule ℂ (X → V) where
  carrier := {f | Integrable ρ μ f}
  zero_mem' := ⟨0, hasIntegral_zero⟩
  add_mem' := by
    rintro f g ⟨v, hv⟩ ⟨w, hw⟩
    exact ⟨v + w, hv.add hw⟩
  smul_mem' := by
    rintro c f ⟨v, hv⟩
    exact ⟨c • v, hv.smul c⟩

@[simp] theorem mem_integrableSubmodule :
    f ∈ integrableSubmodule ρ μ ↔ Integrable ρ μ f := Iff.rfl

section Uniqueness

variable [IsTopologicalGroup G]
variable (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
  IsCompact (L : Set G) ∧ L ≤ K) (hρ : IsSmooth ρ)

include hcofinal hρ in
/-- Separation by the smooth dual makes the representing vector unique. -/
theorem HasIntegral.unique (hf : HasIntegral ρ μ f v) (hg : HasIntegral ρ μ f w) :
    v = w := by
  apply smoothBidual_injective_of_compact_cofinal hcofinal ρ hρ
  apply Subtype.ext
  apply LinearMap.ext
  intro ℓ
  change ℓ.val v = ℓ.val w
  exact (hf ℓ).2.symm.trans (hg ℓ).2

/-- The linear integral on its actual domain of representability. Choice is
made only from the existence proof carried by each domain element. -/
def integralLinear : integrableSubmodule ρ μ →ₗ[ℂ] V where
  toFun f := Classical.choose f.property
  map_add' f g :=
    HasIntegral.unique hcofinal hρ (Classical.choose_spec (f + g).property)
      ((Classical.choose_spec f.property).add (Classical.choose_spec g.property))
  map_smul' c f :=
    HasIntegral.unique hcofinal hρ (Classical.choose_spec (c • f).property)
      ((Classical.choose_spec f.property).smul c)

/-- The selected integral satisfies every smooth scalar test. -/
theorem integralLinear_spec (f : integrableSubmodule ρ μ) :
    HasIntegral ρ μ f.val (integralLinear hcofinal hρ f) :=
  Classical.choose_spec f.property

/-- Every explicit weak integral agrees with the linear integral. -/
theorem integralLinear_eq (f : integrableSubmodule ρ μ) {v : V}
    (hv : HasIntegral ρ μ f.val v) : integralLinear hcofinal hρ f = v :=
  (integralLinear_spec hcofinal hρ f).unique hcofinal hρ hv

/-- Evaluation of the linear integral is the genuine complex integral. -/
theorem integralLinear_eval (f : integrableSubmodule ρ μ) (ℓ : SmoothDual ρ) :
    ℓ.val (integralLinear hcofinal hρ f) = ∫ x, ℓ.val (f.val x) ∂μ :=
  ((integralLinear_spec hcofinal hρ f) ℓ).2.symm

end Uniqueness

section Naturality

variable [IsTopologicalGroup G]
variable {σ : Representation ℂ G W}

/-- Pulling a smooth functional back along an actual intertwiner preserves the
scalar test, so intertwiners preserve weak integrals. -/
theorem HasIntegral.map (hf : HasIntegral ρ μ f v) (T : ρ.IntertwiningMap σ) :
    HasIntegral σ μ (fun x => T (f x)) (T v) := by
  intro ℓ
  exact hf (contragredientMap T ℓ)

/-- Postcomposition by an intertwiner preserves the actual integrable domain. -/
def mapIntegrable (T : ρ.IntertwiningMap σ) :
    integrableSubmodule ρ μ →ₗ[ℂ] integrableSubmodule σ μ where
  toFun f := ⟨fun x => T (f.val x), by
    obtain ⟨v, hv⟩ := f.property
    exact ⟨T v, hv.map T⟩⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact T.toLinearMap.map_add _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact T.toLinearMap.map_smul c _

/-- Naturality of the chosen linear integral, with uniqueness hypotheses on
both representations explicit. -/
theorem integralLinear_map
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (T : ρ.IntertwiningMap σ)
    (f : integrableSubmodule ρ μ) :
    integralLinear hcofinal hσ (mapIntegrable T f) =
      T (integralLinear hcofinal hρ f) :=
  integralLinear_eq hcofinal hσ _ ((integralLinear_spec hcofinal hρ f).map T)

end Naturality

/-- Finite-measure-support simple functions have their finite fiber-sum integral
as weak integral; no separation hypothesis is needed for this relation. -/
theorem hasIntegral_simpleFunc (f : SimpleFunc X V) (hf : f.FinMeasSupp μ) :
    HasIntegral ρ μ f (AlgebraicIntegral.integral μ f) := by
  intro ℓ
  have hmap := hf.map ℓ.val.map_zero
  refine ⟨hmap.integrable, ?_⟩
  change (∫ x, (f.map ℓ.val) x ∂μ) = _
  rw [← AlgebraicIntegral.integral_eq_bochner _ hmap,
    AlgebraicIntegral.integral_linearMap f hf ℓ.val]

/-- The simple-function comparison also identifies the chosen linear integral. -/
theorem integralLinear_simpleFunc [IsTopologicalGroup G]
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K) (hρ : IsSmooth ρ)
    (f : SimpleFunc X V) (hf : f.FinMeasSupp μ) :
    integralLinear hcofinal hρ
      ⟨f, ⟨AlgebraicIntegral.integral μ f, hasIntegral_simpleFunc f hf⟩⟩ =
      AlgebraicIntegral.integral μ f :=
  integralLinear_eq hcofinal hρ _ (hasIntegral_simpleFunc f hf)

section CompactLocallyConstant

variable [TopologicalSpace X] [OpensMeasurableSpace X]
variable [IsFiniteMeasureOnCompacts μ]

/-- Compact locally constant functions are covered via the published genuine
simple-function conversion and its finite-measure-support theorem. -/
theorem hasIntegral_compactlySupported (f : X → V) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) :
    HasIntegral ρ μ f
      (AlgebraicIntegral.integral μ (compactlySupportedSimpleFunc f hf hc)) :=
  hasIntegral_simpleFunc (compactlySupportedSimpleFunc f hf hc)
    (compactlySupportedSimpleFunc_finMeasSupp μ f hf hc)

/-- In particular these actual functions belong to the weak integrable submodule. -/
theorem integrable_compactlySupported (f : X → V) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) : Integrable ρ μ f :=
  ⟨_, hasIntegral_compactlySupported f hf hc⟩

end CompactLocallyConstant

end Langlands.HarmonicAnalysis.SmoothWeakIntegral
