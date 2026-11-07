import Langlands.Automorphic.ConstantTerm
import Langlands.Global.AdelesSecondCountable
import Langlands.Global.PrincipalAdelesDiscreteProof
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Integrals of periodic functions over powers of `𝔸_K / K`

Borel structure and normalized Haar measures on `ι → 𝔸_K / K`. A function on `ι → 𝔸_K` that is
invariant under translation by `K^ι` is integrated over the torus through a chosen lift. For
continuous periodic functions this integral is invariant under translations by arbitrary adelic
vectors, under continuous surjective additive maps preserving rational vectors (in particular
rational linear changes of variables and coordinate projections), satisfies Fubini, and depends
continuously on parameters.
-/

noncomputable section

universe u

open MeasureTheory Topology

namespace Langlands.Automorphic.CuspidalWhittaker

open Langlands.Global

section General

variable {G H : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [CompactSpace H] [MeasurableSpace H] [BorelSpace H]

omit [CompactSpace G] in
/-- A continuous surjective additive homomorphism of compact groups carries a Haar probability
measure to the Haar probability measure. -/
theorem map_eq_of_surjective (μ : Measure G) (ν : Measure H)
    [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    (f : G →+ H) (hf : Continuous f) (hs : Function.Surjective f) :
    Measure.map f μ = ν := by
  have : (Measure.map f μ).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map_of_isFiniteMeasure μ f hf hs
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

omit [CompactSpace G] in
/-- Integrals against Haar probability measures are invariant under continuous surjective
additive homomorphisms. -/
theorem integral_comp_surjective (μ : Measure G) (ν : Measure H)
    [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    [SecondCountableTopology H]
    (f : G →+ H) (hf : Continuous f) (hs : Function.Surjective f) {F : H → ℂ}
    (hF : Continuous F) :
    ∫ x, F (f x) ∂μ = ∫ y, F y ∂ν := by
  rw [← map_eq_of_surjective μ ν f hf hs,
    integral_map hf.measurable.aemeasurable hF.aestronglyMeasurable]

omit [CompactSpace G] in
/-- A continuous additive isomorphism of compact groups carries a Haar probability measure
to the Haar probability measure. -/
theorem measurePreserving_continuousAddEquiv (μ : Measure G) (ν : Measure H)
    [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    (e : G ≃ₜ+ H) : MeasurePreserving e μ ν := by
  refine ⟨e.continuous.measurable, ?_⟩
  have : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

end General

section Parametric

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]

omit [SecondCountableTopology Y] in
/-- Integrals over a compact space of a jointly continuous function depend continuously on the
parameter. -/
theorem continuous_integral_of_continuous_uncurry (μ : Measure Y) [IsFiniteMeasure μ]
    {F : X → Y → ℂ} (hF : Continuous (Function.uncurry F)) :
    Continuous fun x => ∫ y, F x y ∂μ := by
  let Φ : C(X, C(Y, ℂ)) := ContinuousMap.curry ⟨Function.uncurry F, hF⟩
  have hint : ∀ p : C(Y, ℂ), Integrable p μ := fun p =>
    p.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let L : C(Y, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun p => ∫ y, p y ∂μ
      map_add' := fun p q => integral_add (hint p) (hint q)
      map_smul' := fun c p => integral_smul c p }
  let Lc : C(Y, ℂ) →L[ℂ] ℂ := L.mkContinuous (μ.real Set.univ) fun p => by
    calc ‖L p‖ ≤ ‖p‖ * μ.real Set.univ :=
          norm_integral_le_of_norm_le_const (ae_of_all _ fun y => p.norm_coe_le_norm y)
      _ = μ.real Set.univ * ‖p‖ := mul_comm _ _
  exact Lc.continuous.comp Φ.continuous

end Parametric

variable (K : Type u) [Field K] [NumberField K]

/-- The Borel σ-algebra of `𝔸_K / K`, the one used by the published constant terms. -/
scoped instance quotientMeasurableSpace : MeasurableSpace (AdeleQuotient K) := borel _

scoped instance quotient_borelSpace : BorelSpace (AdeleQuotient K) := ⟨rfl⟩

scoped instance quotient_secondCountableTopology :
    SecondCountableTopology (AdeleQuotient K) := by
  have := adeles_secondCountableTopology K
  infer_instance

scoped instance quotient_t2Space : T2Space (AdeleQuotient K) := by
  have : IsClosed (principalAdeles K : Set (Adeles K)) := principalAdeles_isClosed K
  infer_instance

/-! ### Reduction, lifts and periodic functions -/

section Periodic

variable {K} {ι κ : Type*}

/-- Coordinatewise reduction modulo `K`. -/
def torusMk (y : ι → Adeles K) : ι → AdeleQuotient K := fun i => adeleQuotientMap K (y i)

/-- A chosen coordinatewise lift. -/
def torusLift (t : ι → AdeleQuotient K) : ι → Adeles K := fun i =>
  Function.surjInv (QuotientAddGroup.mk_surjective (s := principalAdeles K)) (t i)

/-- Rational vectors in `𝔸_K^ι`. -/
def ratVec (k : ι → K) : ι → Adeles K := fun i => algebraMap K (Adeles K) (k i)

@[simp] theorem ratVec_apply (k : ι → K) (i : ι) :
    ratVec k i = algebraMap K (Adeles K) (k i) := rfl

theorem ratVec_add (k l : ι → K) : ratVec (k + l) = ratVec k + ratVec l := by
  funext i
  simp [ratVec]

theorem ratVec_neg (k : ι → K) : ratVec (-k) = -ratVec k := by
  funext i
  simp [ratVec]

theorem ratVec_zero : ratVec (0 : ι → K) = 0 := by
  funext i
  simp [ratVec]

@[simp] theorem torusMk_torusLift (t : ι → AdeleQuotient K) : torusMk (torusLift t) = t := by
  funext i
  exact Function.surjInv_eq (QuotientAddGroup.mk_surjective (s := principalAdeles K)) (t i)

theorem torusMk_add (y z : ι → Adeles K) : torusMk (y + z) = torusMk y + torusMk z := by
  funext i
  exact map_add (adeleQuotientMap K) (y i) (z i)

theorem torusMk_ratVec (k : ι → K) : torusMk (ratVec k) = 0 := by
  funext i
  exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨k i, rfl⟩

theorem torusMk_add_ratVec (y : ι → Adeles K) (k : ι → K) :
    torusMk (y + ratVec k) = torusMk y := by
  rw [torusMk_add, torusMk_ratVec, add_zero]

theorem exists_eq_add_ratVec_of_torusMk_eq {y z : ι → Adeles K}
    (h : torusMk y = torusMk z) : ∃ k : ι → K, z = y + ratVec k := by
  have hmem : ∀ i, -y i + z i ∈ principalAdeles K := fun i =>
    QuotientAddGroup.eq.mp (congrFun h i)
  choose k hk using hmem
  refine ⟨k, funext fun i => ?_⟩
  change z i = y i + algebraMap K (Adeles K) (k i)
  rw [show algebraMap K (Adeles K) (k i) = -y i + z i from hk i]
  abel

theorem torusMk_surjective : Function.Surjective (torusMk (K := K) (ι := ι)) :=
  fun t => ⟨torusLift t, torusMk_torusLift t⟩

theorem exists_torusLift_torusMk (y : ι → Adeles K) :
    ∃ k : ι → K, torusLift (torusMk y) = y + ratVec k :=
  exists_eq_add_ratVec_of_torusMk_eq (torusMk_torusLift (torusMk y)).symm

theorem isOpenQuotientMap_torusMk [Finite ι] :
    IsOpenQuotientMap (torusMk (K := K) (ι := ι)) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

theorem continuous_torusMk : Continuous (torusMk (K := K) (ι := ι)) :=
  continuous_pi fun i => (adeleQuotientMap K).continuous.comp (continuous_apply i)

/-- The additive homomorphism `torusMk`. -/
def torusMkHom : (ι → Adeles K) →+ (ι → AdeleQuotient K) where
  toFun := torusMk
  map_zero' := by
    have := torusMk_ratVec (K := K) (0 : ι → K)
    rwa [ratVec_zero] at this
  map_add' := torusMk_add

/-- Periodicity under `K^ι`. -/
def IsPeriodic (f : (ι → Adeles K) → ℂ) : Prop :=
  ∀ (y : ι → Adeles K) (k : ι → K), f (y + ratVec k) = f y

theorem IsPeriodic.lift_mk {f : (ι → Adeles K) → ℂ} (hf : IsPeriodic f) (y : ι → Adeles K) :
    f (torusLift (torusMk y)) = f y := by
  obtain ⟨k, hk⟩ := exists_torusLift_torusMk y
  rw [hk, hf]

theorem IsPeriodic.eq_of_torusMk_eq {f : (ι → Adeles K) → ℂ} (hf : IsPeriodic f)
    {y z : ι → Adeles K} (h : torusMk y = torusMk z) : f y = f z := by
  rw [← hf.lift_mk y, h, hf.lift_mk z]

theorem IsPeriodic.continuous_lift [Finite ι] {f : (ι → Adeles K) → ℂ} (hf : IsPeriodic f)
    (hc : Continuous f) : Continuous (f ∘ torusLift) := by
  rw [(isOpenQuotientMap_torusMk (K := K) (ι := ι)).isQuotientMap.continuous_iff]
  convert hc using 1
  funext y
  exact hf.lift_mk y

theorem IsPeriodic.add {f g : (ι → Adeles K) → ℂ} (hf : IsPeriodic f) (hg : IsPeriodic g) :
    IsPeriodic (fun y => f y + g y) := fun y k => by
  beta_reduce
  rw [hf, hg]

theorem IsPeriodic.mul {f g : (ι → Adeles K) → ℂ} (hf : IsPeriodic f) (hg : IsPeriodic g) :
    IsPeriodic (fun y => f y * g y) := fun y k => by
  beta_reduce
  rw [hf, hg]

theorem IsPeriodic.const_mul {f : (ι → Adeles K) → ℂ} (hf : IsPeriodic f) (c : ℂ) :
    IsPeriodic (fun y => c * f y) := fun y k => by
  beta_reduce
  rw [hf]

theorem IsPeriodic.comp_add {f : (ι → Adeles K) → ℂ} (hf : IsPeriodic f) (a : ι → Adeles K) :
    IsPeriodic (fun y => f (y + a)) := fun y k => by
  beta_reduce
  rw [add_right_comm, hf]

theorem isPeriodic_const (c : ℂ) : IsPeriodic (fun _ : ι → Adeles K => c) := fun _ _ => rfl

/-- Additive maps carrying rational vectors to rational vectors. -/
def PreservesRational (φ : (ι → Adeles K) →+ (κ → Adeles K)) : Prop :=
  ∀ k : ι → K, ∃ k' : κ → K, φ (ratVec k) = ratVec k'

theorem IsPeriodic.comp {f : (κ → Adeles K) → ℂ} (hf : IsPeriodic f)
    {φ : (ι → Adeles K) →+ (κ → Adeles K)} (hφ : PreservesRational φ) :
    IsPeriodic (fun y => f (φ y)) := fun y k => by
  beta_reduce
  obtain ⟨k', hk'⟩ := hφ k
  rw [map_add, hk', hf]

theorem PreservesRational.torusMk_eq {φ : (ι → Adeles K) →+ (κ → Adeles K)}
    (hφ : PreservesRational φ) {y z : ι → Adeles K} (h : torusMk y = torusMk z) :
    torusMk (φ y) = torusMk (φ z) := by
  obtain ⟨k, rfl⟩ := exists_eq_add_ratVec_of_torusMk_eq h
  obtain ⟨k', hk'⟩ := hφ k
  rw [map_add, hk', torusMk_add_ratVec]

/-- The map induced on tori by an additive map preserving rational vectors. -/
def torusMap {φ : (ι → Adeles K) →+ (κ → Adeles K)} (hφ : PreservesRational φ) :
    (ι → AdeleQuotient K) →+ (κ → AdeleQuotient K) where
  toFun t := torusMk (φ (torusLift t))
  map_zero' := by
    have h : torusMk (torusLift (0 : ι → AdeleQuotient K)) = torusMk (0 : ι → Adeles K) := by
      rw [torusMk_torusLift]
      exact (map_zero (torusMkHom (K := K) (ι := ι))).symm
    rw [hφ.torusMk_eq h, map_zero]
    exact map_zero (torusMkHom (K := K) (ι := κ))
  map_add' s t := by
    have h : torusMk (torusLift (s + t)) = torusMk (torusLift s + torusLift t) := by
      rw [torusMk_add, torusMk_torusLift, torusMk_torusLift, torusMk_torusLift]
    rw [hφ.torusMk_eq h, map_add, torusMk_add]

theorem torusMap_torusMk {φ : (ι → Adeles K) →+ (κ → Adeles K)} (hφ : PreservesRational φ)
    (y : ι → Adeles K) : torusMap hφ (torusMk y) = torusMk (φ y) :=
  hφ.torusMk_eq (torusMk_torusLift (torusMk y))

theorem continuous_torusMap [Finite ι] {φ : (ι → Adeles K) →+ (κ → Adeles K)}
    (hφ : PreservesRational φ) (hc : Continuous φ) : Continuous (torusMap hφ) := by
  rw [(isOpenQuotientMap_torusMk (K := K) (ι := ι)).isQuotientMap.continuous_iff]
  have : (torusMap hφ ∘ torusMk) = torusMk ∘ φ := funext fun y => torusMap_torusMk hφ y
  rw [this]
  exact continuous_torusMk.comp hc

theorem torusMap_surjective {φ : (ι → Adeles K) →+ (κ → Adeles K)} (hφ : PreservesRational φ)
    (hs : Function.Surjective φ) : Function.Surjective (torusMap hφ) := by
  intro t
  obtain ⟨y, hy⟩ := hs (torusLift t)
  exact ⟨torusMk y, by rw [torusMap_torusMk, hy, torusMk_torusLift]⟩

end Periodic

variable [CompactSpace (AdeleQuotient K)]

/-- The normalized Haar probability measure on `ι → 𝔸_K / K`, a product of copies of the
published `adeleQuotientHaar`. -/
def torusHaar (ι : Type*) [Fintype ι] : Measure (ι → AdeleQuotient K) :=
  Measure.pi fun _ => adeleQuotientHaar K

variable {K}

instance quotientHaar_isAddHaarMeasure : (adeleQuotientHaar K).IsAddHaarMeasure :=
  adeleQuotientHaar_isAddHaarMeasure K

instance torusHaar_isAddHaarMeasure (ι : Type*) [Fintype ι] :
    (torusHaar K ι).IsAddHaarMeasure := by
  unfold torusHaar
  infer_instance

instance torusHaar_isProbabilityMeasure (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (torusHaar K ι) := by
  unfold torusHaar
  infer_instance

/-- Continuous functions on a torus are integrable. -/
theorem integrable_of_continuous {ι : Type*} [Fintype ι] {f : (ι → AdeleQuotient K) → ℂ}
    (hf : Continuous f) : Integrable f (torusHaar K ι) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ### Torus integrals -/

section Integral

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

variable (ι) in
/-- The integral over `(𝔸_K / K)^ι` of a function on `𝔸_K^ι`, through the chosen lift; for a
periodic function it is the integral of the induced function on the torus. -/
def torusIntegral (f : (ι → Adeles K) → ℂ) : ℂ :=
  ∫ t, f (torusLift t) ∂torusHaar K ι

theorem torusIntegral_congr {f g : (ι → Adeles K) → ℂ} (h : ∀ y, f y = g y) :
    torusIntegral ι f = torusIntegral ι g := by
  rw [funext h]

/-- Translation invariance, for an arbitrary adelic translation. -/
theorem torusIntegral_add_right {f : (ι → Adeles K) → ℂ} (hf : IsPeriodic f)
    (a : ι → Adeles K) :
    torusIntegral ι (fun y => f (y + a)) = torusIntegral ι f := by
  unfold torusIntegral
  have h : ∀ t, f (torusLift t + a) = f (torusLift (t + torusMk a)) := fun t =>
    hf.eq_of_torusMk_eq (by rw [torusMk_add, torusMk_torusLift, torusMk_torusLift])
  simp_rw [h]
  exact integral_add_right_eq_self (fun t => f (torusLift t)) (torusMk a)

/-- Invariance under continuous surjective additive maps preserving rational vectors. -/
theorem torusIntegral_comp {f : (κ → Adeles K) → ℂ} (hf : IsPeriodic f) (hc : Continuous f)
    {φ : (ι → Adeles K) →+ (κ → Adeles K)} (hφ : PreservesRational φ) (hφc : Continuous φ)
    (hs : Function.Surjective φ) :
    torusIntegral ι (fun y => f (φ y)) = torusIntegral κ f := by
  unfold torusIntegral
  have h : ∀ t, f (φ (torusLift t)) = (f ∘ torusLift) (torusMap hφ t) := fun t => by
    change _ = f (torusLift (torusMk (φ (torusLift t))))
    rw [hf.lift_mk]
  simp_rw [h]
  exact integral_comp_surjective (torusHaar K ι) (torusHaar K κ) (torusMap hφ)
    (continuous_torusMap hφ hφc) (torusMap_surjective hφ hs) (hf.continuous_lift hc)

theorem torusIntegral_const (c : ℂ) : torusIntegral (K := K) ι (fun _ => c) = c := by
  simp [torusIntegral]

theorem torusIntegral_const_mul (c : ℂ) (f : (ι → Adeles K) → ℂ) :
    torusIntegral ι (fun y => c * f y) = c * torusIntegral ι f :=
  integral_const_mul c _

theorem torusIntegral_mul_const (c : ℂ) (f : (ι → Adeles K) → ℂ) :
    torusIntegral ι (fun y => f y * c) = torusIntegral ι f * c :=
  integral_mul_const c _

theorem torusIntegral_add {f g : (ι → Adeles K) → ℂ} (hf : IsPeriodic f) (hfc : Continuous f)
    (hg : IsPeriodic g) (hgc : Continuous g) :
    torusIntegral ι (fun y => f y + g y) = torusIntegral ι f + torusIntegral ι g :=
  integral_add (integrable_of_continuous (hf.continuous_lift hfc))
    (integrable_of_continuous (hg.continuous_lift hgc))

theorem torusIntegral_sub {f g : (ι → Adeles K) → ℂ} (hf : IsPeriodic f) (hfc : Continuous f)
    (hg : IsPeriodic g) (hgc : Continuous g) :
    torusIntegral ι (fun y => f y - g y) = torusIntegral ι f - torusIntegral ι g :=
  integral_sub (integrable_of_continuous (hf.continuous_lift hfc))
    (integrable_of_continuous (hg.continuous_lift hgc))

omit [CompactSpace (AdeleQuotient K)] in
theorem continuous_torusLift_prod {F : (ι → Adeles K) × (κ → Adeles K) → ℂ}
    (hF : Continuous F) (hp : ∀ y z k l, F (y + ratVec k, z + ratVec l) = F (y, z)) :
    Continuous fun p : (ι → AdeleQuotient K) × (κ → AdeleQuotient K) =>
      F (torusLift p.1, torusLift p.2) := by
  have hq : IsOpenQuotientMap (Prod.map (torusMk (K := K) (ι := ι)) (torusMk (K := K) (ι := κ))) :=
    isOpenQuotientMap_torusMk.prodMap isOpenQuotientMap_torusMk
  rw [hq.isQuotientMap.continuous_iff]
  convert hF using 1
  funext p
  obtain ⟨k, hk⟩ := exists_torusLift_torusMk (K := K) p.1
  obtain ⟨l, hl⟩ := exists_torusLift_torusMk (K := K) p.2
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
  rw [hk, hl, hp]

/-- **Fubini** for jointly continuous, separately periodic functions. -/
theorem torusIntegral_comm {F : (ι → Adeles K) → (κ → Adeles K) → ℂ}
    (hF : Continuous (Function.uncurry F))
    (hp : ∀ y z k l, F (y + ratVec k) (z + ratVec l) = F y z) :
    torusIntegral ι (fun y => torusIntegral κ (F y)) =
      torusIntegral κ (fun z => torusIntegral ι (fun y => F y z)) := by
  unfold torusIntegral
  refine integral_integral_swap ?_
  exact (continuous_torusLift_prod (F := Function.uncurry F) hF
    (fun y z k l => hp y z k l)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Continuity in a parameter. -/
theorem continuous_torusIntegral {X : Type*} [TopologicalSpace X]
    {F : X → (ι → Adeles K) → ℂ} (hF : Continuous (Function.uncurry F))
    (hp : ∀ x, IsPeriodic (F x)) :
    Continuous fun x => torusIntegral ι (F x) := by
  unfold torusIntegral
  refine continuous_integral_of_continuous_uncurry (torusHaar K ι) ?_
  have hq : IsOpenQuotientMap (Prod.map (id : X → X) (torusMk (K := K) (ι := ι))) :=
    IsOpenQuotientMap.id.prodMap isOpenQuotientMap_torusMk
  rw [hq.isQuotientMap.continuous_iff]
  convert hF using 1
  funext p
  exact (hp p.1).lift_mk p.2

end Integral

end Langlands.Automorphic.CuspidalWhittaker
