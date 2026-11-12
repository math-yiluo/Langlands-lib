import Langlands.Global.ArchimedeanCompactReproduction
import Langlands.Automorphic.CuspidalL2.SiegelCover

/-! # One compactly supported kernel reproducing a realized vector at every adelic point -/

noncomputable section
universe u
set_option autoImplicit false

open MeasureTheory Filter Topology TopologicalSpace NumberField

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions CompactKernelAverage

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}
variable [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
variable (μ : Measure (InfiniteAdelicGL K n)) [μ.IsHaarMeasure]

/-- **Simultaneous approximation.** One compact-central kernel smooths each member of a
finite family of vectors into a prescribed neighborhood of that vector. -/
theorem exists_centralKernel_forall_mem {ι : Type*} [Finite ι]
    (f : ι → DerivativeSmoothFunctions K n) (V : ι → Set (DerivativeSmoothFunctions K n))
    (hV : ∀ j, V j ∈ 𝓝 (f j)) :
    ∃ κ : compactCentralKernels K n, ∀ j, smoothingLM μ κ.val (f j) ∈ V j := by
  choose W₀ hW₀ happ using fun j =>
    CompactIndexAverage.exists_average_neighborhood (f j) (V j) (hV j)
  let W := (fun g : InfiniteAdelicGL K n => g⁻¹) ⁻¹' ⋂ j, W₀ j
  have hW : W ∈ 𝓝 (1 : InfiniteAdelicGL K n) := by
    have hc : ContinuousAt (fun g : InfiniteAdelicGL K n => g⁻¹)
        (1 : InfiniteAdelicGL K n) := continuous_inv.continuousAt
    exact hc.preimage_mem_nhds (by simpa only [inv_one] using Filter.iInter_mem.mpr hW₀)
  obtain ⟨T, hT, _, _, hsat⟩ := compactConjugationNeighborhood K n W hW
  obtain ⟨κ, hκsupport, hκnonneg, _, hκint⟩ := normalizedCompactKernel K n μ T hT
  let : MeasurableSpace (standardInfiniteCompact K n) :=
    borel (standardInfiniteCompact K n)
  let : BorelSpace (standardInfiniteCompact K n) := ⟨rfl⟩
  let ν : Measure (standardInfiniteCompact K n) :=
    Measure.haarMeasure (⊤ : PositiveCompacts (standardInfiniteCompact K n))
  let : ν.IsHaarMeasure := by
    dsimp [ν]
    infer_instance
  let : IsProbabilityMeasure ν := ⟨by
    change Measure.haarMeasure
      (⊤ : PositiveCompacts (standardInfiniteCompact K n)) Set.univ = 1
    simpa only [PositiveCompacts.coe_top] using
      (Measure.haarMeasure_self
        (K₀ := (⊤ : PositiveCompacts (standardInfiniteCompact K n))))⟩
  obtain ⟨η, _, hηsupport, hηcentral, _, hηnonneg, hηint⟩ :=
    compactKernelConjugationAverage K n μ ν κ
  have hsupport : tsupport η.val.val ⊆ W := by
    intro x hx
    obtain ⟨k, y, hy, hxy⟩ := hηsupport hx
    exact hsat ⟨k, y, hκsupport hy, hxy⟩
  have hnonneg := hηnonneg hκnonneg
  have hint : (∫ x, η.val.val x⁻¹ ∂μ) = 1 := hηint.trans hκint
  refine ⟨⟨η, hηcentral⟩, fun j => ?_⟩
  apply happ j (CompactKernelAverage.inverseSupport η)
      (CompactKernelAverage.inclusion η)
      (CompactKernelAverage.measure μ η) (CompactKernelAverage.weight η)
  · intro i
    have hi := hsupport i.property
    change (i.val⁻¹)⁻¹ ∈ ⋂ j, W₀ j at hi
    change i.val ∈ W₀ j
    rw [inv_inv] at hi
    exact Set.mem_iInter.mp hi j
  · rw [CompactKernelAverage.integral_weight μ η, hint]
  · exact CompactKernelAverage.integral_norm_weight μ η hnonneg hint

/-- **Simultaneous reproduction.** Finitely many compact-finite, center-finite smooth vectors
are reproduced by one compact-central kernel. -/
theorem exists_centralKernel_forall_reproduce {ι : Type*} [Finite ι]
    (f : ι → DerivativeSmoothFunctions K n)
    (hf : ∀ j, Langlands.FiniteVectors.IsFiniteVector (compactAction K n) (f j))
    (hz : ∀ j, IsCenterFinite K n (toSmooth K n (f j))) :
    ∃ κ : compactCentralKernels K n, ∀ j, smoothingLM μ κ.val (f j) = f j := by
  let Φ : compactCentralKernels K n →ₗ[ℂ] (ι → DerivativeSmoothFunctions K n) :=
    LinearMap.pi fun j => centralSmoothingMap μ (f j)
  let ψ : ((j : ι) → LinearMap.range (centralSmoothingMap μ (f j))) →ₗ[ℂ]
      (ι → DerivativeSmoothFunctions K n) :=
    LinearMap.pi fun j => (LinearMap.range (centralSmoothingMap μ (f j))).subtype ∘ₗ
      LinearMap.proj j
  have : ∀ j, Module.Finite ℂ (LinearMap.range (centralSmoothingMap μ (f j))) :=
    fun j => finite_range_centralSmoothingMap μ (f j) (hf j) (hz j)
  have hle : LinearMap.range Φ ≤ LinearMap.range ψ := by
    rintro _ ⟨κ, rfl⟩
    exact ⟨fun j => ⟨centralSmoothingMap μ (f j) κ, κ, rfl⟩, rfl⟩
  have : Module.Finite ℂ (LinearMap.range Φ) := Submodule.finiteDimensional_of_le hle
  have hclosed : IsClosed (LinearMap.range Φ : Set (ι → DerivativeSmoothFunctions K n)) :=
    (LinearMap.range Φ).closed_of_finiteDimensional
  have hmem : f ∈ closure (LinearMap.range Φ : Set (ι → DerivativeSmoothFunctions K n)) := by
    apply mem_closure_iff_nhds.mpr
    intro V hV
    rw [nhds_pi] at hV
    obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.mp hV
    obtain ⟨κ, hκ⟩ := exists_centralKernel_forall_mem μ f t ht
    exact ⟨Φ κ, hsub fun j _ => hκ j, κ, rfl⟩
  rw [hclosed.closure_eq] at hmem
  obtain ⟨κ, hκ⟩ := hmem
  exact ⟨κ, fun j => congrFun hκ j⟩

end Langlands.Global.ArchimedeanGL

namespace Langlands.Automorphic.OperatorRealization

open Langlands.Global Langlands.Automorphic.CuspidalL2 ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)

local instance cuspidalAdmReproAddCommGroupRationalInvariant :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance cuspidalAdmReproAddCommGroupContinuousRational :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance cuspidalAdmReproAddCommGroupFiniteSmoothRational :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance cuspidalAdmReproAddCommGroupAutomorphicForms :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance cuspidalAdmReproAddCommGroupStableAutomorphic :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance cuspidalAdmReproAddCommGroupSpace : AddCommGroup S.Space :=
  Submodule.addCommGroup _

theorem evaluate_toContinuous_zero (x : AdelicGL F n) :
    evaluate F n (S.toContinuous 0) x = 0 := by
  rw [map_zero]
  rfl

theorem evaluate_toContinuous_add (f f' : S.Space) (x : AdelicGL F n) :
    evaluate F n (S.toContinuous (f + f')) x =
      evaluate F n (S.toContinuous f) x + evaluate F n (S.toContinuous f') x := by
  rw [map_add]
  rfl

theorem evaluate_toContinuous_smul (c : ℂ) (f : S.Space) (x : AdelicGL F n) :
    evaluate F n (S.toContinuous (c • f)) x = c * evaluate F n (S.toContinuous f) x := by
  rw [map_smul]
  rfl

variable [MeasurableSpace (InfiniteAdelicGL F n)] (μ : Measure (InfiniteAdelicGL F n))

/-- The archimedean right convolution identity `f(g h) = ∫ f(g z) κ(z⁻¹ h) dμ(z)` of a
realized vector `f` at the adelic point `g`, for all archimedean `h`. -/
def ReproducesAt (κ : InfiniteAdelicGL F n → ℂ) (f : S.Space) (g : AdelicGL F n) : Prop :=
  ∀ h : InfiniteAdelicGL F n, evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n h) =
    ∫ z, evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n z) * κ (z⁻¹ * h) ∂μ

variable {S μ}

theorem ReproducesAt.rational {κ : InfiniteAdelicGL F n → ℂ} {f : S.Space} {g : AdelicGL F n}
    (H : S.ReproducesAt μ κ f g) (γ : RationalGL F n) :
    S.ReproducesAt μ κ f (AdelicGL.rational F n γ * g) := by
  intro h
  simp only [mul_assoc, evaluate_rational]
  exact H h

theorem ReproducesAt.mul_ofFinite {κ : InfiniteAdelicGL F n → ℂ} {f : S.Space}
    {g : AdelicGL F n} (H : S.ReproducesAt μ κ f g) {l : FiniteAdelicGL F n}
    (hl : ∀ x : AdelicGL F n, evaluate F n (S.toContinuous f) (x * AdelicGL.ofFinite F n l) =
      evaluate F n (S.toContinuous f) x) :
    S.ReproducesAt μ κ f (g * AdelicGL.ofFinite F n l) := by
  have e : ∀ z : InfiniteAdelicGL F n,
      evaluate F n (S.toContinuous f) (g * AdelicGL.ofFinite F n l * AdelicGL.ofInfinite F n z) =
        evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n z) := fun z => by
    rw [mul_assoc, ← AdelicGL.ofInfinite_commute, ← mul_assoc, hl]
  intro h
  simp only [e]
  exact H h

theorem ReproducesAt.mul_ofInfinite [BorelSpace (InfiniteAdelicGL F n)] [μ.IsMulLeftInvariant]
    {κ : InfiniteAdelicGL F n → ℂ}
    {f : S.Space} {g : AdelicGL F n} (H : S.ReproducesAt μ κ f g) (a : InfiniteAdelicGL F n) :
    S.ReproducesAt μ κ f (g * AdelicGL.ofInfinite F n a) := by
  intro h
  have e := H (a * h)
  rw [map_mul, ← mul_assoc] at e
  have hsub := integral_mul_left_eq_self (μ := μ)
    (fun z => evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n z) *
      κ (z⁻¹ * (a * h))) a
  rw [e, ← hsub]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [map_mul, mul_assoc, mul_inv_rev, inv_mul_cancel_left]

/-- A slice reproduced by a smooth compact kernel gives the convolution identity at the
corresponding finite adelic point. -/
theorem reproducesAt_ofFinite [BorelSpace (InfiniteAdelicGL F n)] [μ.IsHaarMeasure]
    (κ : ArchimedeanGL.SmoothCompactKernel F n) (f : S.Space) (y : FiniteAdelicGL F n)
    (hκ : ArchimedeanGL.CompactKernelAverage.smoothingLM μ κ
      ((ArchimedeanGL.DerivativeSmoothFunctions.toSmooth F n).symm
        (finiteSmoothSlice F n y (S.ambient f))) =
        (ArchimedeanGL.DerivativeSmoothFunctions.toSmooth F n).symm
          (finiteSmoothSlice F n y (S.ambient f))) :
    S.ReproducesAt μ κ.val.val f (AdelicGL.ofFinite F n y) := by
  intro h
  have e := ArchimedeanGL.CompactKernelAverage.smoothingLM_eq_rawConvolution μ κ
    ((ArchimedeanGL.DerivativeSmoothFunctions.toSmooth F n).symm
      (finiteSmoothSlice F n y (S.ambient f))) h
  rw [hκ, LinearEquiv.apply_symm_apply, ArchimedeanGL.rawConvolution_apply] at e
  have hs : ∀ z : InfiniteAdelicGL F n,
      evaluate F n (S.toContinuous f) (AdelicGL.ofFinite F n y * AdelicGL.ofInfinite F n z) =
        (finiteSmoothSlice F n y (S.ambient f)).val z := fun z => by
    rw [S.finiteSmoothSlice_ambient_apply, AdelicGL.ofInfinite_commute]
  simp only [hs]
  exact e

variable (S μ)

/-- One smooth compactly supported kernel gives the convolution identity at finitely many
finite adelic points. -/
theorem exists_kernel_forall_mem [BorelSpace (InfiniteAdelicGL F n)] [μ.IsHaarMeasure]
    (f : S.Space) (t : Finset (FiniteAdelicGL F n)) :
    ∃ κ : ArchimedeanGL.SmoothCompactKernel F n, ∀ y ∈ t,
      S.ReproducesAt μ κ.val.val f (AdelicGL.ofFinite F n y) := by
  let s : t → ArchimedeanGL.DerivativeSmoothFunctions F n := fun y =>
    (ArchimedeanGL.DerivativeSmoothFunctions.toSmooth F n).symm
      (finiteSmoothSlice F n y.val (S.ambient f))
  have hf : ∀ y : t, Langlands.FiniteVectors.IsFiniteVector
      (ArchimedeanGL.DerivativeSmoothFunctions.compactAction F n) (s y) := fun y =>
    (S.slice_properties f y.val).1.map
      (ArchimedeanGL.DerivativeSmoothFunctions.compactActionEquiv F n).symm.toIntertwiningMap
  have hz : ∀ y : t, ArchimedeanGL.IsCenterFinite F n
      (ArchimedeanGL.DerivativeSmoothFunctions.toSmooth F n (s y)) := fun y => by
    simp only [s, LinearEquiv.apply_symm_apply]
    exact (S.slice_properties f y.val).2.1
  obtain ⟨κ, hκ⟩ := ArchimedeanGL.exists_centralKernel_forall_reproduce μ s hf hz
  exact ⟨κ.val, fun y hy => reproducesAt_ofFinite κ.val f y (hκ ⟨y, hy⟩)⟩

variable {S μ}

/-- The convolution identity at a finite adelic point `y` propagates to every adelic point
whose rational normal form `γ g = a q` has `q` in the level coset of `y`. -/
theorem ReproducesAt.of_decomposition [BorelSpace (InfiniteAdelicGL F n)]
    [μ.IsMulLeftInvariant] {κ : InfiniteAdelicGL F n → ℂ} {f : S.Space}
    {y : FiniteAdelicGL F n} (H : S.ReproducesAt μ κ f (AdelicGL.ofFinite F n y))
    {g q : AdelicGL F n} {γ : RationalGL F n} {a : InfiniteAdelicGL F n}
    (hγ : AdelicGL.rational F n γ * g = AdelicGL.ofInfinite F n a * q)
    (hyq : ∀ x : AdelicGL F n, evaluate F n (S.toContinuous f)
      (x * AdelicGL.ofFinite F n (y⁻¹ * AdelicGL.finite F n q)) =
        evaluate F n (S.toContinuous f) x) :
    S.ReproducesAt μ κ f g := by
  have h1 := H.mul_ofInfinite (a * AdelicGL.infinite F n q)
  rw [← AdelicGL.ofInfinite_commute] at h1
  have h2 := h1.mul_ofFinite hyq
  have hpt : AdelicGL.ofInfinite F n (a * AdelicGL.infinite F n q) *
      AdelicGL.ofFinite F n y * AdelicGL.ofFinite F n (y⁻¹ * AdelicGL.finite F n q) =
        AdelicGL.ofInfinite F n a * q := by
    rw [mul_assoc, ← map_mul (AdelicGL.ofFinite F n), mul_inv_cancel_left, map_mul, mul_assoc,
      ← AdelicGL.eq_ofInfinite_mul_ofFinite]
  rw [hpt, ← hγ] at h2
  have h3 := h2.rational γ⁻¹
  rwa [map_inv, inv_mul_cancel_left] at h3

variable (S μ)

/-- **One kernel for all adelic points.** Every realized vector satisfies the archimedean
convolution identity at every adelic point with one smooth compactly supported kernel. The
finitely many slices at representatives of the level cosets meeting a Siegel compact set are
reproduced simultaneously, and rational left translation, right translation by the level and
left invariance of Haar measure carry the identity to every point. -/
theorem exists_reproducingKernel [BorelSpace (InfiniteAdelicGL F n)] [μ.IsHaarMeasure]
    (f : S.Space) :
    ∃ κ : ArchimedeanGL.SmoothCompactKernel F n, ∀ g, S.ReproducesAt μ κ.val.val f g := by
  obtain ⟨L, hLo, hL⟩ := S.exists_level f
  obtain ⟨Q₁, _, hQ₁, _, hdec⟩ := exists_siegelDecomposition F n
  obtain ⟨t, ht⟩ := exists_finite_level_cover L hLo Q₁ hQ₁
  obtain ⟨κ, hκ⟩ := S.exists_kernel_forall_mem μ f t
  refine ⟨κ, fun g => ?_⟩
  obtain ⟨γ, x, q, hq, hγ, -⟩ := hdec g
  obtain ⟨y, hy, hyq⟩ := ht q hq
  refine (hκ y hy).of_decomposition hγ fun x' => ?_
  simpa only [map_one, Module.End.one_apply] using hL 1 x' _ hyq

theorem integrable_reproduce [BorelSpace (InfiniteAdelicGL F n)] [IsFiniteMeasureOnCompacts μ]
    {κ : InfiniteAdelicGL F n → ℂ} (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (f : S.Space) (g : AdelicGL F n) (h : InfiniteAdelicGL F n) :
    Integrable (fun z => evaluate F n (S.toContinuous f) (g * AdelicGL.ofInfinite F n z) *
      κ (z⁻¹ * h)) μ := by
  have hs : HasCompactSupport (fun z : InfiniteAdelicGL F n => κ (z⁻¹ * h)) :=
    hκc.comp_homeomorph ((Homeomorph.inv (InfiniteAdelicGL F n)).trans (Homeomorph.mulRight h))
  refine Continuous.integrable_of_hasCompactSupport ?_ hs.mul_left
  exact ((continuous_evaluate F n _).comp
    (continuous_const.mul (AdelicGL.ofInfinite F n).continuous)).mul
    (hκ.comp (continuous_inv.mul continuous_const))

variable {S μ}

/-- The convolution identity at `g d` for `f` is the convolution identity at `g` for the
finite translate of `f` by `d`. -/
theorem ReproducesAt.finiteRepresentation {κ : InfiniteAdelicGL F n → ℂ} {f : S.Space}
    {g : AdelicGL F n} {d : FiniteAdelicGL F n}
    (H : S.ReproducesAt μ κ f (g * AdelicGL.ofFinite F n d)) :
    S.ReproducesAt μ κ (S.finiteRepresentation d f) g := by
  have e : ∀ z : InfiniteAdelicGL F n,
      evaluate F n (S.toContinuous (S.finiteRepresentation d f)) (g * AdelicGL.ofInfinite F n z) =
        evaluate F n (S.toContinuous f)
          (g * AdelicGL.ofFinite F n d * AdelicGL.ofInfinite F n z) := fun z => by
    rw [evaluate_finiteRepresentation, mul_assoc, mul_assoc, AdelicGL.ofInfinite_commute]
  intro h
  simp only [e]
  exact H h

variable (S μ)

/-- The realized vectors satisfying the convolution identity with `κ` at every adelic point:
a subrepresentation of the finite adelic action. -/
def reproducing [BorelSpace (InfiniteAdelicGL F n)] [IsFiniteMeasureOnCompacts μ]
    {κ : InfiniteAdelicGL F n → ℂ} (hκ : Continuous κ) (hκc : HasCompactSupport κ) :
    Subrepresentation S.finiteRepresentation where
  toSubmodule :=
    { carrier := {f | ∀ g, S.ReproducesAt μ κ f g}
      zero_mem' := by
        intro g h
        simp only [evaluate_toContinuous_zero, zero_mul, integral_zero]
      add_mem' := by
        intro f f' hf hf' g h
        simp only [evaluate_toContinuous_add, add_mul]
        rw [integral_add (S.integrable_reproduce μ hκ hκc f g h)
          (S.integrable_reproduce μ hκ hκc f' g h), hf g h, hf' g h]
      smul_mem' := by
        intro c f hf g h
        simp only [evaluate_toContinuous_smul, mul_assoc, integral_const_mul]
        rw [hf g h] }
  apply_mem_toSubmodule d f hf g :=
    ReproducesAt.finiteRepresentation (hf (g * AdelicGL.ofFinite F n d))

theorem mem_reproducing [BorelSpace (InfiniteAdelicGL F n)] [IsFiniteMeasureOnCompacts μ]
    {κ : InfiniteAdelicGL F n → ℂ} (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (f : S.Space) :
    f ∈ (reproducing S μ hκ hκc).toSubmodule ↔ ∀ g, S.ReproducesAt μ κ f g :=
  Iff.rfl

end Langlands.Automorphic.OperatorRealization
