import Langlands.Representation.RankinSelberg.RankOneMatrixUnipotentIntegral
import Langlands.HarmonicAnalysis.ScalarFourierClosureProof
import Langlands.HarmonicAnalysis.RectangularFourier
import Langlands.Representation.Hecke.TestFunction

/-! Compact families of actual inverse corner Fourier transforms. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg.RankOneIwasawa

open MeasureTheory Topology GeneralLinear HarmonicAnalysis

universe uF uX uY

/-- A locally constant family of Schwartz functions becomes a joint Schwartz
function after a compact clopen parameter cutoff. -/
theorem exists_schwartzFamily_kernel
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    (g : X → SchwartzBruhat Y) (hg : IsLocallyConstant g)
    {C : Set X} (hC : IsCompact C) (hCl : IsClopen C) :
    ∃ K : SchwartzBruhat (X × Y), ∀ x y,
      K (x, y) = C.indicator (fun x => g x y) x := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hf := (hg.comp_continuous
    (continuous_subtype_val : Continuous (Subtype.val : C → X))).range_finite
  let S := Set.range (fun x : C => g x)
  let D := ⋃ f ∈ S, tsupport (f : Y → ℂ)
  have hD : IsCompact D := hf.isCompact_biUnion (fun f _ => f.hasCompactSupport)
  have hCD : ∀ x ∈ C, tsupport (g x : Y → ℂ) ⊆ D := by
    intro x hx y hy
    exact Set.mem_iUnion₂.mpr ⟨_, ⟨⟨x, hx⟩, rfl⟩, hy⟩
  have hgj : IsLocallyConstant (fun z : X × Y => g z.1 z.2) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    have hh := hg.eventually_eq z.1
    have hv := (g z.1).locallyConstant.eventually_eq z.2
    filter_upwards [continuous_fst.continuousAt.eventually hh,
      continuous_snd.continuousAt.eventually hv] with z' hh' hv'
    rw [hh']
    exact hv'
  let c : SchwartzBruhat X := Hecke.TestFunction.characteristic hCl hC
  let k : X × Y → ℂ := fun z => c z.1 * g z.1 z.2
  have hk : IsLocallyConstant k :=
    (c.locallyConstant.comp_continuous continuous_fst).mul hgj
  have hc : HasCompactSupport k := by
    apply HasCompactSupport.intro (hC.prod hD)
    intro z hz
    by_cases hx : z.1 ∈ C
    · have hv : z.2 ∉ D := fun hv => hz ⟨hx, hv⟩
      have hsup : z.2 ∉ tsupport (g z.1 : Y → ℂ) := fun hs => hv (hCD z.1 hx hs)
      simp only [k, image_eq_zero_of_notMem_tsupport hsup, mul_zero]
    · simp only [k, c, Hecke.TestFunction.characteristic_apply,
        Set.indicator_of_notMem hx, zero_mul]
  refine ⟨⟨k, hk, hc⟩, fun x y => ?_⟩
  change c x * _ = _
  rw [show c x = C.indicator (fun _ => (1 : ℂ)) x by rfl]
  by_cases hx : x ∈ C <;> simp [hx]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance cornerFourierTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance cornerFourierValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance cornerFourierLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance cornerFourierT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance cornerFourierTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance cornerFourierMeasurable : MeasurableSpace F.Carrier := borel _
local instance cornerFourierBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance cornerFourierNMeasurable (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance cornerFourierNBorel (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier) (n : ℕ)
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))

/-- The actual scalar corner family, with the remaining diagonal entries one. -/
def cornerFamily (h : Langlands.GeneralLinear (n + 1) F.Carrier)
    (t : F.Carrier) : ℂ :=
  unipotentTransform F ψ Φ (Matrix.diagonal (Fin.cons t (fun _ => 1)) * h.val)

theorem exists_cornerFamilyTest (h : Langlands.GeneralLinear (n + 1) F.Carrier) :
    ∃ f : SchwartzBruhat F.Carrier, ∀ t, f t = cornerFamily F ψ n Φ h t := by
  let Φh := rectangularTranslate h Φ
  obtain ⟨f, hf⟩ := exists_cornerSchwartz F ψ Φh (fun _ => 1)
    (k := 1) (one_mem _)
  refine ⟨f, fun t => ?_⟩
  rw [hf]
  simp only [Units.val_one, Matrix.mul_one]
  simp only [cornerFamily, unipotentTransform, Φh, rectangularTranslate_apply,
    Matrix.mul_assoc]

/-- The actual corner family bundled in scalar Schwartz space. -/
def cornerFamilyTest (h : Langlands.GeneralLinear (n + 1) F.Carrier) :
    SchwartzBruhat F.Carrier :=
  Classical.choose (exists_cornerFamilyTest F ψ n Φ h)

theorem cornerFamilyTest_apply (h : Langlands.GeneralLinear (n + 1) F.Carrier)
    (t : F.Carrier) :
    cornerFamilyTest F ψ n Φ h t = cornerFamily F ψ n Φ h t :=
  Classical.choose_spec (exists_cornerFamilyTest F ψ n Φ h) t

theorem cornerFamilyTest_mul_right
    (h κ : Langlands.GeneralLinear (n + 1) F.Carrier)
    (hκ : ∀ X, Φ (X * κ.val) = Φ X) :
    cornerFamilyTest F ψ n Φ (h * κ) = cornerFamilyTest F ψ n Φ h := by
  apply Hecke.TestFunction.ext
  intro t
  simp only [cornerFamilyTest_apply, cornerFamily, Units.val_mul, ← Matrix.mul_assoc]
  exact unipotentTransform_mul_right F ψ Φ κ.val hκ _

/-- Right smoothness is uniform in the scalar corner variable. -/
theorem cornerFamilyTest_locallyConstant :
    IsLocallyConstant (cornerFamilyTest F ψ n Φ) := by
  obtain ⟨m, hm⟩ := exists_schwartz_congruence F Φ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro h
  have hV : {g : Langlands.GeneralLinear (n + 1) F.Carrier |
      h⁻¹ * g ∈ congruenceGroup F n m} ∈ 𝓝 h :=
    ((isOpen_congruenceGroup F n m).preimage
      (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hV] with g hg
  simpa only [mul_inv_cancel_left] using
    cornerFamilyTest_mul_right F ψ n Φ h (h⁻¹ * g) (hm m le_rfl _ hg)

variable (ν : AdditiveHaarMeasure F.Carrier) (hsd : IsSelfDual ψ ν)

/-- A scalar inverse Fourier test for any scalar Schwartz function. -/
def scalarCoFourierTest (f : SchwartzBruhat F.Carrier) : SchwartzBruhat F.Carrier :=
  Classical.choose ((scalarFourierClosure F.Carrier ψ ν hsd).2
    (Hecke.TestFunction.pullback (Homeomorph.neg F.Carrier) f))

theorem scalarCoFourierTest_apply (f : SchwartzBruhat F.Carrier) (v : F.Carrier) :
    scalarCoFourierTest F ψ ν hsd f v =
      fourierIntegral ψ ν (Hecke.TestFunction.pullback (Homeomorph.neg F.Carrier) f) v :=
  Classical.choose_spec ((scalarFourierClosure F.Carrier ψ ν hsd).2
    (Hecke.TestFunction.pullback (Homeomorph.neg F.Carrier) f)) v

/-- The supplied scalar self-duality reconstructs the original test with a plus phase. -/
theorem integral_scalarCoFourierTest (f : SchwartzBruhat F.Carrier) (t : F.Carrier) :
    (∫ v, ψ.complex (t * v) * scalarCoFourierTest F ψ ν hsd f v ∂ν.measure) = f t := by
  have he := (hsd (Hecke.TestFunction.pullback (Homeomorph.neg F.Carrier) f)).2 t
  have hneg (x : F.Carrier) : (Homeomorph.neg F.Carrier) x = -x := rfl
  simpa only [fourierIntegral, fourierTransform, LinearMap.coe_mk, AddHom.coe_mk,
    scalarCoFourierTest_apply, Hecke.TestFunction.pullback_apply,
    hneg, neg_neg, mul_comm t] using he

/-- The corner inverse Fourier transform, with the unchanged supplied measure. -/
def cornerCoFourierTest (h : Langlands.GeneralLinear (n + 1) F.Carrier) :
    SchwartzBruhat F.Carrier :=
  scalarCoFourierTest F ψ ν hsd (cornerFamilyTest F ψ n Φ h)

theorem integral_cornerCoFourierTest
    (h : Langlands.GeneralLinear (n + 1) F.Carrier) (t : F.Carrier) :
    (∫ v, ψ.complex (t * v) * cornerCoFourierTest F ψ n Φ ν hsd h v ∂ν.measure) =
      cornerFamily F ψ n Φ h t := by
  rw [cornerCoFourierTest, integral_scalarCoFourierTest, cornerFamilyTest_apply]

theorem cornerCoFourierTest_locallyConstant :
    IsLocallyConstant (cornerCoFourierTest F ψ n Φ ν hsd) :=
  (cornerFamilyTest_locallyConstant F ψ n Φ).comp (scalarCoFourierTest F ψ ν hsd)

/-- The inverse corner Fourier transforms over a compact family have one
common compact scalar support. -/
theorem exists_compact_cornerCoFourier_support
    {C : Set (Langlands.GeneralLinear (n + 1) F.Carrier)} (hC : IsCompact C) :
    ∃ D : Set F.Carrier, IsCompact D ∧ ∀ h ∈ C,
      tsupport (cornerCoFourierTest F ψ n Φ ν hsd h : _ → ℂ) ⊆ D := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hf := ((cornerCoFourierTest_locallyConstant F ψ n Φ ν hsd).comp_continuous
    (continuous_subtype_val : Continuous (Subtype.val : C → _))).range_finite
  let S := Set.range (fun h : C => cornerCoFourierTest F ψ n Φ ν hsd h)
  refine ⟨⋃ f ∈ S, tsupport (f : F.Carrier → ℂ),
    hf.isCompact_biUnion (fun f _ => f.hasCompactSupport), ?_⟩
  intro h hh v hv
  exact Set.mem_iUnion₂.mpr ⟨_, ⟨⟨h, hh⟩, rfl⟩, hv⟩

/-- Joint local constancy of the compactly parameterized inverse Fourier kernel. -/
theorem cornerCoFourier_joint_locallyConstant :
    IsLocallyConstant (fun z : Langlands.GeneralLinear (n + 1) F.Carrier × F.Carrier =>
      cornerCoFourierTest F ψ n Φ ν hsd z.1 z.2) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  have hh := (cornerCoFourierTest_locallyConstant F ψ n Φ ν hsd).eventually_eq z.1
  have hv := (cornerCoFourierTest F ψ n Φ ν hsd z.1).locallyConstant.eventually_eq z.2
  filter_upwards [continuous_fst.continuousAt.eventually hh,
    continuous_snd.continuousAt.eventually hv] with z' hh' hv'
  rw [hh']
  exact hv'

/-- A compact clopen cutoff in any continuous parameter family gives an actual
joint Schwartz kernel, rather than merely separate scalar transforms. -/
theorem exists_compact_cornerCoFourier_kernel
    {X : Type uX} [TopologicalSpace X] [T2Space X]
    (ρ : X → Langlands.GeneralLinear (n + 1) F.Carrier) (hρ : Continuous ρ)
    {C : Set X} (hC : IsCompact C) (hCl : IsClopen C) :
    ∃ K : SchwartzBruhat (X × F.Carrier), ∀ x v,
      K (x, v) = C.indicator (fun x => cornerCoFourierTest F ψ n Φ ν hsd (ρ x) v) x := by
  exact exists_schwartzFamily_kernel
    (fun x => cornerCoFourierTest F ψ n Φ ν hsd (ρ x))
    ((cornerCoFourierTest_locallyConstant F ψ n Φ ν hsd).comp_continuous hρ) hC hCl

end Langlands.RankinSelberg.RankOneIwasawa
