import Langlands.Global.AdelicBlockCoefficientSmoothness
import Langlands.Global.AdelicBlockSmoothCompactSlices
import Langlands.Global.ArchimedeanIwasawaChart

/-!
# Smooth archimedean slices of adelic scalar sections

A scalar section with smooth compact slices has smooth full infinite slices
at each fixed finite argument. The local formula uses the actual adelic half
character and the smooth evaluation of the realized Levi coefficients.
-/

noncomputable section

open scoped BigOperators Classical ContDiff Manifold Matrix.Norms.Operator Topology
open Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
set_option synthInstance.maxHeartbeats 85000

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear NumberField
open AdelicBlockParabolic AdelicBlockDeterminantCharacter PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "A" => ArchimedeanMatrix F n
local notation "KI" => standardInfiniteCompact F n
local notation "KF" => FiniteAdelicGL.standardIntegral F n
local notation "e" => archimedeanGLCoordinates F n

private def parabolicOfMatrix (x : A) (hx : IsUnit x) (ht : x.IsUpperTriangular) :
    Infinite F B := by
  let a := (e).symm hx.unit
  refine ⟨a, B.mem_parabolic_of_isUpperTriangular a ?_⟩
  intro i j hij
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (hx.unit.val i j) = 0
  rw [hx.unit_spec, ht hij, map_zero]

omit [NumberField F] in
private theorem parabolicOfMatrix_coordinates (x : A) (hx : IsUnit x)
    (ht : x.IsUpperTriangular) : (e (parabolicOfMatrix F B x hx ht).val).val = x :=
  (congrArg Units.val ((e).apply_symm_apply hx.unit)).trans hx.unit_spec

private def compactOfMatrix (x : A) (hx : x ∈ unitary A) : KI :=
  ⟨(e).symm (Unitary.toUnits ⟨x, hx⟩),
    (ArchimedeanGL.mem_standardInfiniteCompact_iff_mem_unitary F n _).mpr (by
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact hx)⟩

omit [NumberField F] in
private theorem compactOfMatrix_coordinates (x : A) (hx : x ∈ unitary A) :
    compactMatrix F (compactOfMatrix F x hx) = x :=
  congrArg Units.val ((e).apply_symm_apply (Unitary.toUnits ⟨x, hx⟩))

private theorem halfCharacter_pair (a : Infinite F B) (p : Finite F B) :
    (parabolicHalfCharacter F B (AdelicBlockParabolic.pair F B a p) : ℂ) =
      (parabolicHalfCharacter F B (ofFinite F B p) : ℂ) *
        archimedeanHalfExtension F B (e a.val).val := by
  have h : AdelicBlockParabolic.pair F B a p = ofFinite F B p * ofInfinite F B a := by
    apply Subtype.ext
    change AdelicGL.pair F n a.val p.val =
      AdelicGL.pair F n 1 p.val * AdelicGL.pair F n a.val 1
    rw [AdelicGL.pair_mul, one_mul, mul_one]
  rw [h, map_mul, Units.val_mul, archimedeanHalfExtension_parabolic]

/-- Evaluate at paired Iwasawa factors using the fixed finite half character,
the archimedean half character, and the normalized compact slice. -/
theorem scalarSection_pair_mul (f : RealizedSections F B S) (a : Infinite F B)
    (p : Finite F B) (k : KI) (l : KF) :
    f.val (AdelicGL.pair F n (a.val * k.val) (p.val * l.val)) =
      (parabolicHalfCharacter F B (ofFinite F B p) : ℂ) *
        archimedeanHalfExtension F B (e a.val).val *
        normalizedSlice F B f.val (compactPair F k l)
          (leviPair F B (B.leviProjection (InfiniteAdeles F) a)
            (B.leviProjection (FiniteAdeles F) p)) := by
  rw [← AdelicGL.pair_mul]
  change f.val ((AdelicBlockParabolic.pair F B a p).val * (compactPair F k l).val) = _
  rw [scalarSection_apply_mul, halfCharacter_pair, leviProjection_pair]

/-- Use the units chart to express a fixed finite slice in ambient mixed matrices. -/
def infiniteSliceExtension (f : AdelicGL F n → ℂ) (d : FiniteAdelicGL F n)
    (x : A) : ℂ :=
  f (AdelicGL.pair F n ((e).symm ((ArchimedeanGL.unitsChart F n).symm x)) d)

@[simp] theorem infiniteSliceExtension_apply (f : AdelicGL F n → ℂ)
    (d : FiniteAdelicGL F n) (g : ArchimedeanGL F n) :
    infiniteSliceExtension F f d g.val = f (AdelicGL.pair F n ((e).symm g) d) := by
  simp only [infiniteSliceExtension, ArchimedeanGL.unitsChart,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

/-- The fixed finite slice is smooth at every invertible mixed matrix. -/
theorem contDiffAt_infiniteSliceExtension (f : CompactFiniteRealizedSections F B S)
    (hf : HasSmoothCompactSlices F B S f.val.val) (d : FiniteAdelicGL F n)
    (g : ArchimedeanGL F n) :
    ContDiffAt ℝ ∞ (infiniteSliceExtension F f.val.val.val d) g.val := by
  obtain ⟨p', l', hd, hp', hl'⟩ := exists_finite_iwasawa F n d
  let p : Finite F B := ⟨p', B.mem_parabolic_of_isUpperTriangular p' hp'⟩
  let l : KF := ⟨l', hl'⟩
  let m := B.leviProjection (FiniteAdeles F) p
  let δ : ℂ := parabolicHalfCharacter F B (ofFinite F B p)
  obtain ⟨b, k, hb, hk, hfact⟩ := ArchimedeanGL.exists_smoothLocalIwasawa F n g
  obtain ⟨hbTri, hbUnit, hkUnit, _⟩ := hfact.self_of_nhds
  let a₀ := parabolicOfMatrix F B (b g.val) hbUnit hbTri
  let k₀ := compactOfMatrix F (k g.val) hkUnit
  have ha₀ : (e a₀.val).val = b g.val := parabolicOfMatrix_coordinates F B _ _ _
  have hk₀ : compactMatrix F k₀ = k g.val := compactOfMatrix_coordinates F _ _
  obtain ⟨r, c, φ, hφ, hexp⟩ := exists_smoothCompactSlice_expansion F B S f hf k₀ l
  have hδ : ContDiffAt ℝ ∞ (fun x => archimedeanHalfExtension F B (b x)) g.val := by
    have h := contDiffAt_archimedeanHalfExtension F B a₀
    rw [ha₀] at h
    exact h.comp _ hb
  have hsum : ContDiffAt ℝ ∞
      (fun x => ∑ j, φ j (k x) * coefficientExtension F B S m (c j) (b x)) g.val := by
    have h (j : Fin r) : ContDiffAt ℝ ∞
        (fun x => φ j (k x) * coefficientExtension F B S m (c j) (b x)) g.val := by
      have hφj := hφ j
      have hcj := coefficientExtension_contDiffAt F B S m a₀ (c j)
      rw [hk₀] at hφj
      rw [ha₀] at hcj
      exact (hφj.comp _ hk).mul (hcj.comp _ hb)
    simpa only [Finset.sum_apply] using
      (ContDiffAt.sum (s := Finset.univ) (fun j _ => h j))
  have hNear := hk.continuousAt
  rw [ContinuousAt, ← hk₀] at hNear
  refine ((contDiffAt_const (c := δ)).mul hδ |>.mul hsum).congr_of_eventuallyEq ?_
  filter_upwards [hfact, hNear.eventually hexp] with x hx he
  let a := parabolicOfMatrix F B (b x) hx.2.1 hx.1
  let q := compactOfMatrix F (k x) hx.2.2.1
  have hab : (e a.val).val = b x := parabolicOfMatrix_coordinates F B _ _ _
  have hqk : compactMatrix F q = k x := compactOfMatrix_coordinates F _ _
  have hax : (e (a.val * q.val)).val = x := by
    rw [map_mul, Units.val_mul, hab]
    change b x * compactMatrix F q = x
    rw [hqk, hx.2.2.2]
  have hvalue : infiniteSliceExtension F f.val.val.val d x =
      f.val.val.val (AdelicGL.pair F n (a.val * q.val) (p.val * l.val)) := by
    rw [← hax, infiniteSliceExtension_apply, ContinuousMulEquiv.symm_apply_apply]
    exact congrArg (fun d' => f.val.val.val (AdelicGL.pair F n (a.val * q.val) d')) hd
  rw [hvalue, scalarSection_pair_mul F B S f.val.val, he q hqk]
  have hc (j : Fin r) : coefficientExtension F B S m (c j) (b x) =
      (c j).val (leviPair F B (B.leviProjection (InfiniteAdeles F) a) m) := by
    rw [← hab, coefficientExtension_apply_parabolic]
  simp only [hab, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc]
  rfl

/-- The actual infinite slice at each finite argument belongs to the smooth
function space used for archimedean differentiation. -/
theorem infiniteSlice_mem_smoothFunctions (f : CompactFiniteRealizedSections F B S)
    (hf : HasSmoothCompactSlices F B S f.val.val) (d : FiniteAdelicGL F n) :
    (fun a => f.val.val.val (AdelicGL.pair F n a d)) ∈ ArchimedeanGL.smoothFunctions F n := by
  change ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞
    (fun g : ArchimedeanGL F n => f.val.val.val (AdelicGL.pair F n ((e).symm g) d))
  intro g
  have h := (contDiffAt_infiniteSliceExtension F B S f hf d g).comp_contMDiffAt
    (Units.contMDiff_val (𝕜 := ℝ) (n := ∞) g)
  simpa only [Function.comp_def, infiniteSliceExtension_apply] using h

/-- Smoothness of every full infinite slice provides the ambient extensions
for the scalar evaluations of normalized compact slices. -/
theorem hasSmoothCompactSlices_of_infiniteSlice_mem (f : RealizedSections F B S)
    (hf : ∀ d : FiniteAdelicGL F n,
      (fun a => f.val (AdelicGL.pair F n a d)) ∈ ArchimedeanGL.smoothFunctions F n) :
    HasSmoothCompactSlices F B S f := by
  intro k l m
  let a := B.leviEmbedding (Adeles F) m
  let g := AdelicGL.infinite F n a
  let d := AdelicGL.finite F n a * l.val
  let s : ArchimedeanGL.SmoothFunctions F n :=
    ⟨fun h => f.val (AdelicGL.pair F n h d), hf d⟩
  let L : A → A := fun x => (e g).val * x
  have hbase (q : KI) : L (compactMatrix F q) = (e (g * q.val)).val := by
    simp only [L, compactMatrix, map_mul, Units.val_mul]
  have hL : ContDiffAt ℝ ∞ L (compactMatrix F k) := contDiffAt_const.mul contDiffAt_id
  have hs := ArchimedeanGL.coordinateExtension_contDiffAt F n s (e (g * k.val))
  rw [← hbase k] at hs
  refine ⟨fun x => (leviHalfCharacter F B m : ℂ)⁻¹ *
      ArchimedeanGL.coordinateExtension F n s (L x),
    contDiffAt_const.mul (hs.comp _ hL), Filter.Eventually.of_forall ?_⟩
  intro x q hq
  dsimp only
  rw [← hq, hbase q, ArchimedeanGL.coordinateExtension_apply,
    ContinuousMulEquiv.symm_apply_apply]
  have hpair : AdelicGL.pair F n (g * q.val) d = a * (compactPair F q l).val := by
    rw [show g = AdelicGL.infinite F n a from rfl, show d = AdelicGL.finite F n a * l.val from rfl,
      ← AdelicGL.pair_mul, AdelicGL.pair_projections, compactPair_val]
  change (leviHalfCharacter F B m : ℂ)⁻¹ * f.val (AdelicGL.pair F n (g * q.val) d) =
    (leviHalfCharacter F B m : ℂ)⁻¹ * f.val (a * (compactPair F q l).val)
  rw [hpair]

end Langlands.Global.AdelicBlockScalarSections
