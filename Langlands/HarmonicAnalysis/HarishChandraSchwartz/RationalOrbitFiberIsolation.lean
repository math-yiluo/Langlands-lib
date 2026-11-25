import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitCentralProjection
import Langlands.Representation.Plancherel.RationalOrbitSmoothFunctions

/-! # Isolating one class of a finite central-character fiber by a smooth orbit function

In the proof of Theorem VIII.4.2, Waldspurger chooses a section `ψ` vanishing at the
classes of the finite fiber `𝒪_χ` other than `ω`. This module constructs a scalar smooth
function on the actual orbit which is `1` at a prescribed class and `0` at the other
classes of any finite set, and multiplies a section by it.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Langlands.HarishChandraSchwartz

universe u uV

open Langlands.Plancherel

section Torus

variable {J : Type*} [Fintype J]

/-- A coordinate of the finite torus is a smooth torus function. -/
theorem isSmoothFiniteTorusFunction_coord (j : J) :
    IsSmoothFiniteTorusFunction (fun z : J → Circle => ((z j : Circle) : ℂ)) := by
  have hcomp : (fun z : J → Circle => ((z j : Circle) : ℂ)) ∘ finiteTorusExp =
      fun x : J → ℝ => Complex.exp ((x j : ℂ) * Complex.I) := by
    funext x
    rfl
  unfold IsSmoothFiniteTorusFunction
  rw [hcomp]
  exact (Complex.contDiff_exp (𝕜 := ℝ)).comp
    ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ ↦ ℝ) j)).mul contDiff_const)

/-- Lagrange interpolation on the finite torus: for a finite set `Z` and a point `z₀` there
is a smooth torus function equal to `1` at `z₀` and to `0` at the other points of `Z`. It
is a product of affine functions of the coordinates. -/
theorem exists_isSmoothFiniteTorusFunction_lagrange (Z : Set (J → Circle)) (hZ : Z.Finite)
    (z₀ : J → Circle) :
    ∃ p : (J → Circle) → ℂ, IsSmoothFiniteTorusFunction p ∧ p z₀ = 1 ∧
      ∀ w ∈ Z, w ≠ z₀ → p w = 0 := by
  classical
  have hj : ∀ w : J → Circle, w ≠ z₀ → ∃ j, w j ≠ z₀ j := fun w hw => by
    by_contra h
    push Not at h
    exact hw (funext h)
  let q : (J → Circle) → (J → Circle) → ℂ := fun w z =>
    if hw : w = z₀ then 1 else
      ((z (Classical.choose (hj w hw)) : ℂ) - (w (Classical.choose (hj w hw)) : ℂ)) *
        ((z₀ (Classical.choose (hj w hw)) : ℂ) - (w (Classical.choose (hj w hw)) : ℂ))⁻¹
  have hq : ∀ w, IsSmoothFiniteTorusFunction (q w) := by
    intro w
    by_cases hw : w = z₀
    · have h1 : q w = fun _ => 1 := by
        funext z
        simp only [q, dite_eq_left hw]
      rw [h1]
      exact contDiff_const
    · have h1 : q w = fun z =>
          ((z (Classical.choose (hj w hw)) : ℂ) - (w (Classical.choose (hj w hw)) : ℂ)) *
            ((z₀ (Classical.choose (hj w hw)) : ℂ) -
              (w (Classical.choose (hj w hw)) : ℂ))⁻¹ := by
        funext z
        simp only [q, dite_eq_right hw]
      rw [h1]
      exact ((isSmoothFiniteTorusFunction_coord (Classical.choose (hj w hw))).sub
        contDiff_const).mul contDiff_const
  refine ⟨fun z => ∏ w ∈ hZ.toFinset, q w z, ?_, ?_, ?_⟩
  · exact contDiff_prod (fun w _ => hq w)
  · refine Finset.prod_eq_one fun w _ => ?_
    by_cases hw : w = z₀
    · simp only [q, dite_eq_left hw]
    · simp only [q, dite_eq_right hw]
      have hne : ((z₀ (Classical.choose (hj w hw)) : ℂ) -
          (w (Classical.choose (hj w hw)) : ℂ)) ≠ 0 := by
        intro h
        exact Classical.choose_spec (hj w hw) (Circle.ext (sub_eq_zero.mp h)).symm
      exact mul_inv_cancel₀ hne
  · intro w hwZ hw
    refine Finset.prod_eq_zero (hZ.mem_toFinset.mpr hwZ) ?_
    simp only [q, dite_eq_right hw, sub_self, zero_mul]

/-- Averaging a smooth torus function over finitely many translations is smooth. -/
theorem isSmoothFiniteTorusFunction_sum_mul_const {ι : Type*} (t : Finset ι)
    (c : ι → J → Circle) {p : (J → Circle) → ℂ} (hp : IsSmoothFiniteTorusFunction p) :
    IsSmoothFiniteTorusFunction (fun z => ∑ i ∈ t, p (z * c i)) := by
  have h : ∀ i ∈ t, IsSmoothFiniteTorusFunction (fun z => p (z * c i)) :=
    fun i _ => (isSmoothFiniteTorusFunction_mul_const_iff p (c i)).mpr hp
  exact ContDiff.sum h

end Torus

section Rational

open CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instRationalOrbitFiberIsolation1 :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance instRationalOrbitFiberIsolation2 :
    NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G
local instance instRationalOrbitFiberIsolation3 : T2Space F := BruhatTits.localField_t2Space F
local instance instRationalOrbitFiberIsolation4 : T2Space (GroupScheme.rationalPoints G) :=
  rationalPoint_t2Space F G
local instance instRationalOrbitFiberIsolation5 :
    LocallyCompactSpace (GroupScheme.rationalPoints G) :=
  rationalPoint_locallyCompactSpace F G
local instance instRationalOrbitFiberIsolation6 :
    SecondCountableTopology (GroupScheme.rationalPoints G) := by
  have : SecondCountableTopology F :=
    HarmonicAnalysis.GeneralLocalField.secondCountableTopology F
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsTopologicalSpace _
  have : SecondCountableTopology (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsSecondCountableTopology (CommAlgCat.of (CommRingCat.of F) F)
  exact (GroupScheme.rationalPointsAffineHomeomorph G).isEmbedding.secondCountableTopology
local instance instRationalOrbitFiberIsolation7 :
    Nonempty (CompactOpenSubgroup (GroupScheme.rationalPoints G)) :=
  ⟨BruhatTits.rationalPointCompactOpenSubgroup F G⟩

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
  [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
  (mu : Measure (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))
  (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
  (hG : GroupScheme.IsConnectedReductive G)

include hindex in
/-- **Smooth isolation on an actual orbit.** For a finite set `Φ` of classes of the
unitary unramified orbit of `omega` and a class `ω₁`, there is a scalar smooth orbit
function equal to `1` at `ω₁` and to `0` at the other classes of `Φ`. -/
theorem exists_rationalSmoothOrbitFunction_isolating :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (Φ : Set (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega)),
      Φ.Finite → ∀ ω₁ : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
      ∃ f ∈ rationalSmoothOrbitFunctions s hs mu hG omega,
        f ω₁ = 1 ∧ ∀ x ∈ Φ, x ≠ ω₁ → f x = 0 := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega Φ hΦ ω₁
  classical
  let c := rationalDiscreteSeriesOrbitCoordinateMap s hs mu hG omega
  let e := rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG
  have hsurj : Function.Surjective c :=
    (isOpenQuotientMap_rationalDiscreteSeriesOrbitCoordinateMap s hs mu hG omega).surjective
  have hfin := finite_rationalDiscreteSeriesStabilizer s hs mu hindex omega
  let Stab := discreteSeriesStabilizer (GroupScheme.rationalPoints.map s).range
    hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega
  let _ : Fintype Stab := Fintype.ofFinite Stab
  -- Fibers of the coordinate map are translates by the stabilizer.
  have hcval : ∀ z, (c z).val = e.symm z • omega := fun z => rfl
  have hfib_mul : ∀ z (χ : Stab), c (z * e χ.val) = c z := by
    intro z χ
    apply Subtype.ext
    rw [hcval, hcval, map_mul, e.symm_apply_apply, mul_smul, χ.property]
  have hfib : ∀ z w, c z = c w → ∃ χ : Stab, w = z * e χ.val := by
    intro z w h
    have hv : e.symm z • omega = e.symm w • omega := by
      rw [← hcval, ← hcval, h]
    refine ⟨⟨(e.symm z)⁻¹ * e.symm w, ?_⟩, ?_⟩
    · change ((e.symm z)⁻¹ * e.symm w) • omega = omega
      rw [mul_smul, ← hv, ← mul_smul, inv_mul_cancel, one_smul]
    · change w = z * e ((e.symm z)⁻¹ * e.symm w)
      rw [map_mul, map_inv, e.apply_symm_apply, e.apply_symm_apply, mul_inv_cancel_left]
  -- The finite set of torus points over `Φ ∪ {ω₁}`.
  obtain ⟨z₁, hz₁⟩ := hsurj ω₁
  have hZ : (c ⁻¹' (Φ ∪ {ω₁})).Finite := by
    refine (hΦ.union (Set.finite_singleton ω₁)).preimage' fun b _ => ?_
    obtain ⟨zb, rfl⟩ := hsurj b
    refine ((Set.finite_range fun χ : Stab => zb * e χ.val)).subset ?_
    intro w hw
    obtain ⟨χ, rfl⟩ := hfib zb w (Set.mem_singleton_iff.mp hw).symm
    exact ⟨χ, rfl⟩
  obtain ⟨p, hp, hp1, hp0⟩ := exists_isSmoothFiniteTorusFunction_lagrange _ hZ z₁
  -- Average over the stabilizer.
  let pbar : (Fin (rationalImageRank G) → Circle) → ℂ := fun z => ∑ χ : Stab, p (z * e χ.val)
  have hpbar : IsSmoothFiniteTorusFunction pbar :=
    isSmoothFiniteTorusFunction_sum_mul_const Finset.univ (fun χ : Stab => e χ.val) hp
  have hpbar_inv : ∀ z (χ' : Stab), pbar (z * e χ'.val) = pbar z := by
    intro z χ'
    change ∑ χ : Stab, p (z * e χ'.val * e χ.val) = ∑ χ : Stab, p (z * e χ.val)
    refine Fintype.sum_equiv (Equiv.mulLeft χ') _ _ fun χ => ?_
    change p (z * e χ'.val * e χ.val) = p (z * e (χ'.val * χ.val))
    rw [map_mul, mul_assoc]
  have hpbar_wd : ∀ z w, c z = c w → pbar z = pbar w := by
    intro z w h
    obtain ⟨χ, rfl⟩ := hfib z w h
    exact (hpbar_inv z χ).symm
  let f : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ :=
    fun x => pbar (Classical.choose (hsurj x))
  have hfc : f ∘ c = pbar := by
    funext z
    exact hpbar_wd _ _ (Classical.choose_spec (hsurj (c z)))
  have hfval : ∀ z, f (c z) = pbar z := fun z => congrFun hfc z
  -- Values of the average.
  have hval : ∀ z, c z ∈ Φ ∪ {ω₁} → pbar z = if c z = ω₁ then 1 else 0 := by
    intro z hz
    split_ifs with hzx
    · have h1 : pbar z = pbar z₁ := hpbar_wd _ _ (hzx.trans hz₁.symm)
      rw [h1]
      change ∑ χ : Stab, p (z₁ * e χ.val) = 1
      rw [Fintype.sum_eq_single 1]
      · simpa using hp1
      · intro χ hχ
        apply hp0
        · change c (z₁ * e χ.val) ∈ Φ ∪ {ω₁}
          rw [hfib_mul, hz₁]
          exact Set.mem_union_right _ rfl
        · intro h
          apply hχ
          apply Subtype.ext
          apply e.injective
          have h' : z₁ * e χ.val = z₁ * 1 := by rw [h, mul_one]
          rw [mul_left_cancel h']
          simp
    · refine Finset.sum_eq_zero fun χ _ => hp0 _ ?_ ?_
      · change c (z * e χ.val) ∈ Φ ∪ {ω₁}
        rw [hfib_mul]
        exact hz
      · intro h
        apply hzx
        rw [← hfib_mul z χ, h, hz₁]
  refine ⟨f, ?_, ?_, ?_⟩
  · change IsSmoothFiniteTorusFunction (f ∘ c)
    rw [hfc]
    exact hpbar
  · rw [← hz₁, hfval, hval z₁ (by rw [hz₁]; exact Set.mem_union_right _ rfl), ite_eq_left hz₁]
  · intro x hx hne
    obtain ⟨z, rfl⟩ := hsurj x
    rw [hfval, hval z (Set.mem_union_left _ hx), ite_eq_right hne]

set_option maxHeartbeats 1600000 in
include hindex in
/-- **An isolated wave packet** (proof of Theorem VIII.4.2, `M = G`). For a class `ω₁` of
the finite fiber `𝒪_η` there is one smooth orbit function `f`, with `f ω₁ = 1`, such that
for every section `ψ` and every `g` (under the continuity and integrability hypotheses of
`integral_central_rationalOrbitWavePacket`) the central projection of the wave packet of
`f • ψ` at `g` is `μ_A(A_G ∩ G¹) (E^G_G ψ_{ω₁})(g)`. -/
theorem integral_central_rationalOrbitWavePacket_isolated :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
      [BorelSpace (GroupScheme.rationalPoints.map s).range]
      (μA : Measure (GroupScheme.rationalPoints.map s).range) [μA.IsMulLeftInvariant]
      (eta : (GroupScheme.rationalPoints.map s).range →* Circle), Continuous eta →
      ∀ ω₁ : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
      ω₁ ∈ rationalOrbitCentralFiber s hs mu omega eta →
      ∃ f ∈ rationalSmoothOrbitFunctions s hs mu hG omega, f ω₁ = 1 ∧
        ∀ (ψ : ∀ x : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
            CoefficientTensor (Quotient.out x.val.val).obj) (g : GroupScheme.rationalPoints G),
        Continuous (fun x => coefficientTensorMap _ (ψ x) g) →
        Integrable (fun a : (GroupScheme.rationalPoints.map s).range =>
          rationalOrbitWavePacket s hs mu hindex omega (fun x => f x • ψ x)
            ((a : GroupScheme.rationalPoints G) * g)) μA →
        ∫ a, ((eta a⁻¹ : Circle) : ℂ) *
            rationalOrbitWavePacket s hs mu hindex omega (fun x => f x • ψ x)
              ((a : GroupScheme.rationalPoints G) * g) ∂μA =
          ((μA (Subtype.val ⁻¹'
            (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)))).toReal : ℂ) *
            coefficientTensorMap _ (ψ ω₁) g := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega _ _ μA _ eta heta ω₁ hω₁
  obtain ⟨f, hf, hf1, hf0⟩ := exists_rationalSmoothOrbitFunction_isolating s hs mu hindex hG
    omega (rationalOrbitCentralFiber s hs mu omega eta)
    (finite_setOf_rationalOrbitCentralCharacter_eq s hs mu hindex omega eta) ω₁
  refine ⟨f, hf, hf1, fun ψ g hcont hintA => ?_⟩
  have hfc : Continuous f := IsSmoothRationalOrbitFunction.continuous s hs mu hG omega hf
  have hcoef : ∀ x, coefficientTensorMap _ (f x • ψ x) g =
      f x * coefficientTensorMap _ (ψ x) g := by
    intro x
    rw [map_smul]
    rfl
  have hvan : ∀ x ∈ rationalOrbitCentralFiber s hs mu omega eta, x ≠ ω₁ →
      (fun x => f x • ψ x) x = 0 := by
    intro x hx hne
    change f x • ψ x = 0
    rw [hf0 x hx hne, zero_smul]
  have hcont' : Continuous (fun x => coefficientTensorMap _ (f x • ψ x) g) := by
    simp_rw [hcoef]
    exact hfc.mul hcont
  rw [integral_central_rationalOrbitWavePacket_of_vanishing s hs mu hindex hG omega μA eta heta
    (fun x => f x • ψ x) ω₁ hω₁ hvan g hcont' hintA]
  change _ * coefficientTensorMap _ (f ω₁ • ψ ω₁) g = _
  rw [hf1, one_smul]

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine T.X.left] in
/-- The smooth finite-fiber isolation on actual orbits, recorded as a proposition over all
the structural choices of `RationalOrbitCentralProjection`. It is proved below by
`exists_rationalSmoothOrbitFunction_isolating`. -/
def RationalOrbitFiberIsolationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left]
    (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
    [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
    (mu : Measure (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)),
    (RenardCartan.splitValuationImage s).FiniteIndex →
    ∀ hG : GroupScheme.IsConnectedReductive G,
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (Φ : Set (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega)),
      Φ.Finite → ∀ ω₁ : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
      ∃ f ∈ rationalSmoothOrbitFunctions s hs mu hG omega,
        f ω₁ = 1 ∧ ∀ x ∈ Φ, x ≠ ω₁ → f x = 0

theorem rationalOrbitFiberIsolation : RationalOrbitFiberIsolationStatement.{u, uV} :=
  fun _ _ _ _ _ _ _ _ _ _ s hs _ mu hindex hG =>
    exists_rationalSmoothOrbitFunction_isolating s hs mu hindex hG

end Rational

end Langlands.HarishChandraSchwartz
