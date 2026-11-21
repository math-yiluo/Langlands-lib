import Langlands.Automorphic.CuspidalJointAdmissibility
import Langlands.Automorphic.JointAdmissibilityTensor
import Langlands.Automorphic.JointMultiplicityEvaluation
import Langlands.Global.AdelicBlockSliceEvaluation

/-!
# Joint admissibility of actual scalar adelic block sections

At an open finite level, finitely many evaluations on the standard finite
compact determine a compact-type intertwiner. Joint admissibility of the
block realizations therefore implies joint admissibility of the induced pair.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands

/-- Joint admissibility descends through a linear injection intertwining both actions. -/
theorem IsJointlyAdmissible.of_injective
    {G K X Y : Type*} [Group G] [TopologicalSpace G] [Group K]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρX : Representation ℂ G X} {κX : Representation ℂ K X}
    {ρY : Representation ℂ G Y} {κY : Representation ℂ K Y}
    (hY : IsJointlyAdmissible ρY κY) (e : X →ₗ[ℂ] Y) (he : Function.Injective e)
    (hρ : ∀ d x, e (ρX d x) = ρY d (e x)) (hκ : ∀ k x, e (κX k x) = κY k (e x)) :
    IsJointlyAdmissible ρX κX := by
  intro L m σ
  refine jointMultiplicitySpace_finite_of_evaluations (I := Unit) (fun _ => e) (fun _ => L)
    (MonoidHom.id K) (fun _ x hx d => ?_) (fun _ k x => hκ k x) hY ?_
  · change ρY (d : G) (e x) = e x
    rw [← hρ]
    exact congrArg e (hx d)
  · intro φ hzero
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change φ.val v = 0
    apply he
    rw [map_zero]
    exact hzero () v

namespace Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear
open AdelicBlockParabolic PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "Kf" => OpenSubgroup.toSubgroup (FiniteAdelicGL.standardIntegral F n)
local notation "K" => (standardCompact F n)
local notation "V" => RealizedSections F B S

local instance (t : ℕ) : AddCommGroup (RationalInvariantFunctions F t) := Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (ContinuousRationalFunctions F t) := Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F t) :=
  Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (AutomorphicForms F t) := Submodule.addCommGroup _
local instance (t : ℕ) : AddCommGroup (StableAutomorphicFunctions F t) := Submodule.addCommGroup _
local instance {t : ℕ} (T : OperatorRealization F t) : AddCommGroup T.Space :=
  Submodule.addCommGroup _

private theorem compactPoint_eq (k : K) (x : Kf) (a : standardInfiniteCompact F n)
    (z : FiniteAdelicGL F n) (ha : AdelicGL.infinite F n k.val = a.val)
    (hx : AdelicGL.finite F n k.val = x.val * z) :
    k.val = (finiteSlicePoint F x).val * AdelicGL.ofInfinite F n a.val * AdelicGL.ofFinite F n z := by
  apply (AdelicGL.split F n).injective
  apply Prod.ext
  · change AdelicGL.infinite F n k.val = AdelicGL.infinite F n (_ * _ * _)
    simp [ha, map_mul, AdelicGL.ofInfinite_eq_pair, AdelicGL.ofFinite_eq_pair]
  · change AdelicGL.finite F n k.val = AdelicGL.finite F n (_ * _ * _)
    simp [hx, map_mul, AdelicGL.ofInfinite_eq_pair, AdelicGL.ofFinite_eq_pair]

/-- The quotient by the open level's intersection with the standard finite compact. -/
abbrev finiteSliceQuotient (L : OpenSubgroup (FiniteAdelicGL F n)) :=
  ↥Kf ⧸ L.toSubgroup.subgroupOf Kf

instance finite_finiteSliceQuotient (L : OpenSubgroup (FiniteAdelicGL F n)) :
    Finite (finiteSliceQuotient F L) := by
  have : CompactSpace ↥Kf :=
    isCompact_iff_compactSpace.mp (FiniteAdelicGL.isCompact_standardIntegral F n)
  exact Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ L.isOpen)

/-- A representative of each coset `x (Kf ∩ L)` in the standard finite compact. -/
def finiteSliceRepresentative (L : OpenSubgroup (FiniteAdelicGL F n))
    (q : finiteSliceQuotient F L) : ↥Kf := Quotient.out q

set_option synthInstance.maxHeartbeats 100000 in
/-- The complete scalar carrier is jointly admissible for its actual finite and
infinite compact right actions whenever the inducing blocks are jointly admissible. -/
theorem RealizedSections.isJointlyAdmissible (h : ∀ i, (S i).IsJointlyAdmissible) :
    Langlands.IsJointlyAdmissible (RealizedSections.finiteAction F B S)
      (RealizedSections.infiniteCompactAction F B S) := by
  intro L m σ
  let H := L.toSubgroup.subgroupOf Kf
  let rep := finiteSliceRepresentative F L
  have hA : IsJointlyAdmissible (coefficientFiniteAction F B S)
      (coefficientInfiniteCompactAction F B S) := FiniteTensor.isJointlyAdmissible_external _ _ h
  apply jointMultiplicitySpace_finite_of_evaluations
    (fun q => finiteSliceEvaluation F B S (rep q)) (fun q => finiteSliceLevel F B L (rep q))
    (infiniteLeviCompactInclusion B F)
    (fun q f hf => finiteSliceEvaluation_mem_fixedVectors F B S L (rep q) f hf)
    (fun q k f => finiteSliceEvaluation_infiniteCompact F B S (rep q) k f) hA
  intro φ hzero
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext g
  obtain ⟨p, k, rfl⟩ := exists_parabolic_mul_standardCompact F B g
  change (φ.val v).val (p.val * k.val) = 0
  rw [scalarSection_apply_mul]
  suffices hs : normalizedSlice F B (φ.val v).val k (B.leviProjection (Adeles F) p) = 0 by
    rw [hs, mul_zero]
  let y := B.leviProjection (Adeles F) p
  have hk := (mem_standardCompact_iff F n k.val).mp k.property
  let a : standardInfiniteCompact F n := ⟨AdelicGL.infinite F n k.val, hk.1⟩
  let x : ↥Kf := ⟨AdelicGL.finite F n k.val, hk.2⟩
  let q : ↥Kf ⧸ H := x
  obtain ⟨d, hd⟩ := QuotientGroup.mk_out_eq_mul H x
  let z : FiniteAdelicGL F n := (d.val.val)⁻¹
  have hz : z ∈ L := L.inv_mem d.property
  have hx : AdelicGL.finite F n k.val = (rep q).val * z := by
    change x.val = (rep q).val * d.val.val⁻¹
    rw [show rep q = x * d.val from hd, Subgroup.coe_mul, mul_inv_cancel_right]
  have hfactor := compactPoint_eq F k (rep q) a z rfl hx
  have htr : normalizedSlice F B (φ.val v).val k y =
      normalizedSlice F B ((RealizedSections.infiniteCompactAction F B S) a (φ.val v)).val
        (finiteSlicePoint F (rep q)) y := by
    let A := B.leviEmbedding (Adeles F) y
    let C := (finiteSlicePoint F (rep q)).val * AdelicGL.ofInfinite F n a.val
    have hfix : (RealizedSections.finiteAction F B S) z (φ.val v) = φ.val v :=
      φ.property.1 v ⟨z, hz⟩
    have hfix' : (φ.val v).val ((A * C) * AdelicGL.ofFinite F n z) = (φ.val v).val (A * C) :=
      congrArg (fun f : V => f.val (A * C)) hfix
    simp only [normalizedSlice, RealizedSections.infiniteCompactAction_apply]
    rw [hfactor, ← mul_assoc A C, hfix', mul_assoc]
  change normalizedSlice F B (φ.val v).val k y = 0
  rw [htr, ← φ.property.2 a v]
  have ht := congrFun (coefficientEvaluation_finiteSliceEvaluation F B S (rep q) (φ.val (σ a v))) y
  rw [hzero q (σ a v), map_zero, Pi.zero_apply] at ht
  exact ht.symm

local instance : AddCommGroup (FiniteSmoothRealizedSections F B S) := Submodule.addCommGroup _
local instance : AddCommGroup (CompactFiniteRealizedSections F B S) := Submodule.addCommGroup _

/-- Joint admissibility also holds after taking the finite-smooth,
infinite-compact-finite carrier. -/
theorem compactFiniteRealizedSections_isJointlyAdmissible
    (h : ∀ i, (S i).IsJointlyAdmissible) :
    Langlands.IsJointlyAdmissible (compactFiniteFiniteSubrepresentation F B S).toRepresentation
      (compactFiniteSubrepresentation F B S).toRepresentation := by
  let e : CompactFiniteRealizedSections F B S →ₗ[ℂ] V :=
    (FiniteSmoothRealizedSections F B S).subtype ∘ₗ
      (CompactFiniteRealizedSections F B S).subtype
  exact (RealizedSections.isJointlyAdmissible F B S h).of_injective e
    (Subtype.val_injective.comp Subtype.val_injective) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The joint admissibility input for an ordered list of actual cuspidal blocks. -/
theorem cuspidalCompactFiniteRealizedSections_isJointlyAdmissible [CompactSpace (AdeleQuotient F)]
    {k : ℕ} {r : Fin k → ℕ} (hr : ∑ i, (r i + 1) = n)
    (T : ∀ i, CuspidalOperatorRealization F (r i)) :
    let B' : BlockShape n := ⟨k, fun i => r i + 1, fun _ => Nat.succ_pos _, hr⟩
    let S' : ∀ i : Fin B'.length, OperatorRealization F (B'.size i) := fun i => (T i).realization
    Langlands.IsJointlyAdmissible (compactFiniteFiniteSubrepresentation F B' S').toRepresentation
      (compactFiniteSubrepresentation F B' S').toRepresentation :=
  compactFiniteRealizedSections_isJointlyAdmissible F _ _ (fun i => (T i).isJointlyAdmissible)

end Global.AdelicBlockScalarSections

end Langlands
