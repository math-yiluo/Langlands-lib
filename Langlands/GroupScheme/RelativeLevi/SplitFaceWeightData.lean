import Langlands.GroupScheme.RelativeLevi.FaceHeightCocharacter
import Langlands.GroupScheme.RelativeLevi.SplitParabolicVectorSeries

/-! # Unscaled face weights on actual split root charts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.LinearAlgebra.RootDatumFaceHeight

variable {J M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootDatum J M N} (b : P.Base) (cv : N)

/-- Face heights are nonnegative on every positive root, for any face coweight. -/
theorem faceHeight_nonneg_of_isPos [Finite J] {a : J} (ha : b.IsPos a) :
    0 ≤ faceHeight b cv (P.rootSpanMem ℤ a) := by
  apply ha.induction_on_add
  · intro a ha
    rw [faceHeight_simple b cv a ha]
    split_ifs <;> norm_num
  · intro a c e he hA hc
    have he' : P.rootSpanMem ℤ e = P.rootSpanMem ℤ a + P.rootSpanMem ℤ c := by
      apply Subtype.ext
      exact he
    rw [he', map_add, faceHeight_simple b cv c hc]
    exact add_nonneg hA (by split_ifs <;> norm_num)

/-- On roots with nonnegative pairing, a dominant face height is positive
exactly when the original coweight pairing is positive. -/
theorem faceHeight_pos_iff_of_nonneg
    (hdom : ∀ i ∈ b.support, 0 ≤ P.root' i cv) (a : J)
    (ha : 0 ≤ P.root' a cv) :
    0 < faceHeight b cv (P.rootSpanMem ℤ a) ↔ 0 < P.root' a cv := by
  constructor
  · intro h
    by_contra hn
    have hz : P.root' a cv = 0 := by omega
    rw [faceHeight_root_of_eq_zero hdom a hz] at h
    omega
  · intro h
    exact lt_of_lt_of_le (by norm_num) (one_le_faceHeight_root_of_pos hdom a h)

end Langlands.LinearAlgebra.RootDatumFaceHeight

namespace Langlands.GroupScheme.LocalSplitCell

open RelativeUnipotent Langlands.GroupTheory
open Langlands.LinearAlgebra.RootDatumFaceHeight

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
  {G U : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {fam : J → (Ga R ⟶ G)}
  (j : U ⟶ G) (hu : TorusEquivariant i (fun a => P.root a) fam)
  (reg : I → ℤ)
  (hU : (Dynamic.unipotent (AffineRegularBorel.cocharacter i reg)).IsRepresentedBy j)
  {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}
  (hpos : ∀ k, 0 < coPairing (P.root (pos k)) reg)
  [IsOpenImmersion (cellMap i fam neg pos).left]
  (hneg : ∀ k, coPairing (P.root (neg k)) reg < 0)

include hneg in
/-- Any nonnegative integral root-span linear form gives the unscaled
commutator sum bound on the actual regular-cell root factors. -/
theorem commutator_unipotent_rootFactor_le_of_rootSpanLinear
    (b : P.Base) (h : P.rootSpan ℤ →ₗ[ℤ] ℤ) (w : Fin n → ℕ)
    (hw : ∀ k, h (P.rootSpanMem ℤ (pos k)) = (w k : ℤ))
    (T : Over (Spec (CommRingCat.of R))) (k l : Fin n) :
    ⁅rootFactor (liftedPositiveRootToUnipotent j hu reg hU hpos) ULift.up T k,
      rootFactor (liftedPositiveRootToUnipotent j hu reg hU hpos) ULift.up T l⁆ ≤
      HeightFiltration.level
        (rootFactor (liftedPositiveRootToUnipotent j hu reg hU hpos) ULift.up T)
        w (w k + w l) := by
  obtain ⟨d, hd, cv, hcv⟩ := exists_coPairing_eq_rootSpanLinear P b h
  have he (p : Fin n) : coPairing (P.root (pos p)) cv = d * (w p : ℤ) := by
    rw [hcv (P.rootSpanMem ℤ (pos p)), hw p]
  apply Subgroup.commutator_le.mpr
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  obtain ⟨c, hc, hlow⟩ := exists_unipotent_commutator_eq_weight_ge_of_regular
    j hu reg hU hpos hneg cv k l
      (by rw [he]; exact mul_nonneg hd.le (Int.natCast_nonneg _))
      (by rw [he]; exact mul_nonneg hd.le (Int.natCast_nonneg _)) T x.toAdd y.toAdd
  change ⁅rootPoint (positiveRootToUnipotent j hu reg hU hpos k) T x.toAdd,
    rootPoint (positiveRootToUnipotent j hu reg hU hpos l) T y.toAdd⁆ ∈ _
  rw [hc]
  apply (HeightFiltration.level
    (rootFactor (liftedPositiveRootToUnipotent j hu reg hU hpos) ULift.up T)
    w (w k + w l)).list_prod_mem
  intro a ha
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp ha
  by_cases hp : w k + w l ≤ w p
  · exact HeightFiltration.le_level _ _ hp
      (mem_rootFactor (liftedPositiveRootToUnipotent j hu reg hU hpos) ULift.up T p (c p))
  · have hc0 : c p = 0 := hlow p (by
      rw [he p, he k, he l]
      have hp' : (w p : ℤ) < (w k : ℤ) + (w l : ℤ) := by omega
      nlinarith)
    rw [hc0, rootPoint_zero]
    exact one_mem _

variable [IsAffine U.X.left]

/-- Nonnegative values of an integral root-span linear form give actual
weight data, without scaling its integer values. -/
def positiveCellRootLinearWeightData (b : P.Base) (h : P.rootSpan ℤ →ₗ[ℤ] ℤ)
    (hwt : ∀ k, 0 ≤ h (P.rootSpanMem ℤ (pos k))) :
    RootWeightData (positiveCellRootHeightChart j hu reg hU hpos hneg) where
  weight := fun k => (h (P.rootSpanMem ℤ (pos k))).toNat
  commutator := commutator_unipotent_rootFactor_le_of_rootSpanLinear
    j hu reg hU hpos hneg b h _
      (fun k => (Int.toNat_of_nonneg (hwt k)).symm)

/-- Actual unscaled canonical face weights on the specified regular-cell chart.
Only the chosen positive system and the zero simple-root face enter the weights. -/
def positiveCellRootFaceWeightData [Finite J] (b : P.Base) (cv : I → ℤ)
    (hb : ∀ k, b.IsPos (pos k)) :
    RootWeightData (positiveCellRootHeightChart j hu reg hU hpos hneg) :=
  positiveCellRootLinearWeightData j hu reg hU hpos hneg b (faceHeight b cv)
    (fun k => faceHeight_nonneg_of_isPos b cv (hb k))

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

variable {R : Type u} [CommRing R]
  {U : GroupScheme (Spec (CommRingCat.of R))} {C : RootHeightChart U}

/-- Only the set of zero roots controls the positive term at cutoff one. -/
theorem subgroup_zero_eq_of_zero_iff (W W' : RootWeightData C)
    (h : ∀ k, W.weight k = 0 ↔ W'.weight k = 0) :
    W.subgroup 0 = W'.subgroup 0 := by
  ext T x
  rw [W.mem_subgroup_iff, W'.mem_subgroup_iff]
  constructor
  · intro hx k hk
    apply hx k
    have := (h k).mpr (by omega)
    omega
  · intro hx k hk
    apply hx k
    have := (h k).mp (by omega)
    omega

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData
