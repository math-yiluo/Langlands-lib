import Langlands.HarmonicAnalysis.UnitConjugation.RegularSet
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Intertwiners on a semisimple Lie algebra slice -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Function Set
open scoped _root_.Topology

universe u v

local notation "C(" F "," S ")" => Subalgebra.centralizer F {S}
local notation "W(" F "," S ")" => LinearMap.range (adjointEndomorphism F S)

section Algebra

variable {F : Type u} [Field F] {A : Type v} [Ring A] [Algebra F A]

private theorem centralizer_commute {S : A} (x : C(F, S)) : Commute S (x : A) :=
  (Subalgebra.mem_centralizer_iff F).mp x.property S (Set.mem_singleton _)

private theorem centralizer_mul_mem_range {S : A} (x : C(F, S)) {z : A} (hz : z ∈ W(F, S)) :
    (x : A) * z ∈ W(F, S) := by
  obtain ⟨a, rfl⟩ := hz
  refine ⟨(x : A) * a, ?_⟩
  simp only [adjointEndomorphism_apply, mul_sub]
  rw [← mul_assoc S, (centralizer_commute x).eq, mul_assoc (x : A) S, mul_assoc (x : A) a]

private theorem range_mul_centralizer_mem {S : A} (x : C(F, S)) {z : A} (hz : z ∈ W(F, S)) :
    z * (x : A) ∈ W(F, S) := by
  obtain ⟨a, rfl⟩ := hz
  refine ⟨a * (x : A), ?_⟩
  simp only [adjointEndomorphism_apply, sub_mul]
  rw [← mul_assoc S, mul_assoc a (x : A), ← (centralizer_commute x).eq, ← mul_assoc a]

/-- The restriction of `a ↦ Xa - aY` to the range of `ad S`. -/
def sliceIntertwiner {S : A} (X Y : C(F, S)) : Module.End F (W(F, S)) :=
  (LinearMap.mulLeft F (X : A) - LinearMap.mulRight F (Y : A)).restrict fun _ ha =>
    (W(F, S)).sub_mem (centralizer_mul_mem_range X ha) (range_mul_centralizer_mem Y ha)

@[simp] theorem sliceIntertwiner_apply {S : A} (X Y : C(F, S)) (a : W(F, S)) :
    (sliceIntertwiner X Y a : A) = (X : A) * (a : A) - (a : A) * (Y : A) := rfl

private def rangeMul {S : A} (X Y : C(F, S)) : Module.End F (W(F, S)) :=
  ((LinearMap.mulRight F (Y : A)).comp (LinearMap.mulLeft F (X : A))).restrict
    fun _ ha => range_mul_centralizer_mem Y (centralizer_mul_mem_range X ha)

private def rangeMulEquiv {S : A} (u v : C(F, S)ˣ) : W(F, S) ≃ₗ[F] W(F, S) := by
  let U := Units.map (C(F, S)).val.toMonoidHom u
  let V := Units.map (C(F, S)).val.toMonoidHom v
  refine LinearEquiv.ofLinearMap (rangeMul u.val (v⁻¹ : C(F, S)ˣ).val)
    (rangeMul (u⁻¹ : C(F, S)ˣ).val v.val) ?_ ?_
  · ext a
    change (U : A) * ((↑U⁻¹ : A) * (a : A) * (V : A)) * (↑V⁻¹ : A) = (a : A)
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
  · ext a
    change (↑U⁻¹ : A) * ((U : A) * (a : A) * (↑V⁻¹ : A)) * (V : A) = (a : A)
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]

/-- Independent unit conjugations of the two parameters give a conjugate endomorphism on
`range (ad S)`. -/
private theorem sliceIntertwiner_conj {S : A} (u v : C(F, S)ˣ) (X Y : C(F, S)) :
    sliceIntertwiner (conjugationLinearEquiv F u X) (conjugationLinearEquiv F v Y) =
      (rangeMulEquiv u v).conj (sliceIntertwiner X Y) := by
  let e := rangeMulEquiv u v
  let U := Units.map (C(F, S)).val.toMonoidHom u
  let V := Units.map (C(F, S)).val.toMonoidHom v
  ext a
  obtain ⟨b, rfl⟩ := e.surjective a
  change (sliceIntertwiner (conjugationLinearEquiv F u X) (conjugationLinearEquiv F v Y)
    (e b) : A) = (e.conj (sliceIntertwiner X Y) (e b) : A)
  rw [LinearEquiv.conj_apply_apply, e.symm_apply_apply]
  change ((U : A) * (X : A) * (↑U⁻¹ : A)) * ((U : A) * (b : A) * (↑V⁻¹ : A)) -
      ((U : A) * (b : A) * (↑V⁻¹ : A)) * ((V : A) * (Y : A) * (↑V⁻¹ : A)) =
    (U : A) * ((X : A) * (b : A) - (b : A) * (Y : A)) * (↑V⁻¹ : A)
  simp only [mul_sub, sub_mul, mul_assoc, Units.inv_mul_cancel_left]

/-- The determinant of the restricted intertwiner is invariant in each conjugacy variable. -/
theorem det_sliceIntertwiner_conj [FiniteDimensional F A] {S : A}
    (u v : C(F, S)ˣ) (X Y : C(F, S)) :
    (sliceIntertwiner (conjugationLinearEquiv F u X) (conjugationLinearEquiv F v Y)).det =
      (sliceIntertwiner X Y).det := by
  rw [sliceIntertwiner_conj, LinearEquiv.conj_apply, LinearMap.comp_assoc,
    LinearMap.det_conj]

/-- If the restricted intertwiner is injective, every ambient intertwiner belongs to the
centralizer of `S`. -/
theorem mem_centralizer_of_intertwiner {S : A} (hS : IsCompl (C(F, S)).toSubmodule (W(F, S)))
    {X Y : C(F, S)} (hXY : Injective (sliceIntertwiner X Y)) {a : A}
    (ha : (X : A) * a = a * (Y : A)) : a ∈ C(F, S) := by
  let d := LinearMap.mulLeft F (X : A) - LinearMap.mulRight F (Y : A)
  obtain ⟨⟨b, w⟩, hbw⟩ := ((C(F, S)).toSubmodule.prodEquivOfIsCompl (W(F, S)) hS).surjective a
  change (b : A) + (w : A) = a at hbw
  have hd : d a = 0 := sub_eq_zero.mpr ha
  have hsum : d b + d w = 0 := by rw [← map_add, hbw, hd]
  have hb : d b ∈ (C(F, S)).toSubmodule :=
    (C(F, S)).sub_mem ((C(F, S)).mul_mem X.property b.property)
      ((C(F, S)).mul_mem b.property Y.property)
  have hw : d w ∈ (C(F, S)).toSubmodule := by
    rw [eq_neg_iff_add_eq_zero.mpr ((add_comm (d w) (d b)).trans hsum)]
    exact (C(F, S)).neg_mem hb
  have hz : d w = 0 := Submodule.disjoint_def.mp hS.disjoint _ hw
    (sliceIntertwiner X Y w).property
  have hw0 : w = 0 := hXY (by rw [map_zero]; exact Subtype.ext hz)
  rw [hw0, Submodule.coe_zero, add_zero] at hbw
  exact hbw ▸ b.property

end Algebra

section Topology

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  {A : Type v} [NormedRing A] [NormedAlgebra F A] [FiniteDimensional F A]

private def sliceIntertwinerLinear (S : A) : C(F, S) × C(F, S) →ₗ[F] Module.End F (W(F, S)) where
  toFun z := sliceIntertwiner z.1 z.2
  map_add' z w := by
    ext a
    change ((z.1 : A) + (w.1 : A)) * (a : A) - (a : A) * ((z.2 : A) + (w.2 : A)) =
      ((z.1 : A) * (a : A) - (a : A) * (z.2 : A)) +
        ((w.1 : A) * (a : A) - (a : A) * (w.2 : A))
    rw [add_mul, mul_add]
    abel
  map_smul' t z := by
    ext a
    change (t • (z.1 : A)) * (a : A) - (a : A) * (t • (z.2 : A)) =
      t • ((z.1 : A) * (a : A) - (a : A) * (z.2 : A))
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub]

private theorem continuous_det_sliceIntertwiner (S : A) :
    Continuous (fun z : C(F, S) × C(F, S) => (sliceIntertwiner z.1 z.2).det) := by
  let L := (LinearMap.toContinuousLinearMap : Module.End F (W(F, S)) ≃ₗ[F] (W(F, S) →L[F] W(F, S)))
  exact ContinuousLinearMap.continuous_det.comp
    (L.toLinearMap.comp (sliceIntertwinerLinear S)).continuous_of_finiteDimensional

/-- In an open invariant neighborhood of the slice center every pair has an invertible
restricted intertwiner. -/
def SemisimpleSliceIntertwinerStatement : Prop :=
  ∀ (F : Type u) [NontriviallyNormedField F] [CompleteSpace F] (A : Type v) [NormedRing A]
    [NormedAlgebra F A] [FiniteDimensional F A] (S : A),
    IsCompl (C(F, S)).toSubmodule (W(F, S)) →
    ∃ U : Set (C(F, S)), IsOpen U ∧
      (⟨S, (Subalgebra.mem_centralizer_iff F).mpr fun _ ht => (Set.mem_singleton_iff.mp ht).symm ▸ rfl⟩ :
        C(F, S)) ∈ U ∧
      (∀ (u : C(F, S)ˣ) (X : C(F, S)), X ∈ U → conjugationHomeomorph u X ∈ U) ∧
      ∀ X ∈ U, ∀ Y ∈ U, Bijective (sliceIntertwiner X Y)

theorem semisimpleSliceIntertwiner : SemisimpleSliceIntertwinerStatement.{u, v} := by
  intro F _ _ A _ _ _ S hS
  let s : C(F, S) := ⟨S, (Subalgebra.mem_centralizer_iff F).mpr fun t ht => by
    rw [Set.mem_singleton_iff.mp ht]⟩
  have hs : Injective (sliceIntertwiner s s) := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro w hw
    have h0 : S * (w : A) - (w : A) * S = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hw)
    have hc : (w : A) ∈ (C(F, S)).toSubmodule := by
      apply (Subalgebra.mem_centralizer_iff F).mpr
      intro t ht
      rw [Set.mem_singleton_iff.mp ht]
      exact sub_eq_zero.mp h0
    exact Subtype.ext (Submodule.disjoint_def.mp hS.disjoint _ hc w.property)
  have det_iff (T : Module.End F (W(F, S))) : T.det ≠ 0 ↔ Bijective T := by
    rw [← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]
  let D : Set (C(F, S) × C(F, S)) := {z | (sliceIntertwiner z.1 z.2).det ≠ 0}
  have hD : IsOpen D := isOpen_compl_singleton.preimage (continuous_det_sliceIntertwiner S)
  have hss : (s, s) ∈ D := (det_iff _).2 ⟨hs, LinearMap.injective_iff_surjective.mp hs⟩
  obtain ⟨P, Q, hPo, hPs, hQo, hQs, hPQ⟩ := mem_nhds_prod_iff'.mp (hD.mem_nhds hss)
  let U := conjugationSaturation (P ∩ Q)
  refine ⟨U, isOpen_iUnion fun u => (conjugationHomeomorph u).isOpenMap _ (hPo.inter hQo),
    subset_conjugationSaturation (P ∩ Q) ⟨hPs, hQs⟩, ?_, ?_⟩
  · intro u X hX
    obtain ⟨v, x, hx, hv⟩ := mem_conjugationSaturation_iff.mp hX
    exact mem_conjugationSaturation_iff.mpr ⟨u * v, x, hx, by
      change conjugationHomeomorph (u * v) x = conjugationHomeomorph u X
      rw [conjugationHomeomorph_mul, show conjugationHomeomorph v x = X from hv]⟩
  · intro X hX Y hY
    obtain ⟨u, x, hx, rfl⟩ := mem_conjugationSaturation_iff.mp hX
    obtain ⟨v, y, hy, rfl⟩ := mem_conjugationSaturation_iff.mp hY
    apply (det_iff _).mp
    change (sliceIntertwiner (conjugationLinearEquiv F u x) (conjugationLinearEquiv F v y)).det ≠ 0
    rw [det_sliceIntertwiner_conj]
    exact hPQ (show (x, y) ∈ P ×ˢ Q from ⟨hx.1, hy.2⟩)

end Topology

end Langlands.HarmonicAnalysis.UnitConjugation
