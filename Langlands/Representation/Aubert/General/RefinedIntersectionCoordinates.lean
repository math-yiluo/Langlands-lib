import Langlands.Representation.Aubert.General.SemidirectHaarModulus

/-! # Coordinates on the intersection of two refined radicals -/

noncomputable section

open scoped Pointwise

namespace Langlands.Aubert.General

namespace IsSemidirectDecomposition

variable {A : Type*} [Group A] {P M U R B W : Subgroup A}
  (d : IsSemidirectDecomposition P M U)

include d

/-- A literal product of subgroups of the two original factors inherits their
unique factorization, provided its radical factor is normalized. -/
theorem ofSubgroupProduct (hB : B ≤ M) (hW : W ≤ U)
    (hRW : R ≤ Subgroup.normalizer W)
    (hprod : (R : Set A) = (B : Set A) * (W : Set A)) :
    IsSemidirectDecomposition R B W := by
  have hBR : B ≤ R := by
    intro b hb
    change b ∈ (R : Set A)
    rw [hprod]
    exact ⟨b, hb, 1, W.one_mem, mul_one b⟩
  have hWR : W ≤ R := by
    intro w hw
    change w ∈ (R : Set A)
    rw [hprod]
    exact ⟨1, B.one_mem, w, hw, one_mul w⟩
  have hRP : R ≤ P := by
    intro x hx
    have hx' : x ∈ (B : Set A) * (W : Set A) := by
      rw [← hprod]
      exact hx
    obtain ⟨b, hb, w, hw, rfl⟩ := Set.mem_mul.mp hx'
    exact P.mul_mem (d.levi_le (hB hb)) (d.unipotent_le (hW hw))
  refine ⟨hBR, hWR, hRW, ?_⟩
  apply Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mpr
  intro q
  have hq : (q : A) ∈ (B : Set A) * (W : Set A) := by
    rw [← hprod]
    exact q.property
  obtain ⟨b, hb, w, hw, hbw⟩ := Set.mem_mul.mp hq
  let m : B.subgroupOf R := ⟨⟨b, hBR hb⟩, hb⟩
  have hbq : b⁻¹ * (q : A) ∈ W := by
    rw [← hbw, inv_mul_cancel_left]
    exact hw
  have hbproj : d.projection ⟨q, hRP q.property⟩ = ⟨b, hB hb⟩ :=
    (d.projection_eq_iff _ _).mpr (hW hbq)
  refine ⟨m, hbq, ?_⟩
  intro n hn
  apply Subtype.ext
  apply Subtype.ext
  have hnproj : d.projection ⟨q, hRP q.property⟩ =
      ⟨n.val.val, hB n.property⟩ :=
    (d.projection_eq_iff _ _).mpr (hW hn)
  exact congrArg (fun m : M => (m : A)) (hnproj.symm.trans hbproj)

/-- Any finer decomposition whose two factors lie in the original factors
uses the original Levi projection on ambient points. -/
theorem projection_eq_of_subdecomposition
    (e : IsSemidirectDecomposition R B W)
    (hRP : R ≤ P) (hBM : B ≤ M) (hWU : W ≤ U) (r : R) :
    (e.projection r : A) = (d.projection ⟨r, hRP r.property⟩ : A) := by
  symm
  exact congrArg Subtype.val ((d.projection_eq_iff _
    ⟨e.projection r, hBM (e.projection r).property⟩).mpr
      (hWU (e.projection_inv_mul_mem r)))

variable [TopologicalSpace A]

/-- The refined projection is continuous whenever the original projection is. -/
theorem continuous_projection_of_subdecomposition
    (e : IsSemidirectDecomposition R B W)
    (hRP : R ≤ P) (hBM : B ≤ M) (hWU : W ≤ U)
    (hp : Continuous d.projection) : Continuous e.projection := by
  apply continuous_induced_rng.mpr
  change Continuous (fun r : R => (e.projection r : A))
  have he : (fun r : R => (e.projection r : A)) =
      fun r : R => (d.projection ⟨r, hRP r.property⟩ : A) :=
    funext (d.projection_eq_of_subdecomposition e hRP hBM hWU)
  rw [he]
  exact continuous_subtype_val.comp
    (hp.comp (continuous_subtype_val.subtype_mk _))

end IsSemidirectDecomposition

namespace RefinedIntersection

variable {A : Type*} [Group A] (M U Q N V R S : Subgroup A)
  (hR : (R : Set A) = (↑(M ⊓ V) : Set A) * (U : Set A))
  (hS : (S : Set A) = (↑(N ⊓ U) : Set A) * (V : Set A))
  (hSQ : S ≤ Q)
  (hUQ : (↑(U ⊓ Q) : Set A) =
    (↑(U ⊓ N) : Set A) * (↑(U ⊓ V) : Set A))

include hR hS hSQ hUQ

/-- The intersection of the two refined radicals retains the first endpoint
factor and the original radical-parabolic intersection. -/
theorem eq_mul :
    (↑(R ⊓ S) : Set A) =
      (↑(M ⊓ V) : Set A) * (↑(U ⊓ Q) : Set A) := by
  have hVS : V ≤ S := by
    intro v hv
    change v ∈ (S : Set A)
    rw [hS]
    exact ⟨1, ⟨N.one_mem, U.one_mem⟩, v, hv, one_mul v⟩
  have hUQS : U ⊓ Q ≤ S := by
    intro u hu
    have hu' : u ∈ (↑(U ⊓ N) : Set A) * (↑(U ⊓ V) : Set A) := by
      rw [← hUQ]
      exact hu
    obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.mp hu'
    change a * c ∈ (S : Set A)
    rw [hS]
    exact ⟨a, ⟨ha.2, ha.1⟩, c, hc.2, rfl⟩
  ext x
  constructor
  · intro hx
    have hx' : x ∈ (↑(M ⊓ V) : Set A) * (U : Set A) := by
      rw [← hR]
      exact hx.1
    obtain ⟨b, hb, u, hu, hbu⟩ := Set.mem_mul.mp hx'
    have huS : u ∈ S := by
      have h := S.mul_mem (S.inv_mem (hVS hb.2)) hx.2
      rwa [← hbu, inv_mul_cancel_left] at h
    exact ⟨b, hb, u, ⟨hu, hSQ huS⟩, hbu⟩
  · rintro ⟨b, hb, u, hu, rfl⟩
    refine ⟨?_, S.mul_mem (hVS hb.2) (hUQS hu)⟩
    change b * u ∈ (R : Set A)
    rw [hR]
    exact ⟨b, hb, u, hu.1, rfl⟩

/-- All three actual factors, in the order used by multiplication coordinates. -/
theorem eq_triple_mul :
    (↑(R ⊓ S) : Set A) =
      (↑(M ⊓ V) : Set A) *
        ((↑(U ⊓ N) : Set A) * (↑(U ⊓ V) : Set A)) := by
  rw [eq_mul M U Q N V R S hR hS hSQ hUQ, hUQ]

variable {P : Subgroup A}

omit hS hSQ hUQ in
/-- The first refined radical remains in the original parabolic. -/
theorem left_le_parabolic (d : IsSemidirectDecomposition P M U) : R ≤ P := by
  intro x hx
  have hx' : x ∈ (↑(M ⊓ V) : Set A) * (U : Set A) := by
    rw [← hR]
    exact hx
  obtain ⟨b, hb, u, hu, rfl⟩ := Set.mem_mul.mp hx'
  exact P.mul_mem (d.levi_le hb.1) (d.unipotent_le hu)

/-- The outer multiplication coordinates retain the first endpoint factor. -/
theorem outerDecomposition (d : IsSemidirectDecomposition P M U) :
    IsSemidirectDecomposition (R ⊓ S) (M ⊓ V) (U ⊓ Q) := by
  apply d.ofSubgroupProduct inf_le_left inf_le_left ?_
    (eq_mul M U Q N V R S hR hS hSQ hUQ)
  intro x hx
  apply Subgroup.inf_normalizer_le_normalizer_inf
  exact ⟨d.le_normalizer
    (left_le_parabolic M U V R hR d hx.1),
    Subgroup.le_normalizer (hSQ hx.2)⟩

omit hR hS hSQ in
/-- The inner multiplication coordinates use the second original projection. -/
theorem innerDecomposition (e : IsSemidirectDecomposition Q N V) :
    IsSemidirectDecomposition (U ⊓ Q) (U ⊓ N) (U ⊓ V) := by
  apply e.ofSubgroupProduct inf_le_right inf_le_right ?_ hUQ
  intro x hx
  apply Subgroup.inf_normalizer_le_normalizer_inf
  exact ⟨Subgroup.le_normalizer hx.1, e.le_normalizer hx.2⟩

variable [TopologicalSpace A]

/-- Both refined projections are restrictions of the original projections. -/
theorem continuous_outer_projection (d : IsSemidirectDecomposition P M U)
    (hp : Continuous d.projection) :
    Continuous (outerDecomposition M U Q N V R S hR hS hSQ hUQ d).projection :=
  d.continuous_projection_of_subdecomposition
    (outerDecomposition M U Q N V R S hR hS hSQ hUQ d)
    (inf_le_left.trans (left_le_parabolic M U V R hR d))
    inf_le_left inf_le_left hp

omit hR hS hSQ in
theorem continuous_inner_projection (e : IsSemidirectDecomposition Q N V)
    (hq : Continuous e.projection) :
    Continuous (innerDecomposition U Q N V hUQ e).projection :=
  e.continuous_projection_of_subdecomposition
    (innerDecomposition U Q N V hUQ e)
    inf_le_right inf_le_right inf_le_right hq

variable [IsTopologicalGroup A]

/-- Multiplication gives continuous coordinates in the displayed three factors. -/
def coordinates (d : IsSemidirectDecomposition P M U)
    (e : IsSemidirectDecomposition Q N V)
    (hp : Continuous d.projection) (hq : Continuous e.projection) :
    ↥(M ⊓ V) × (↥(U ⊓ N) × ↥(U ⊓ V)) ≃ₜ ↥(R ⊓ S) :=
  ((Homeomorph.refl ↥(M ⊓ V)).prodCongr
    ((innerDecomposition U Q N V hUQ e).coordinates
      (continuous_inner_projection U Q N V hUQ e hq))).trans
    ((outerDecomposition M U Q N V R S hR hS hSQ hUQ d).coordinates
      (continuous_outer_projection M U Q N V R S hR hS hSQ hUQ d hp))

@[simp]
theorem coordinates_apply (d : IsSemidirectDecomposition P M U)
    (e : IsSemidirectDecomposition Q N V)
    (hp : Continuous d.projection) (hq : Continuous e.projection)
    (b : ↥(M ⊓ V)) (a : ↥(U ⊓ N)) (c : ↥(U ⊓ V)) :
    (coordinates M U Q N V R S hR hS hSQ hUQ d e hp hq (b, a, c) : A) =
      (b : A) * ((a : A) * (c : A)) := rfl

end RefinedIntersection

end Langlands.Aubert.General
