import Langlands.AlgebraicGeometry.PointTopology.Affine
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Localization and principal-open point topologies
-/

noncomputable section

universe u v w z

open Topology

namespace Langlands.AlgebraicGeometry.PointTopology

namespace AlgPoint

variable {R : Type u} {A : Type v} {S : Type w} {L : Type z}
variable [CommRing R] [CommRing A] [CommRing S] [CommRing L]
variable [Algebra R A] [Algebra R S] [Algebra R L] [Algebra A L]
variable [IsScalarTower R A L] (M : Submonoid A) [IsLocalization M L]

/-- Algebra points on which every element of a multiplicative set is unit-valued. -/
abbrev LocalizationLocus := {p : AlgPoint R A S // ∀ m : M, IsUnit (p m)}

/-- Restriction from a localization identifies its points with the unit-valued locus. -/
def localizationPointEquiv : AlgPoint R L S ≃ LocalizationLocus (R := R) (S := S) M where
  toFun p := ⟨precomp (Algebra.algHom R A L) p, fun m =>
    (IsLocalization.map_units L m).map p.toAlgHom.toRingHom⟩
  invFun p := ofAlgHom (IsLocalization.liftAlgHom p.property)
  left_inv p := by
    change IsLocalization.liftAlgHom _ = p.toAlgHom
    apply IsLocalization.algHom_ext M
    ext a
    exact IsLocalization.lift_eq _ a
  right_inv p := by
    apply Subtype.ext
    apply AlgPoint.ext
    intro a
    exact IsLocalization.lift_eq _ a

@[simp] theorem localizationPointEquiv_apply (p : AlgPoint R L S) :
    (localizationPointEquiv (R := R) (S := S) (L := L) M p).val =
      precomp (Algebra.algHom R A L) p := rfl

@[simp] theorem localizationPointEquiv_symm_algebraMap
    (p : LocalizationLocus (R := R) (S := S) M) (a : A) :
    (localizationPointEquiv (R := R) (S := S) (L := L) M).symm p
      (algebraMap A L a) = p.val a :=
  IsLocalization.lift_eq _ a

/-- Every localization coordinate is a numerator times a unit denominator's inverse. -/
theorem localizationPointEquiv_symm_apply
    (p : LocalizationLocus (R := R) (S := S) M) (b : L)
    (a : A) (m : M) (hb : b * algebraMap A L m = algebraMap A L a) :
    (localizationPointEquiv (R := R) (S := S) (L := L) M).symm p b =
      p.val a * Units.val ((p.property m).unit⁻¹) := by
  apply (Units.eq_mul_inv_iff_mul_eq (p.property m).unit).mpr
  have h := congrArg ((localizationPointEquiv (R := R) (S := S) (L := L) M).symm p).toAlgHom hb
  simpa only [map_mul, toAlgHom_apply, localizationPointEquiv_symm_algebraMap,
    IsUnit.unit_spec] using h

variable [TopologicalSpace S]

/-- Inversion on units with the subspace topology suffices for localization continuity. -/
theorem continuous_localizationPointEquiv_symm [ContinuousMul S]
    (hS : IsEmbedding (Units.val : Sˣ → S)) :
    Continuous ((localizationPointEquiv (R := R) (S := S) (L := L) M).symm) := by
  apply (AlgPoint.continuous_iff _).mpr
  intro b
  obtain ⟨⟨a, m⟩, hb⟩ := IsLocalization.surj M b
  have hu : Continuous (fun p : LocalizationLocus (R := R) (S := S) M =>
      (p.property m).unit) := by
    apply hS.isInducing.continuous_iff.mpr
    simpa only [Function.comp_def, IsUnit.unit_spec] using
      (AlgPoint.continuous_eval (m : A)).comp
        (continuous_subtype_val (p := fun p : AlgPoint R A S => ∀ m : M, IsUnit (p m)))
  have heq : (fun p : LocalizationLocus (R := R) (S := S) M =>
      (localizationPointEquiv (R := R) (S := S) (L := L) M).symm p b) =
      fun p => p.val a * Units.val ((p.property m).unit⁻¹) := by
    funext p
    exact localizationPointEquiv_symm_apply M p b a m hb
  rw [heq]
  exact ((AlgPoint.continuous_eval a).comp continuous_subtype_val).mul
    (Units.continuous_coe_inv.comp hu)

/-- The actual localization point space is homeomorphic to its unit-valued locus. -/
def localizationPointHomeomorph [ContinuousMul S]
    (hS : IsEmbedding (Units.val : Sˣ → S)) :
    AlgPoint R L S ≃ₜ LocalizationLocus (R := R) (S := S) M where
  toEquiv := localizationPointEquiv M
  continuous_toFun := (continuous_precomp (Algebra.algHom R A L)).subtype_mk _
  continuous_invFun := continuous_localizationPointEquiv_symm M hS

omit [TopologicalSpace S] in
/-- The range of restriction from a localization is exactly its unit-valued locus. -/
theorem range_precomp_localization :
    Set.range (precomp (S := S) (Algebra.algHom R A L)) =
      {p : AlgPoint R A S | ∀ m : M, IsUnit (p m)} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact (localizationPointEquiv (R := R) (S := S) (L := L) M q).property
  · intro hp
    exact ⟨(localizationPointEquiv (R := R) (S := S) (L := L) M).symm ⟨p, hp⟩,
      congrArg Subtype.val ((localizationPointEquiv (R := R) (S := S) (L := L) M).apply_symm_apply ⟨p, hp⟩)⟩

include M in
/-- Restriction from a localization is an embedding when units have their subspace topology. -/
theorem isEmbedding_precomp_localization [ContinuousMul S]
    (hS : IsEmbedding (Units.val : Sˣ → S)) :
    IsEmbedding (precomp (S := S) (Algebra.algHom R A L)) :=
  IsEmbedding.subtypeVal.comp
    (localizationPointHomeomorph (R := R) (L := L) M hS).isEmbedding

omit [TopologicalSpace S] in
/-- A point is unit-valued on all powers exactly when it is unit-valued on the generator. -/
theorem unit_powers_iff (f : A) (p : AlgPoint R A S) :
    (∀ m : Submonoid.powers f, IsUnit (p m)) ↔ IsUnit (p f) := by
  constructor
  · intro h
    exact h ⟨f, Submonoid.mem_powers _⟩
  · intro h m
    obtain ⟨k, hk⟩ := m.property
    rw [← hk]
    change IsUnit (p.toAlgHom (f ^ k))
    rw [map_pow]
    exact h.pow k

/-- The principal unit-valued locus is open when units form an open subspace. -/
theorem isOpen_unitLocus [IsOpenUnits S] (f : A) :
    IsOpen {p : AlgPoint R A S | IsUnit (p f)} := by
  change IsOpen ((fun p : AlgPoint R A S => p f) ⁻¹' Set.range (Units.val : Sˣ → S))
  exact (IsOpenUnits.isOpenEmbedding_unitsVal (M := S)).isOpen_range.preimage
    (AlgPoint.continuous_eval f)

/-- Restriction from any actual localization away from one element is an open embedding. -/
theorem isOpenEmbedding_precomp_away [ContinuousMul S] [IsOpenUnits S]
    (f : A) [IsLocalization.Away f L] :
    IsOpenEmbedding (precomp (S := S) (Algebra.algHom R A L)) := by
  refine ⟨isEmbedding_precomp_localization (R := R) (L := L) (M := Submonoid.powers f)
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := S)).isEmbedding, ?_⟩
  rw [range_precomp_localization (R := R) (L := L) (Submonoid.powers f)]
  simpa only [unit_powers_iff] using isOpen_unitLocus (R := R) (S := S) f

end AlgPoint

end Langlands.AlgebraicGeometry.PointTopology
