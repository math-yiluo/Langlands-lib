import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# The scalar graph quotient over PGL₂

The graph of a character on scalar units gives a central extension of the
projective group of invertible two-by-two matrices. This is the point-group
construction underlying the example of Gan and Gao, §4.6.
-/

namespace Langlands.Covering.BrylinskiDeligne.PGL2ScalarGraph

open Matrix

variable {R A : Type*} [CommRing R] [CommGroup A] (c : Rˣ →* A)

/-- The subgroup of pairs `(uI, c u)` indexed by the scalar units. -/
def graph : Subgroup (GL (Fin 2) R × A) :=
  ((GeneralLinearGroup.scalar (Fin 2)).prod c).range

theorem graph_le_center : graph c ≤ Subgroup.center (GL (Fin 2) R × A) := by
  rintro _ ⟨u, rfl⟩
  refine Subgroup.mem_center_iff.mpr fun g ↦ ?_
  exact Prod.ext (GeneralLinearGroup.scalar_commute u g.1).symm (mul_comm g.2 (c u))

instance : (graph c).Normal := Subgroup.normal_of_le_center (graph_le_center c)

/-- The group of classes of pairs in `GL₂(R) × A` modulo the scalar graph. -/
abbrev Extension := (GL (Fin 2) R × A) ⧸ graph c

/-- The quotient homomorphism from `GL₂(R) × A`. -/
def mk : GL (Fin 2) R × A →* Extension c := QuotientGroup.mk' (graph c)

theorem mk_surjective : Function.Surjective (mk c) := QuotientGroup.mk'_surjective _

/-- Include `A` by sending `a` to the class of `(1, a)`. -/
def inclusion : A →* Extension c := (mk c).comp (MonoidHom.inr _ _)

theorem inclusion_injective : Function.Injective (inclusion c) := by
  refine (injective_iff_map_eq_one (inclusion c)).mpr fun a ha ↦ ?_
  obtain ⟨u, hu⟩ : (1, a) ∈ graph c := (QuotientGroup.eq_one_iff _).mp ha
  have hscalar : GeneralLinearGroup.scalar (Fin 2) u = 1 := congrArg Prod.fst hu
  have hcoef : c u = a := congrArg Prod.snd hu
  have hu_one : u = 1 := by
    apply Units.ext
    simpa using congrArg (fun g : GL (Fin 2) R ↦ (g : Matrix (Fin 2) (Fin 2) R) 0 0) hscalar
  simpa [hu_one] using hcoef.symm

theorem inclusion_le_center : (inclusion c).range ≤ Subgroup.center (Extension c) := by
  rintro _ ⟨a, rfl⟩
  refine Subgroup.mem_center_iff.mpr fun x ↦ ?_
  obtain ⟨⟨g, b⟩, rfl⟩ := mk_surjective c x
  change mk c (g, b) * mk c (1, a) = mk c (1, a) * mk c (g, b)
  simp [← map_mul, mul_comm b a]

/-- Project to the class of the first coordinate in Mathlib's `PGL₂(R)`. -/
def projection : Extension c →* ProjGenLinGroup (Fin 2) R :=
  QuotientGroup.lift (graph c) (ProjGenLinGroup.mk.comp (MonoidHom.fst _ _)) (by
    rintro _ ⟨u, rfl⟩
    exact ProjGenLinGroup.mk_scalar u)

@[simp]
theorem projection_mk (g : GL (Fin 2) R) (a : A) :
    projection c (mk c (g, a)) = ProjGenLinGroup.mk g := rfl

@[simp]
theorem projection_inclusion (a : A) : projection c (inclusion c a) = 1 := rfl

theorem projection_surjective : Function.Surjective (projection c) := by
  intro x
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
  exact ⟨mk c (g, 1), rfl⟩

/-- A scalar first coordinate contributes the inverse of its character value. -/
@[simp]
theorem mk_scalar (u : Rˣ) (a : A) :
    mk c (GeneralLinearGroup.scalar (Fin 2) u, a) = inclusion c (a * (c u)⁻¹) := by
  symm
  change QuotientGroup.mk' (graph c) (1, a * (c u)⁻¹) =
    QuotientGroup.mk' (graph c) (GeneralLinearGroup.scalar (Fin 2) u, a)
  refine (QuotientGroup.mk'_eq_mk' (graph c)).mpr
    ⟨(GeneralLinearGroup.scalar (Fin 2) u, c u), ⟨u, rfl⟩, ?_⟩
  simp

theorem mk_scalar_one (u : Rˣ) :
    mk c (GeneralLinearGroup.scalar (Fin 2) u, 1) = inclusion c (c u)⁻¹ := by
  rw [mk_scalar, one_mul]

theorem ker_projection : (projection c).ker = (inclusion c).range := by
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨g, a⟩, rfl⟩ := mk_surjective c x
    have hg : ProjGenLinGroup.mk g = 1 := hx
    obtain ⟨u, rfl⟩ : g ∈ (GeneralLinearGroup.scalar (Fin 2)).range := by
      rw [← GeneralLinearGroup.center_eq_range_scalar]
      exact ProjGenLinGroup.mk_eq_one.mp hg
    exact ⟨a * (c u)⁻¹, (mk_scalar c u a).symm⟩
  · rintro _ ⟨a, rfl⟩
    exact projection_inclusion c a

/-- The short exact sequence with central inclusion `inclusion c`. -/
def groupExtension : GroupExtension A (Extension c) (ProjGenLinGroup (Fin 2) R) where
  inl := inclusion c
  rightHom := projection c
  inl_injective := inclusion_injective c
  range_inl_eq_ker_rightHom := (ker_projection c).symm
  rightHom_surjective := projection_surjective c

/-- The invertible matrix with rows `(0, u)` and `(1, 0)`. -/
def swapMatrix (u : Rˣ) : GL (Fin 2) R :=
  ⟨!![0, (u : R); 1, 0], !![0, 1; (↑(u⁻¹) : R), 0],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

@[simp]
theorem coe_swapMatrix (u : Rˣ) :
    (swapMatrix u : Matrix (Fin 2) (Fin 2) R) = !![0, (u : R); 1, 0] := rfl

theorem swapMatrix_sq (u : Rˣ) : swapMatrix u ^ 2 = GeneralLinearGroup.scalar (Fin 2) u := by
  apply GeneralLinearGroup.ext
  intro i j
  simp only [pow_two, GeneralLinearGroup.coe_mul, coe_swapMatrix, Matrix.mul_fin_two,
    zero_mul, mul_zero, zero_add, add_zero, mul_one, one_mul, GeneralLinearGroup.coe_scalar]
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

/-- The lift of the projective class of `swapMatrix u` with coefficient `1`. -/
def swapLift (u : Rˣ) : Extension c := mk c (swapMatrix u, 1)

@[simp]
theorem projection_swapLift (u : Rˣ) :
    projection c (swapLift c u) = ProjGenLinGroup.mk (swapMatrix u) := rfl

theorem swapLift_sq (u : Rˣ) : swapLift c u ^ 2 = inclusion c (c u)⁻¹ := by
  rw [swapLift, ← map_pow]
  change mk c (swapMatrix u ^ 2, (1 : A) ^ 2) = _
  rw [swapMatrix_sq, one_pow, mk_scalar_one]

section ChangeOfRings

variable {S : Type*} [CommRing S] (f : R →+* S) (d : Sˣ →* A)

/-- Map the quotient for the restricted character to the quotient over the target ring. -/
def map : Extension (d.comp (Units.map f.toMonoidHom)) →* Extension d :=
  QuotientGroup.map _ _ ((GeneralLinearGroup.map f).prodMap (MonoidHom.id A)) (by
    rintro _ ⟨u, rfl⟩
    refine ⟨Units.map f.toMonoidHom u, Prod.ext ?_ rfl⟩
    exact (GeneralLinearGroup.map_scalar f u).symm)

@[simp]
theorem map_mk (g : GL (Fin 2) R) (a : A) :
    map f d (mk (d.comp (Units.map f.toMonoidHom)) (g, a)) =
      mk d (GeneralLinearGroup.map f g, a) := rfl

@[simp]
theorem map_inclusion (a : A) :
    map f d (inclusion (d.comp (Units.map f.toMonoidHom)) a) = inclusion d a := by
  change mk d (GeneralLinearGroup.map f 1, a) = mk d (1, a)
  rw [map_one]

@[simp]
theorem projection_map (x : Extension (d.comp (Units.map f.toMonoidHom))) :
    projection d (map f d x) =
      ProjGenLinGroup.map f (projection (d.comp (Units.map f.toMonoidHom)) x) := by
  obtain ⟨⟨g, a⟩, rfl⟩ := mk_surjective (d.comp (Units.map f.toMonoidHom)) x
  rfl

@[simp]
theorem map_swapMatrix (u : Rˣ) :
    GeneralLinearGroup.map f (swapMatrix u) = swapMatrix (Units.map f.toMonoidHom u) := by
  apply GeneralLinearGroup.ext
  intro i j
  change f ((swapMatrix u : Matrix (Fin 2) (Fin 2) R) i j) =
    (swapMatrix (Units.map f.toMonoidHom u) : Matrix (Fin 2) (Fin 2) S) i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem map_swapLift (u : Rˣ) :
    map f d (swapLift (d.comp (Units.map f.toMonoidHom)) u) =
      swapLift d (Units.map f.toMonoidHom u) := by
  rw [swapLift, map_mk, map_swapMatrix]
  rfl

end ChangeOfRings

end Langlands.Covering.BrylinskiDeligne.PGL2ScalarGraph
