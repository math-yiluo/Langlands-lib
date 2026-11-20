import Langlands.Global.AdelicBlockDeterminantCharacter
import Langlands.Global.AdelicGLStandardCompact
import Langlands.Topology.CompactNormCharacter

/-!
# Levi projection on the adelic compact intersection

The projection of a compact parabolic element lands in the product of the actual
standard compact subgroups of its blocks. The positive half character is one
on this intersection.
-/

noncomputable section

open scoped BigOperators

set_option autoImplicit false

universe u v w

namespace Langlands.Global.AdelicBlockParabolic

open Langlands.GeneralLinear PrimitiveAdelicHeight AdelicBlockDeterminantCharacter

variable {n : ℕ} (B : BlockShape n)

private theorem leviProjection_coordinate_mem_unitary {R : Type v} {A : Type w}
    [CommRing R] [CommRing A] [StarRing A] (f : R →+* A)
    (p : B.parabolic R)
    (hp : (Matrix.GeneralLinearGroup.map f p.val).val ∈ Matrix.unitaryGroup (Fin n) A)
    (i : Fin B.length) :
    (Matrix.GeneralLinearGroup.map f (B.leviProjection R p i)).val ∈
      Matrix.unitaryGroup (Fin (B.size i)) A := by
  let g := Matrix.GeneralLinearGroup.map f p.val
  let b := Matrix.GeneralLinearGroup.map f (B.leviProjection R p i)
  have hg : (g⁻¹).val = star g.val :=
    Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.mp hp)
  have hbi : b⁻¹ = Matrix.GeneralLinearGroup.map f (B.leviProjection R p⁻¹ i) := by
    simp only [b, map_inv, Pi.inv_apply]
  have hb : (b⁻¹).val = star b.val := by
    ext a c
    rw [hbi]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) A =>
      M (B.index i a) (B.index i c)) hg
  change b.val ∈ Matrix.unitaryGroup (Fin (B.size i)) A
  rw [Matrix.mem_unitaryGroup_iff, ← hb, ← Units.val_mul, mul_inv_cancel, Units.val_one]

variable (F : Type u) [Field F] [NumberField F]

omit [NumberField F] in
/-- Extracting a diagonal block of an infinite compact parabolic element preserves
orthogonality or unitarity at each place. -/
theorem leviProjection_mem_standardInfiniteCompact (p : Infinite F B)
    (hp : p.val ∈ standardInfiniteCompact F n) (i : Fin B.length) :
    B.leviProjection (InfiniteAdeles F) p i ∈ standardInfiniteCompact F (B.size i) := by
  obtain ⟨hReal, hComplex⟩ := (mem_standardInfiniteCompact_iff F n p.val).mp hp
  apply (mem_standardInfiniteCompact_iff F (B.size i) _).mpr
  exact ⟨fun z => leviProjection_coordinate_mem_unitary B
      ((realCoord z).comp (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom)
      p (hReal z) i,
    fun z => leviProjection_coordinate_mem_unitary B
      ((complexCoord z).comp (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom)
      p (hComplex z) i⟩

/-- The diagonal block and its inverse have integral entries at every finite place. -/
theorem leviProjection_mem_standardIntegral (p : Finite F B)
    (hp : p.val ∈ FiniteAdelicGL.standardIntegral F n) (i : Fin B.length) :
    B.leviProjection (FiniteAdeles F) p i ∈ FiniteAdelicGL.standardIntegral F (B.size i) := by
  obtain ⟨h, hi⟩ := (FiniteAdelicGL.mem_standardIntegral F n p.val).mp hp
  apply (FiniteAdelicGL.mem_standardIntegral F (B.size i) _).mpr
  refine ⟨fun a b z => h (B.index i a) (B.index i b) z, fun a b z => ?_⟩
  have he : (B.leviProjection (FiniteAdeles F) p i)⁻¹ =
      B.leviProjection (FiniteAdeles F) p⁻¹ i := by rw [map_inv, Pi.inv_apply]
  rw [he]
  exact hi (B.index i a) (B.index i b) z

/-- The full Levi projection sends a compact parabolic matrix to compact matrices in
each diagonal block. -/
theorem leviProjection_mem_standardCompact (p : Full F B)
    (hp : p.val ∈ standardCompact F n) (i : Fin B.length) :
    B.leviProjection (Adeles F) p i ∈ standardCompact F (B.size i) := by
  obtain ⟨hInf, hFin⟩ := (mem_standardCompact_iff F n _).mp hp
  apply (mem_standardCompact_iff F (B.size i) _).mpr
  constructor
  · change leviInfinite F B (B.leviProjection (Adeles F) p) i ∈ _
    rw [← leviProjection_infinite]
    exact leviProjection_mem_standardInfiniteCompact B F (infinite F B p) hInf i
  · change leviFinite F B (B.leviProjection (Adeles F) p) i ∈ _
    rw [← leviProjection_finite]
    exact leviProjection_mem_standardIntegral B F (finite F B p) hFin i

/-- The intersection of the actual parabolic and the standard compact subgroup,
viewed inside the parabolic. -/
def compactIntersection : Subgroup (Full F B) :=
  (standardCompact F n).comap (B.parabolic (Adeles F)).subtype

/-- The Levi projection on the compact intersection takes values in the actual
product of the standard compact block subgroups. -/
def compactLeviProjection : compactIntersection B F →ₜ*
    (∀ i : Fin B.length, standardCompact F (B.size i)) where
  toFun p i := ⟨B.leviProjection (Adeles F) p.val i,
    leviProjection_mem_standardCompact B F p.val p.property i⟩
  map_one' := funext fun i => Subtype.ext (congrFun ((B.leviProjection (Adeles F)).map_one) i)
  map_mul' p q := funext fun i =>
    Subtype.ext (congrFun ((B.leviProjection (Adeles F)).map_mul p.val q.val) i)
  continuous_toFun := continuous_pi fun i =>
    ((continuous_apply i).comp ((B.leviProjectionContinuous (Adeles F)).continuous.comp
      continuous_subtype_val)).subtype_mk _

@[simp]
theorem compactLeviProjection_val (p : compactIntersection B F) (i : Fin B.length) :
    (compactLeviProjection B F p i).val = B.leviProjection (Adeles F) p.val i := rfl

/-- The positive half character is trivial on the compact parabolic intersection. -/
theorem parabolicHalfCharacter_eq_one_of_mem_standardCompact (p : Full F B)
    (hp : p.val ∈ standardCompact F n) : parabolicHalfCharacter F B p = 1 := by
  have h (i : Fin B.length) :
      determinantNorm F (B.size i) (B.leviProjection (Adeles F) p i) = 1 :=
    RankinSelberg.LastRowReduction.eq_one_of_isCompact
      (determinantNorm F (B.size i)).toMonoidHom (determinantNorm F (B.size i)).continuous
      (standardCompact F (B.size i)) (isCompact_standardCompact F (B.size i))
      (leviProjection_mem_standardCompact B F p hp i)
  change leviHalfCharacter F B (B.leviProjection (Adeles F) p) = 1
  rw [leviHalfCharacter_eq_one, leviCharacter_apply]
  simp [h]

end Langlands.Global.AdelicBlockParabolic
