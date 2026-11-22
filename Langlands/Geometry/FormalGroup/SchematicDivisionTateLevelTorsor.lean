import Langlands.Geometry.FormalGroup.SchematicDivisionTateLevel

/-! # The order frame torsor at a schematic Tate test -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory Opposite AlgebraicGeometry MulOpposite

namespace Langlands.Shimura.LocalDivision

open Langlands.CentralDivision Langlands.Shimura.PEL

private theorem regularLinearEquiv_apply {O : Type v} [Ring O] (f : O ≃ₗ[O] O) (a : O) :
    f a = a * f 1 :=
  (congrArg f (mul_one a).symm).trans (f.map_smul a 1)

private def regularLinearEquivUnit {O : Type v} [Ring O] (f : O ≃ₗ[O] O) : Oˣ where
  val := f 1
  inv := f.symm 1
  val_inv := (regularLinearEquiv_apply f.symm (f 1)).symm.trans (f.symm_apply_apply 1)
  inv_val := (regularLinearEquiv_apply f (f.symm 1)).symm.trans (f.apply_symm_apply 1)

variable (k : Type u) (D : Type v)
variable [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k] [LocallyCompactSpace k]
variable [DivisionRing D] [Algebra k D] [FiniteDimensional k D]
variable [TopologicalSpace D] [IsModuleTopology k D]

private abbrev integralUnits := (maximalCompactLevel k D).subgroup

/-- With an initial frame, postcomposition by order units gives every other
frame exactly once. -/
theorem right_divisionFrame_bijective {M : Type w} [AddCommGroup M] [Module (integerRing k D) M]
    (e : M ≃ₗ[integerRing k D] integerRing k D) :
    Function.Bijective (fun g : integralUnits k D => right e g) := by
  constructor
  · intro g h hgh
    apply (integralUnitsEquiv k D).injective
    apply Units.ext
    have hv := DFunLike.congr_fun hgh (e.symm 1)
    simpa only [right_divisionFrame_apply, LinearEquiv.apply_symm_apply, one_mul] using hv
  · intro f
    let a := regularLinearEquivUnit (e.symm.trans f)
    refine ⟨(integralUnitsEquiv k D).symm a, ?_⟩
    apply LinearEquiv.ext
    intro x
    rw [right_divisionFrame_apply, MulEquiv.apply_symm_apply]
    change e x * f (e.symm 1) = f x
    simpa only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using
      (regularLinearEquiv_apply (e.symm.trans f) (e x)).symm

variable {R : CommRingCat.{w}} {p : ℕ} [Fact p.Prime] {G : PDivisibleGroup R p}
variable (ρ : integerRing k D →+* End G) (T : Over (Spec R))
variable (uniformizer : Dˣ) (hsmall : regularAbsoluteValue k D (uniformizer : D) < 1)
variable {N : ℕ} (hN : 0 < N)

private abbrev levelSubgroup :=
  (uniformizerLevel k D uniformizer hsmall N hN).subgroup.subgroupOf (integralUnits k D)

/-- A chosen integral trivialization identifies the level fibre with the
published finite quotient by right translation of that trivialization. -/
def schematicTateLevelEquiv (e : SchematicTateFrame k D ρ T) :
    UniformizerLevelQuotient k D uniformizer hsmall N hN ≃
      SchematicTateLevel k D ρ T uniformizer hsmall N hN :=
  Equiv.ofBijective (fun g => schematicTateLevelTranslate k D ρ T uniformizer hsmall hN g
    (schematicTateLevelClass k D ρ T uniformizer hsmall hN e)) (by
    constructor
    · intro a b hab
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
      change schematicTateLevelClass k D ρ T uniformizer hsmall hN (right e g) =
        schematicTateLevelClass k D ρ T uniformizer hsmall hN (right e h) at hab
      obtain ⟨u, hu, he⟩ :=
        (RightOrbit.mk_eq_mk (levelSubgroup k D uniformizer hsmall hN) _ _).mp hab
      rw [right_mul] at he
      have hh : h = g * u := (right_divisionFrame_bijective k D e).1 he
      exact QuotientGroup.eq.mpr (by rwa [hh, inv_mul_cancel_left])
    · intro q
      induction q using Quotient.inductionOn with
      | h f =>
        obtain ⟨g, rfl⟩ := (right_divisionFrame_bijective k D e).2 f
        exact ⟨QuotientGroup.mk g, rfl⟩)

@[simp] theorem schematicTateLevelEquiv_apply (e : SchematicTateFrame k D ρ T)
    (g : UniformizerLevelQuotient k D uniformizer hsmall N hN) :
    schematicTateLevelEquiv k D ρ T uniformizer hsmall hN e g =
      schematicTateLevelTranslate k D ρ T uniformizer hsmall hN g
        (schematicTateLevelClass k D ρ T uniformizer hsmall hN e) := rfl

/-- In the chosen coordinates, the right action is right multiplication on the quotient. -/
theorem schematicTateLevelEquiv_translate (e : SchematicTateFrame k D ρ T)
    (a b : UniformizerLevelQuotient k D uniformizer hsmall N hN) :
    schematicTateLevelEquiv k D ρ T uniformizer hsmall hN e (a * b) =
      schematicTateLevelTranslate k D ρ T uniformizer hsmall hN b
        (schematicTateLevelEquiv k D ρ T uniformizer hsmall hN e a) :=
  mul_smul (MulOpposite.op b) (MulOpposite.op a)
    (schematicTateLevelClass k D ρ T uniformizer hsmall hN e)

/-- The chosen quotient coordinates commute with the published level reduction. -/
theorem schematicTateLevelEquiv_forget {M : ℕ} (hM : 0 < M) (hNM : N ≤ M)
    (e : SchematicTateFrame k D ρ T) (a : UniformizerLevelQuotient k D uniformizer hsmall M hM) :
    schematicTateLevelForget k D ρ T uniformizer hsmall hN hM hNM
        (schematicTateLevelEquiv k D ρ T uniformizer hsmall hM e a) =
      schematicTateLevelEquiv k D ρ T uniformizer hsmall hN e
        (uniformizerLevelTransition k D uniformizer hsmall hM hN hNM a) := by
  simp only [schematicTateLevelEquiv_apply, schematicTateLevelForget_translate,
    schematicTateLevelForget_mk]

theorem finite_schematicTateLevel (e : SchematicTateFrame k D ρ T) :
    Finite (SchematicTateLevel k D ρ T uniformizer hsmall N hN) := by
  have := finite_uniformizerLevelQuotient k D uniformizer hsmall N hN
  exact Finite.of_equiv _ (schematicTateLevelEquiv k D ρ T uniformizer hsmall hN e)

end Langlands.Shimura.LocalDivision
