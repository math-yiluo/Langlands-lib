import Langlands.Geometry.FormalGroup.DivisionUniformizerLevelTower
import Langlands.Geometry.FormalGroup.PDivisibleGroupTateOrder
import Langlands.Shimura.PEL.InvariantOrbits
import Mathlib.Algebra.Group.Submonoid.Units

/-! # Division-uniformizer level classes on schematic Tate sections -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory Opposite AlgebraicGeometry MulOpposite

namespace Langlands.Shimura.LocalDivision

open Langlands.CentralDivision Langlands.Shimura.PEL

variable (k : Type u) (D : Type v)
variable [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k] [LocallyCompactSpace k]
variable [DivisionRing D] [Algebra k D] [FiniteDimensional k D]
variable [TopologicalSpace D] [IsModuleTopology k D]

private abbrev integralUnits := (maximalCompactLevel k D).subgroup

/-- The integral compact subgroup is the group of units of the actual order. -/
def integralUnitsEquiv : integralUnits k D ≃* (integerRing k D)ˣ :=
  (integerRing k D).toSubmonoid.unitsEquivUnitsType

@[simp] theorem integralUnitsEquiv_coe (g : integralUnits k D) :
    (((integralUnitsEquiv k D g : (integerRing k D)ˣ) : integerRing k D) : D) =
      ((g : Dˣ) : D) := rfl

/-- On frames directed into the left regular module, units act on the right by
postcomposition with right multiplication. -/
instance divisionFrameRightAction {M : Type w} [AddCommGroup M] [Module (integerRing k D) M] :
    MulAction (integralUnits k D)ᵐᵒᵖ (M ≃ₗ[integerRing k D] integerRing k D) where
  smul g e := e.trans ((integralUnitsEquiv k D g.unop).mulRightLinearEquiv (integerRing k D))
  one_smul e := by
    apply LinearEquiv.ext
    intro x
    change e x * (integralUnitsEquiv k D 1 : (integerRing k D)ˣ) = e x
    rw [map_one, Units.val_one, mul_one]
  mul_smul g h e := by
    apply LinearEquiv.ext
    intro x
    change e x * (integralUnitsEquiv k D (h.unop * g.unop) : (integerRing k D)ˣ) =
      (e x * (integralUnitsEquiv k D h.unop : (integerRing k D)ˣ)) *
        (integralUnitsEquiv k D g.unop : (integerRing k D)ˣ)
    rw [map_mul, Units.val_mul, mul_assoc]

theorem right_divisionFrame_apply {M : Type w} [AddCommGroup M] [Module (integerRing k D) M]
    (e : M ≃ₗ[integerRing k D] integerRing k D) (g : integralUnits k D) (x : M) :
    right e g x = e x * (integralUnitsEquiv k D g : (integerRing k D)ˣ) := rfl

variable {R : CommRingCat.{w}} {p : ℕ} [Fact p.Prime] {G : PDivisibleGroup R p}
variable (ρ : integerRing k D →+* End G) (T : Over (Spec R))
variable (uniformizer : Dˣ) (hsmall : regularAbsoluteValue k D (uniformizer : D) < 1)

/-- An integral order-linear trivialization of the actual schematic Tate section module. -/
abbrev SchematicTateFrame :=
  (PDivisibleGroup.schematicTateModulePresheaf ρ).obj (op T) ≃ₗ[integerRing k D] integerRing k D

private abbrev restrictedLevel (N : ℕ) (hN : 0 < N) :=
  (uniformizerLevel k D uniformizer hsmall N hN).subgroup.subgroupOf (integralUnits k D)

/-- Classes of integral Tate trivializations on the test scheme modulo the
published division-uniformizer subgroup. -/
def SchematicTateLevel (N : ℕ) (hN : 0 < N) :=
  RightOrbit (SchematicTateFrame k D ρ T) (restrictedLevel k D uniformizer hsmall N hN)

variable {N : ℕ} (hN : 0 < N)

/-- The canonical class of an integral Tate trivialization at this level. -/
def schematicTateLevelClass (e : SchematicTateFrame k D ρ T) :
    SchematicTateLevel k D ρ T uniformizer hsmall N hN :=
  RightOrbit.mk (restrictedLevel k D uniformizer hsmall N hN) e

private theorem level_conjugate (g u : integralUnits k D)
    (hu : u ∈ restrictedLevel k D uniformizer hsmall N hN) :
    g⁻¹ * u * g ∈ restrictedLevel k D uniformizer hsmall N hN := by
  let U := restrictedLevel k D uniformizer hsmall N hN
  let hU : U.Normal := inferInstance
  simpa only [inv_inv] using hU.conj_mem u hu g⁻¹

private def levelTranslate (g : integralUnits k D) :
    SchematicTateLevel k D ρ T uniformizer hsmall N hN →
      SchematicTateLevel k D ρ T uniformizer hsmall N hN :=
  RightOrbit.translate g (level_conjugate k D uniformizer hsmall hN g)

/-- Right translation on Tate trivializations depends only on the class of the
unit in the published finite quotient. -/
def schematicTateLevelTranslate (g : UniformizerLevelQuotient k D uniformizer hsmall N hN) :
    SchematicTateLevel k D ρ T uniformizer hsmall N hN →
      SchematicTateLevel k D ρ T uniformizer hsmall N hN :=
  Quotient.lift (levelTranslate k D ρ T uniformizer hsmall hN) (by
    intro g h hgh
    funext q
    induction q using Quotient.inductionOn with
    | h e =>
      apply (RightOrbit.mk_eq_mk _ _ _).mpr
      refine ⟨g⁻¹ * h, (QuotientGroup.leftRel_apply).mp hgh, ?_⟩
      rw [right_mul, mul_inv_cancel_left]) g

@[simp] theorem schematicTateLevelTranslate_mk (g : integralUnits k D)
    (e : SchematicTateFrame k D ρ T) :
    schematicTateLevelTranslate k D ρ T uniformizer hsmall hN (QuotientGroup.mk g)
        (schematicTateLevelClass k D ρ T uniformizer hsmall hN e) =
      schematicTateLevelClass k D ρ T uniformizer hsmall hN (right e g) := rfl

/-- The published finite division unit quotient acts on the level classes on the right. -/
instance schematicTateLevelRightAction :
    MulAction (UniformizerLevelQuotient k D uniformizer hsmall N hN)ᵐᵒᵖ
      (SchematicTateLevel k D ρ T uniformizer hsmall N hN) where
  smul g := schematicTateLevelTranslate k D ρ T uniformizer hsmall hN g.unop
  one_smul q := RightOrbit.translate_one q
  mul_smul g h q := by
    obtain ⟨g', hg⟩ := QuotientGroup.mk_surjective g.unop
    obtain ⟨h', hh⟩ := QuotientGroup.mk_surjective h.unop
    change schematicTateLevelTranslate k D ρ T uniformizer hsmall hN (h.unop * g.unop) q =
      schematicTateLevelTranslate k D ρ T uniformizer hsmall hN g.unop
        (schematicTateLevelTranslate k D ρ T uniformizer hsmall hN h.unop q)
    rw [← hg, ← hh, ← QuotientGroup.mk_mul]
    exact (RightOrbit.translate_comp h' g' (level_conjugate k D uniformizer hsmall hN h')
      (level_conjugate k D uniformizer hsmall hN g') q).symm

/-- A finer published level maps to a coarser level by retaining the same trivialization. -/
def schematicTateLevelForget {M : ℕ} (hM : 0 < M) (hNM : N ≤ M) :
    SchematicTateLevel k D ρ T uniformizer hsmall M hM →
      SchematicTateLevel k D ρ T uniformizer hsmall N hN :=
  RightOrbit.translate 1 fun u hu => by
    rw [inv_one, one_mul, mul_one]
    change (u : Dˣ) ∈ (uniformizerLevel k D uniformizer hsmall N hN).subgroup
    exact uniformizerLevel_antitone k D uniformizer hsmall hM hN hNM hu

@[simp] theorem schematicTateLevelForget_mk {M : ℕ} (hM : 0 < M) (hNM : N ≤ M)
    (e : SchematicTateFrame k D ρ T) :
    schematicTateLevelForget k D ρ T uniformizer hsmall hN hM hNM
        (schematicTateLevelClass k D ρ T uniformizer hsmall hM e) =
      schematicTateLevelClass k D ρ T uniformizer hsmall hN e := by
  change schematicTateLevelClass k D ρ T uniformizer hsmall hN (right e 1) = _
  rw [right_one]

@[simp] theorem schematicTateLevelForget_id
    (q : SchematicTateLevel k D ρ T uniformizer hsmall N hN) :
    schematicTateLevelForget k D ρ T uniformizer hsmall hN hN le_rfl q = q := by
  induction q using Quotient.inductionOn with
  | h e =>
    exact schematicTateLevelForget_mk k D ρ T uniformizer hsmall hN hN le_rfl e

theorem schematicTateLevelForget_comp {L M : ℕ} (hL : 0 < L) (hM : 0 < M)
    (hNM : N ≤ M) (hML : M ≤ L) (q : SchematicTateLevel k D ρ T uniformizer hsmall L hL) :
    schematicTateLevelForget k D ρ T uniformizer hsmall hN hM hNM
        (schematicTateLevelForget k D ρ T uniformizer hsmall hM hL hML q) =
      schematicTateLevelForget k D ρ T uniformizer hsmall hN hL (hNM.trans hML) q := by
  induction q using Quotient.inductionOn with
  | h e =>
    change schematicTateLevelForget k D ρ T uniformizer hsmall hN hM hNM
        (schematicTateLevelForget k D ρ T uniformizer hsmall hM hL hML
          (schematicTateLevelClass k D ρ T uniformizer hsmall hL e)) =
      schematicTateLevelForget k D ρ T uniformizer hsmall hN hL (hNM.trans hML)
        (schematicTateLevelClass k D ρ T uniformizer hsmall hL e)
    simp only [schematicTateLevelForget_mk]

/-- The transition of level classes commutes with the published quotient homomorphism. -/
theorem schematicTateLevelForget_translate {M : ℕ} (hM : 0 < M) (hNM : N ≤ M)
    (g : UniformizerLevelQuotient k D uniformizer hsmall M hM)
    (q : SchematicTateLevel k D ρ T uniformizer hsmall M hM) :
    schematicTateLevelForget k D ρ T uniformizer hsmall hN hM hNM
        (schematicTateLevelTranslate k D ρ T uniformizer hsmall hM g q) =
      schematicTateLevelTranslate k D ρ T uniformizer hsmall hN
        (uniformizerLevelTransition k D uniformizer hsmall hM hN hNM g)
        (schematicTateLevelForget k D ρ T uniformizer hsmall hN hM hNM q) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
  induction q using Quotient.inductionOn with
  | h e =>
    let q := schematicTateLevelClass k D ρ T uniformizer hsmall hM e
    change schematicTateLevelForget k D ρ T uniformizer hsmall hN hM hNM
        (schematicTateLevelTranslate k D ρ T uniformizer hsmall hM (QuotientGroup.mk u) q) =
      schematicTateLevelTranslate k D ρ T uniformizer hsmall hN
        (uniformizerLevelTransition k D uniformizer hsmall hM hN hNM (QuotientGroup.mk u))
        (schematicTateLevelForget k D ρ T uniformizer hsmall hN hM hNM q)
    dsimp only [q]
    simp only [schematicTateLevelForget_mk, schematicTateLevelTranslate_mk,
      uniformizerLevelTransition_mk]

end Langlands.Shimura.LocalDivision
