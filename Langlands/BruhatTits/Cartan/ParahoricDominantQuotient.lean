import Langlands.BruhatTits.Cartan.DominantQuotient
import Langlands.Geometry.Building.KPParahoric

/-! # The actual dominant centralizer quotient for a parahoric -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.Cartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ParahoricBuildingData G) (ν : cocharacterLattice B.S)

/-- The positive-valuation dominant set in the actual centralizer of `B.i`. -/
abbrev parahoricDominantSet : Set (rationalPoints B.centralizer.Z) :=
  dominantCentralizer B.i ν B.centralizer.s B.centralizer.bijective

/-- The actual dominant set modulo `z' * z⁻¹ ∈ Z(F)^0`.
This is a set quotient, with no normality or invariance premise. -/
abbrev ParahoricDominantQuotient : Type u :=
  RestrictedRightQuotient.Quotient (parahoricDominantSet B ν) B.centralizerZero

/-- The class of an actual dominant centralizer point. -/
def parahoricDominantClass (z : parahoricDominantSet B ν) :
    ParahoricDominantQuotient B ν :=
  RestrictedRightQuotient.mk _ _ z

@[simp]
theorem parahoricDominantClass_eq_iff (z z' : parahoricDominantSet B ν) :
    parahoricDominantClass B ν z = parahoricDominantClass B ν z' ↔
      z'.val * z.val⁻¹ ∈ B.centralizerZero :=
  RestrictedRightQuotient.mk_eq_mk _ _ z z'

variable (x : B.Apartment)

local notation "P" => B.parahoricAt x
local notation "QP" => DoubleCoset.Quotient (P : Set (rationalPoints G)) P

/-- `j(Z(F)^0) ≤ P_x` makes the representative map well-defined on the
restricted right quotient, without a Cartan classification or coverage premise. -/
theorem parahoricDominantRespects :
    RestrictedRightQuotient.Respects (parahoricDominantSet B ν) B.centralizerZero
      (rationalPoints.map B.centralizer.j) P := by
  intro z z' hzz'
  apply DoubleCoset.eq.mpr
  refine ⟨rationalPoints.map B.centralizer.j (z'.val * z.val⁻¹), ?_,
    1, (B.parahoricAt x).one_mem, ?_⟩
  · exact B.map_centralizerZero_le_parahoric {x} ⟨_, hzz', rfl⟩
  · simp only [map_mul, map_inv, mul_one, inv_mul_cancel_right]

/-- The canonical map `[z] ↦ P_x j(z) P_x` from the actual dominant
`Z(F)^0` quotient. Its bijectivity is a separate Cartan assertion. -/
def parahoricDominantDoubleCosetMap : ParahoricDominantQuotient B ν → QP :=
  RestrictedRightQuotient.doubleCosetMap (parahoricDominantSet B ν) B.centralizerZero
    (rationalPoints.map B.centralizer.j) P (parahoricDominantRespects B ν x)

@[simp]
theorem parahoricDominantDoubleCosetMap_class (z : parahoricDominantSet B ν) :
    parahoricDominantDoubleCosetMap B ν x (parahoricDominantClass B ν z) =
      DoubleCoset.mk P P (rationalPoints.map B.centralizer.j z.val) :=
  rfl

/-- Bundle the canonical map as an equivalence after its bijectivity has
been supplied. The representative formula remains the same. -/
def parahoricDominantDoubleCosetEquiv
    (hb : Function.Bijective (parahoricDominantDoubleCosetMap B ν x)) :
    ParahoricDominantQuotient B ν ≃ QP :=
  Equiv.ofBijective _ hb

@[simp]
theorem parahoricDominantDoubleCosetEquiv_class
    (hb : Function.Bijective (parahoricDominantDoubleCosetMap B ν x))
    (z : parahoricDominantSet B ν) :
    parahoricDominantDoubleCosetEquiv B ν x hb (parahoricDominantClass B ν z) =
      DoubleCoset.mk P P (rationalPoints.map B.centralizer.j z.val) :=
  rfl

end Langlands.BruhatTits.Cartan
