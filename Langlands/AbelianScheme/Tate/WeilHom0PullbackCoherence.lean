import Langlands.AbelianScheme.Tate.WeilHom0Pullback

/-! # Coherence of actual rational dual pullback -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} {A B : AbelianScheme S}
  (hA : HasDualScheme A) (hB : HasDualScheme B)
  (geometryA : DualSchemeGeometry A hA) (geometryB : DualSchemeGeometry B hB)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (additivity : DualSchemeMapAdditivity preservation stability A B hA hB)

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "dual0" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hA hB additivity MA evaluationA MB evaluationB geometryA geometryB

local notation "pullAB" => rationalDualPullbackHom0 preservation composition unitCoherence
  associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
  MB evaluationB additivity

/-- For a fixed actual rational map, dual pullback is rational-linear in the
dual-valued homomorphism. -/
def rationalDualPullbackHom0Linear (f : Hom0 A B) : Hom0 B DB →ₗ[ℚ] Hom0 A DA :=
  ((comp0 A DB DA).flip (dual0 f)).comp (comp0 A B DB f)

@[simp] lemma rationalDualPullbackHom0Linear_apply (f : Hom0 A B) (lamB : Hom0 B DB) :
    rationalDualPullbackHom0Linear preservation composition unitCoherence associativity
      comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
      additivity f lamB = pullAB f lamB := rfl

/-- Rational scalar multiplication commutes with actual dual pullback. -/
lemma rationalDualPullbackHom0_smul (f : Hom0 A B) (q : ℚ) (lamB : Hom0 B DB) :
    pullAB f (q • lamB) = q • pullAB f lamB :=
  (rationalDualPullbackHom0Linear preservation composition unitCoherence associativity
    comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
    additivity f).map_smul q lamB

/-- The rational identity pulls a dual-valued homomorphism back to itself. -/
@[simp] lemma rationalDualPullbackHom0_id
    (additivityAA : DualSchemeMapAdditivity preservation stability A A hA hA)
    (lamA : Hom0 A DA) :
    rationalDualPullbackHom0 preservation composition unitCoherence associativity
      comparison symmetry stability hA hA geometryA geometryA MA evaluationA MA evaluationA
      additivityAA (id0 A) lamA = lamA := by
  simp only [rationalDualPullbackHom0, dualHom0_id, id0_comp0, comp0_id0]

/-- The rational identity has unit geometric multiplier. -/
lemma IsRationalDualPullbackMultiple.id
    (additivityAA : DualSchemeMapAdditivity preservation stability A A hA hA)
    (lamA : Hom0 A DA) :
    IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability hA hA geometryA geometryA MA evaluationA MA evaluationA
      additivityAA 1 (id0 A) lamA lamA := by
  simp only [IsRationalDualPullbackMultiple, rationalDualPullbackHom0_id, one_smul]

variable {C : AbelianScheme S}
  (hC : HasDualScheme C) (geometryC : DualSchemeGeometry C hC)
  (MC : LineBundle ((relativeSpace C.X.hom).obj (dualScheme C hC)))
  (evaluationC : tensorObj (poincareFamily C hC).obj.carrier MC.obj ≅
    structureSheaf ((relativeSpace C.X.hom).obj (dualScheme C hC)))
  (additivityBC : DualSchemeMapAdditivity preservation stability B C hB hC)
  (additivityAC : DualSchemeMapAdditivity preservation stability A C hA hC)

local notation "DC" => dualAbelianSchemeFromEvaluation C hC geometryC preservation MC
  evaluationC stability composition unitCoherence associativity comparison symmetry
local notation "pullBC" => rationalDualPullbackHom0 preservation composition unitCoherence
  associativity comparison symmetry stability hB hC geometryB geometryC MB evaluationB
  MC evaluationC additivityBC
local notation "pullAC" => rationalDualPullbackHom0 preservation composition unitCoherence
  associativity comparison symmetry stability hA hC geometryA geometryC MA evaluationA
  MC evaluationC additivityAC

/-- Actual rational dual pullback reverses composition. -/
lemma rationalDualPullbackHom0_comp (f : Hom0 A B) (g : Hom0 B C)
    (lamC : Hom0 C DC) :
    pullAC (comp0 A B C f g) lamC = pullAB f (pullBC g lamC) := by
  simp only [rationalDualPullbackHom0]
  rw [dualHom0_comp preservation composition unitCoherence associativity comparison
    symmetry stability hA hB additivity MA evaluationA MB evaluationB geometryA geometryB
    hC MC evaluationC geometryC additivityBC additivityAC f g]
  simp only [comp0_assoc]

/-- Geometric multiplier equations compose with the product rational multiplier. -/
lemma IsRationalDualPullbackMultiple.comp
    (q r : ℚ) (f : Hom0 A B) (g : Hom0 B C)
    (lamA : Hom0 A DA) (lamB : Hom0 B DB) (lamC : Hom0 C DC)
    (hf : IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
      additivity q f lamA lamB)
    (hg : IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability hB hC geometryB geometryC MB evaluationB MC evaluationC
      additivityBC r g lamB lamC) :
    IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability hA hC geometryA geometryC MA evaluationA MC evaluationC
      additivityAC (q * r) (comp0 A B C f g) lamA lamC := by
  change pullAB f lamB = q • lamA at hf
  change pullBC g lamC = r • lamB at hg
  change pullAC (comp0 A B C f g) lamC = (q * r) • lamA
  rw [rationalDualPullbackHom0_comp preservation composition unitCoherence associativity
    comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
    additivity hC geometryC MC evaluationC additivityBC additivityAC, hg,
    rationalDualPullbackHom0_smul, hf, smul_smul, mul_comm r q]

section Inverse
variable (additivityBA : DualSchemeMapAdditivity preservation stability B A hB hA)
  (additivityBB : DualSchemeMapAdditivity preservation stability B B hB hB)

local notation "pullBA" => rationalDualPullbackHom0 preservation composition unitCoherence
  associativity comparison symmetry stability hB hA geometryB geometryA MB evaluationB
  MA evaluationA additivityBA
local notation "pullBB" => rationalDualPullbackHom0 preservation composition unitCoherence
  associativity comparison symmetry stability hB hB geometryB geometryB MB evaluationB
  MB evaluationB additivityBB

include additivityBB

/-- Pulling back by an isogeny and then by its rational inverse is the identity. -/
lemma rationalDualPullbackHom0_inv_hom (e : Rationalization.of A ≅ Rationalization.of B)
    (lamB : Hom0 B DB) : pullBA e.inv (pullAB e.hom lamB) = lamB := by
  rw [← rationalDualPullbackHom0_comp preservation composition unitCoherence associativity
    comparison symmetry stability hB hA geometryB geometryA MB evaluationB MA evaluationA
    additivityBA hB geometryB MB evaluationB additivity additivityBB]
  have he : comp0 B A B e.inv e.hom = id0 B := e.inv_hom_id
  rw [he, rationalDualPullbackHom0_id]

/-- An inverse rational isogeny has the inverse geometric rational-unit multiplier. -/
lemma IsRationalDualPullbackMultiple.inv (q : ℚˣ)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (lamA : Hom0 A DA) (lamB : Hom0 B DB)
    (hf : IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
      additivity (q : ℚ) e.hom lamA lamB) :
    IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability hB hA geometryB geometryA MB evaluationB MA evaluationA
      additivityBA (q⁻¹ : ℚˣ).val e.inv lamB lamA := by
  change pullAB e.hom lamB = (q : ℚ) • lamA at hf
  change pullBA e.inv lamA = (q⁻¹ : ℚˣ).val • lamB
  have h' : lamB = (q : ℚ) • pullBA e.inv lamA := by
    calc
      lamB = pullBA e.inv (pullAB e.hom lamB) :=
        (rationalDualPullbackHom0_inv_hom preservation composition unitCoherence associativity
          comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
          additivity additivityBA additivityBB e lamB).symm
      _ = _ := by rw [hf, rationalDualPullbackHom0_smul]
  calc
    pullBA e.inv lamA = (q⁻¹ : ℚˣ).val • ((q : ℚ) • pullBA e.inv lamA) := by
      simp [smul_smul]
    _ = (q⁻¹ : ℚˣ).val • lamB := congrArg ((q⁻¹ : ℚˣ).val • ·) h'.symm

end Inverse

end Langlands.AbelianScheme
