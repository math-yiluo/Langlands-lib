import Langlands.AbelianScheme.Tate.WeilIntegralPolarizationComparison
import Langlands.AlgebraicGeometry.Picard.RationalPolarizationCompatibility
import Langlands.AbelianScheme.RationalAlgebraAction
import Langlands.CategoryTheory.RationalizationIntegralInverse

/-! # Integral dual pullback and rational action comparisons -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AbelianScheme

namespace RationalAlgebraAction

variable {S : Scheme.{u}} {R : Type v} [Ring R] [Algebra ℚ R]
  {X Y : RationalAlgebraAction S R}

/-- An equivariant rational isomorphism expresses the original action by conjugation. -/
theorem action_eq_conjugate (e : X ≅ Y) (x : R) :
    X.action x = comp0 X.abelianScheme Y.abelianScheme X.abelianScheme (hom0 e.hom)
      (comp0 Y.abelianScheme Y.abelianScheme X.abelianScheme (Y.action x) (hom0 e.inv)) := by
  have he : comp0 X.abelianScheme Y.abelianScheme X.abelianScheme
      (hom0 e.hom) (hom0 e.inv) = id0 X.abelianScheme :=
    (underlyingIso e).hom_inv_id
  calc
    X.action x = comp0 _ _ _ (X.action x) (id0 X.abelianScheme) :=
      (comp0_id0 _).symm
    _ = comp0 _ _ _ (comp0 _ _ _ (X.action x) (hom0 e.hom)) (hom0 e.inv) := by
      rw [comp0_assoc, he]
    _ = _ := by rw [intertwines e.hom x, comp0_assoc]

/-- Injectivity of the whole rational algebra action is preserved by equivariant isomorphisms. -/
theorem action_injective_of_iso (e : X ≅ Y) (h : Function.Injective X.action) :
    Function.Injective Y.action := by
  intro x y hxy
  apply h
  rw [action_eq_conjugate e x, action_eq_conjugate e y, hxy]

theorem action_injective_iff (e : X ≅ Y) :
    Function.Injective X.action ↔ Function.Injective Y.action :=
  ⟨action_injective_of_iso e, action_injective_of_iso e.symm⟩

end RationalAlgebraAction

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

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
  (additivityAB : DualSchemeMapAdditivity preservation stability A B hA hB)

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "dual0AB" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hA hB additivityAB MA evaluationA MB evaluationB geometryA geometryB
local notation "pullAB" => rationalDualPullbackHom0 preservation composition unitCoherence
  associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
  MB evaluationB additivityAB

/-- Alias of the published actual integral contravariant dual pullback. -/
abbrev integralDualPullback (f : A ⟶ B) (lamB : B ⟶ DB) : A ⟶ DA :=
  integralDualPullbackHom preservation composition unitCoherence associativity
    comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
    f lamB

/-- Rationalization of the actual dual composite is the constructed rational dual pullback. -/
theorem homToHom0_integralDualPullback (f : A ⟶ B) (lamB : B ⟶ DB) :
    homToHom0 (integralDualPullback preservation composition unitCoherence associativity
      comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
      f lamB) = pullAB (homToHom0 f) (homToHom0 lamB) := by
  exact (rationalDualPullbackHom0_homToHom0 preservation composition unitCoherence
    associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
    MB evaluationB additivityAB f lamB).symm

/-- Scaling the map scales its dual pullback by the square of the scalar. -/
theorem rationalDualPullbackHom0_smul_map (q : ℚ) (f : Hom0 A B)
    (lamB : Hom0 B DB) :
    pullAB (q • f) lamB = q ^ 2 • pullAB f lamB := by
  simpa only [pow_two] using
    rationalDualPullbackHom0_smul_hom preservation composition unitCoherence
      associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
      MB evaluationB additivityAB q f lamB

variable (additivityAA : DualSchemeMapAdditivity preservation stability A A hA hA)
  (additivityBB : DualSchemeMapAdditivity preservation stability B B hB hB)

local notation "dual0AA" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hA hA additivityAA MA evaluationA MA evaluationA geometryA geometryA
local notation "dual0BB" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hB hB additivityBB MB evaluationB MB evaluationB geometryB geometryB

/-- Pullback preserves the involution equation along an intertwining rational map. -/
theorem IsInvolutionCompatible.rationalDualPullback
    {R : Type v} [Ring R] [StarRing R]
    (iA : R →+* End0 A) (iB : R →+* End0 B) (f : Hom0 A B)
    (hf : ∀ b : R, comp0 A A B (iA b) f = comp0 A B B f (iB b))
    (lamB : Hom0 B DB)
    (hlam : IsInvolutionCompatible preservation composition unitCoherence associativity
      comparison symmetry stability hB additivityBB MB evaluationB geometryB iB lamB) :
    IsInvolutionCompatible preservation composition unitCoherence associativity
      comparison symmetry stability hA additivityAA MA evaluationA geometryA
      iA (pullAB f lamB) := by
  intro b
  have hd : comp0 DB DA DA (dual0AB f) (dual0AA (iA (star b))) =
      comp0 DB DB DA (dual0BB (iB (star b))) (dual0AB f) := by
    have h := congrArg dual0AB (hf (star b))
    rw [dualHom0_comp preservation composition unitCoherence associativity comparison
      symmetry stability hA hA additivityAA MA evaluationA MA evaluationA geometryA geometryA
      hB MB evaluationB geometryB additivityAB additivityAB,
      dualHom0_comp preservation composition unitCoherence associativity comparison
      symmetry stability hA hB additivityAB MA evaluationA MB evaluationB geometryA geometryB
      hB MB evaluationB geometryB additivityBB additivityAB] at h
    exact h
  change comp0 A A DA (iA b) (pullAB f lamB) =
    comp0 A DA DA (pullAB f lamB) (dual0AA (iA (star b)))
  calc
    _ = comp0 A DB DA
        (comp0 A B DB (comp0 A A B (iA b) f) lamB) (dual0AB f) := by
      simp only [rationalDualPullbackHom0, comp0_assoc]
    _ = comp0 A DB DA
        (comp0 A B DB f (comp0 B B DB (iB b) lamB)) (dual0AB f) := by
      rw [hf b]
      simp only [comp0_assoc]
    _ = comp0 A DB DA
        (comp0 A B DB f (comp0 B DB DB lamB (dual0BB (iB (star b)))))
        (dual0AB f) := by rw [hlam b]
    _ = _ := by
      simp only [rationalDualPullbackHom0, comp0_assoc]
      rw [← hd]

variable (additivityBA : DualSchemeMapAdditivity preservation stability B A hB hA)

local notation "pullBA" => rationalDualPullbackHom0 preservation composition unitCoherence
  associativity comparison symmetry stability hB hA geometryB geometryA MB evaluationB
  MA evaluationA additivityBA
local notation "pullAA" => rationalDualPullbackHom0 preservation composition unitCoherence
  associativity comparison symmetry stability hA hA geometryA geometryA MA evaluationA
  MA evaluationA additivityAA

include additivityAA additivityBA

/-- Exact integral inverse-multiple data gives the square rational pullback multiplier. -/
theorem integralInverseData_dualPullback_multiple
    (d : Rationalization.IntegralInverseData A B) (lamA : A ⟶ DA) :
    IsRationalDualPullbackMultiple preservation composition unitCoherence associativity
      comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
      additivityAB ((d.multiple : ℚ) ^ 2) (homToHom0 d.hom) (homToHom0 lamA)
      (homToHom0 (integralDualPullback preservation composition unitCoherence associativity
        comparison symmetry stability hB hA geometryB geometryA MB evaluationB MA evaluationA
        d.inv lamA)) := by
  rw [homToHom0_integralDualPullback preservation composition unitCoherence associativity
    comparison symmetry stability hB hA geometryB geometryA MB evaluationB MA evaluationA
    additivityBA]
  change pullAB (homToHom0 d.hom) (pullBA (homToHom0 d.inv) (homToHom0 lamA)) =
    (d.multiple : ℚ) ^ 2 • homToHom0 lamA
  rw [← rationalDualPullbackHom0_comp preservation composition unitCoherence associativity
    comparison symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
    additivityAB hA geometryA MA evaluationA additivityBA additivityAA,
    comp0_homToHom0, d.hom_inv, map_zsmul, homToHom0_id,
    ← Int.cast_smul_eq_zsmul ℚ, rationalDualPullbackHom0_smul_map,
    rationalDualPullbackHom0_id]

end Langlands.AbelianScheme
