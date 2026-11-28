import Langlands.Shimura.PEL.PolarizedWeilLevelClasses

/-! # Composition of explicit witnesses of the polarized isogeny relation -/

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.Shimura.PEL.PolarizedWeilLevel

open Langlands.AbelianScheme Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (square : MumfordBundlePicardZeroStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (S : Scheme.{u}) (D : Type v) [Ring D] [Algebra ℚ D] [StarRing D]

local notation "PObj" => PolarizedAction preservation composition unitCoherence
  associativity comparison symmetry stability square universality S D

variable {S D}
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]
  [QuasiSeparatedSpace S]

local notation "tower" => levelTower preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu
local notation "LevelIndex" => FiniteAdelicScalarExtensionLevel D V ψ

local notation "Data" => LevelData preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu

variable (additivity : PairAdditivity preservation composition unitCoherence associativity
  comparison symmetry stability square universality (S := S) (D := D))

local notation "Mult" => Multiple preservation composition unitCoherence associativity
  comparison symmetry stability square universality additivity

local notation "transport" => levelIso preservation composition unitCoherence associativity
  comparison symmetry stability square universality compatibility h V ψ s hs htor hu additivity


/-- Witnesses of the polarized isogeny relation compose: the composite rational
isomorphism, with the product multiplier, relates the outer representatives. -/
theorem witness_trans {K : LevelIndex} {x y z : Data K} {q r : ℚˣ}
    {e : x.1.actionObj ≅ y.1.actionObj} {f : y.1.actionObj ≅ z.1.actionObj}
    (hxy : ∃ he : Mult x.1 y.1 q e, transport x.1 y.1 K q e he x.2 = y.2)
    (hyz : ∃ hf : Mult y.1 z.1 r f, transport y.1 z.1 K r f hf y.2 = z.2) :
    ∃ hef : Mult x.1 z.1 (q * r) (e.trans f),
      transport x.1 z.1 K (q * r) (e.trans f) hef x.2 = z.2 := by
  obtain ⟨he, h1⟩ := hxy
  obtain ⟨hf, h2⟩ := hyz
  refine ⟨multiple_trans preservation composition unitCoherence associativity comparison
    symmetry stability square universality additivity he hf, ?_⟩
  rw [levelIso_trans, Equiv.trans_apply, h1, h2]
  · exact he
  · exact hf

/-- The inverse of a witness, with the inverse multiplier, is a witness. -/
theorem witness_symm {K : LevelIndex} {x y : Data K} {q : ℚˣ}
    {e : x.1.actionObj ≅ y.1.actionObj}
    (hxy : ∃ he : Mult x.1 y.1 q e, transport x.1 y.1 K q e he x.2 = y.2) :
    ∃ he' : Mult y.1 x.1 q⁻¹ e.symm, transport y.1 x.1 K q⁻¹ e.symm he' y.2 = x.2 := by
  obtain ⟨he, h1⟩ := hxy
  refine ⟨multiple_symm preservation composition unitCoherence associativity comparison
    symmetry stability square universality additivity he, ?_⟩
  rw [← levelIso_symm, ← h1, Equiv.symm_apply_apply]
  exact he

end Langlands.Shimura.PEL.PolarizedWeilLevel
