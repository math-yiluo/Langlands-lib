import Langlands.Shimura.PEL.PolarizedWeilLevelClasses

/-! # Multiplier independence of actual polarized level transport -/

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

local notation "LevelIndex" => FiniteAdelicScalarExtensionLevel D V ψ

variable (additivity : PairAdditivity preservation composition unitCoherence associativity
  comparison symmetry stability square universality (S := S) (D := D))

/-- The rational scalar is a witness for compatibility of the same actual
isogeny. It does not alter that isogeny's map on compatible level orbits. -/
theorem levelIso_eq_of_multiplier (X Y : PObj) (K : LevelIndex)
    (q r : ℚˣ) (e : X.actionObj ≅ Y.actionObj)
    (he : Multiple preservation composition unitCoherence associativity comparison
      symmetry stability square universality additivity X Y q e)
    (hf : Multiple preservation composition unitCoherence associativity comparison
      symmetry stability square universality additivity X Y r e) :
    levelIso preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ s hs htor hu additivity
      X Y K q e he =
    levelIso preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ s hs htor hu additivity
      X Y K r e hf := by
  rfl

/-- The identity rational isogeny acts identically for any valid multiplier
witness. No cancellation or nonzero-polarization premise is needed. -/
theorem levelIso_identity_of_multiple (X : PObj) (K : LevelIndex) (q : ℚˣ)
    (he : Multiple preservation composition unitCoherence associativity comparison
      symmetry stability square universality additivity X X q (Iso.refl _)) :
    levelIso preservation composition unitCoherence associativity comparison symmetry
      stability square universality compatibility h V ψ s hs htor hu additivity
      X X K q (Iso.refl _) he = Equiv.refl _ := by
  rw [levelIso_eq_of_multiplier preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h V ψ s hs htor hu
    additivity X X K q 1 (Iso.refl _) he
    (multiple_refl preservation composition unitCoherence associativity comparison
      symmetry stability square universality additivity X)]
  exact levelIso_refl preservation composition unitCoherence associativity comparison
    symmetry stability square universality compatibility h V ψ s hs htor hu additivity X K

end Langlands.Shimura.PEL.PolarizedWeilLevel
