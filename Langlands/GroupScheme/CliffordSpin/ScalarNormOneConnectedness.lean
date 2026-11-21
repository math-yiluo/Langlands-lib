import Langlands.GroupScheme.CliffordSpin.ReflectionFamilies
import Langlands.GroupScheme.CliffordSpin.GeometricPoints
import Langlands.GroupScheme.FiniteTypeIdentityComponent
import Mathlib.Data.List.Induction

/-! # Connectedness of scalar norm-one orthogonal groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct Matrix

namespace Langlands.GroupScheme.CliffordSpin

open Quaternionic Langlands.QuadraticForm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {F : Type u} [Field F] [CharZero F] [Invertible (2 : F)] {n : ℕ} [NeZero n]
  (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

local notation "τ" => FirstKindInvolution.scalar F
local notation "Q" => Matrix.toQuadraticForm' (FirstKindInvolution.polar τ q)
local notation "b" => Pi.basisFun F (Fin n)
local notation "SO" => FirstKindInvolution.normOneIsometryGroup τ q
local notation "S" => CommRingCat.of F

local instance scalarNormOneAffine : IsAffineHom (SO).X.hom :=
  (FirstKindInvolution.isClosedSubgroup_normOneIsometryAmbientι τ q).isAffineHom

local instance scalarNormOneFiniteType : LocallyOfFiniteType (SO).X.hom :=
  (FirstKindInvolution.isClosedSubgroup_normOneIsometryAmbientι τ q).locallyOfFiniteType

local notation "C" => FiniteTypeIdentityComponent.groupScheme (SO)
local notation "inc" => FiniteTypeIdentityComponent.inclusion (SO)

variable (K : Type u) [Field K] [Algebra F K]

local notation "R" => CommAlgCat.of F K
local notation "qK" => QuadraticForm.baseChange K Q
local notation "W" => K ⊗[F] (Fin n → F)
local notation "action" => matrixAction b K

private theorem exists_componentPoint_reflectionPair (v w : W) (hv : qK v ≠ 0) (hw : qK w ≠ 0) :
    ∃ x : (C).affinePoints R, action (actionMatrix q R (x ≫ (inc).hom.hom)) =
      (reflection qK v hv).toLinearEquiv * (reflection qK w hw).toLinearEquiv := by
  obtain ⟨A, _, _, _, φ₀, φ₁, x, hx₀, hx₁⟩ := exists_reflectionPair_family q K v w hv hw
  let T := (algSpec S).obj (op (CommAlgCat.of F A))
  let U := (algSpec S).obj (op R)
  let t : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  let eval (φ : A →ₐ[F] K) : U ⟶ T := (algSpec S).map (CommAlgCat.ofHom φ).op
  have hpoint : IdentityComponent.identityPoint (SO) ∈ Set.range x.left := by
    refine ⟨(eval φ₀).left t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left]
    change (((SO).affinePointMap (CommAlgCat.ofHom φ₀)) x).left t = _
    rw [hx₀]
    change (toUnit U ≫ η[(SO).X]).left t = _
    exact IdentityComponent.unit_left_apply (SO) _
  have hconn : ConnectedSpace T.left := by
    change ConnectedSpace (Spec (CommRingCat.of A))
    infer_instance
  have hr : Set.range x.left ⊆ Set.range (inc).hom.hom.left := by
    rw [FiniteTypeIdentityComponent.range_identityComponentι]
    exact (isConnected_range x.left.continuous).isPreconnected.subset_connectedComponent hpoint
  let y := FiniteEtaleImage.liftOver (inc).hom.hom x hr
  refine ⟨eval φ₁ ≫ y, ?_⟩
  rw [Category.assoc, FiniteEtaleImage.liftOver_fac]
  exact hx₁

private theorem exists_componentPoint_reflectionWord (l : List {v : W // qK v ≠ 0})
    (h : Even l.length) : ∃ x : (C).affinePoints R,
      action (actionMatrix q R (x ≫ (inc).hom.hom)) = (reflectionWord qK l).toLinearEquiv := by
  induction l using List.twoStepInduction with
  | nil =>
    refine ⟨1, ?_⟩
    rw [MonObj.one_comp, map_one, map_one]
    rfl
  | singleton v =>
    exfalso
    have h' : Even (1 : ℕ) := h
    exact Nat.not_even_one h'
  | cons_cons v w l ih =>
    have hl : Even l.length := by
      simpa only [List.length_cons, Nat.even_add_one, not_not] using h
    obtain ⟨x, hx⟩ := ih hl
    obtain ⟨y, hy⟩ := exists_componentPoint_reflectionPair q K w.val v.val w.property v.property
    refine ⟨x * y, ?_⟩
    rw [MonObj.mul_comp, map_mul, map_mul, hx, hy, reflectionWord_cons, reflectionWord_cons]
    apply LinearEquiv.ext
    intro z
    rfl

/-- The scalar norm-one isometry group of a regular form is connected. -/
theorem connectedSpace_scalarNormOne (hq : (τ).IsNondegenerateQuadratic q) : ConnectedSpace (SO).X.left := by
  have hs : Surjective (inc).hom.hom.left := by
    apply Langlands.AbelianScheme.surjective_of_algClosed_point_lifting
    intro L _ _ s x
    let : Algebra F L := (Spec.preimage s).hom.toAlgebra
    have he : Spec.algebraMap F L = s := Spec.map_preimage s
    revert x
    rw [← he]
    intro x
    change (SO).affinePoints (CommAlgCat.of F L) at x
    let A := CommAlgCat.of F L
    let g := actionMatrix q A x
    have hg := (mem_range_actionMatrix_iff q A g).mp ⟨x, rfl⟩
    let l := matrixAction b L g
    let z : ((Q).baseChange L).IsometryEquiv ((Q).baseChange L) := ⟨l, hg.1⟩
    let : Invertible (2 : L) := (Invertible.map (algebraMap F L) 2).copy 2 (map_ofNat _ _).symm
    let : Module.Finite L (L ⊗[F] (Fin n → F)) := Module.Finite.of_basis ((b).baseChange L)
    have hd : LinearEquiv.det l = 1 := (det_matrixAction b g).trans hg.2
    have hz : z.toLinearEquiv.toLinearMap.det = 1 := by
      simpa only [LinearEquiv.coe_det, Units.val_one] using congrArg Units.val hd
    obtain ⟨word, heven, hword⟩ := exists_even_reflectionWord ((Q).baseChange L)
      (nondegenerate_polar_baseChange q hq L) z hz
    obtain ⟨y, hy⟩ := exists_componentPoint_reflectionWord q L word heven
    refine ⟨y, (actionMatrix_injective q A) ((matrixAction b L).injective ?_)⟩
    rw [hy, hword]
  exact hs.surj.connectedSpace (inc).hom.hom.left.continuous

/-- In characteristic zero the norm-one group of a positive-dimensional regular scalar form is connected. -/
def ScalarNormOneConnectednessStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] [Invertible (2 : F)] (n : ℕ) [NeZero n]
    (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n)),
    (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q →
    ConnectedSpace ((FirstKindInvolution.scalar F).normOneIsometryGroup q).X.left

end Langlands.GroupScheme.CliffordSpin
