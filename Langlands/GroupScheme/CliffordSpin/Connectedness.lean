import Langlands.GroupScheme.CliffordSpin.CentralIsogeny
import Langlands.GroupScheme.CliffordSpin.SplitPlaneFamily
import Langlands.GroupScheme.FiniteTypeIdentityComponent
import Langlands.GroupScheme.CentralIsogeny.SemisimpleTransfer
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-! # Connectedness of the scalar Clifford lift group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CliffordSpin

open Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

variable {F : Type u} [Field F] [CharZero F] [Invertible (2 : F)] {n : ℕ} [NeZero n]
  (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

local notation "τ" => FirstKindInvolution.scalar F
local notation "Q" => Matrix.toQuadraticForm' (FirstKindInvolution.polar τ q)
local notation "b" => Pi.basisFun F (Fin n)
local notation "P" => groupScheme Q b
local notation "SO" => FirstKindInvolution.normOneIsometryGroup τ q
local notation "π" => projection q
local notation "S" => CommRingCat.of F

local instance scalarNormOne_affineHom : IsAffineHom (SO).X.hom :=
  (FirstKindInvolution.isClosedSubgroup_normOneIsometryAmbientι τ q).isAffineHom

private theorem exists_scalarPoint_of_projection_eq_one (hq : (τ).IsNondegenerateQuadratic q)
    (K : Type u) [Field K] [Algebra F K]
    (x : (P).affinePoints (CommAlgCat.of F K)) (hx : x ≫ (π).hom.hom = 1) :
    ∃ t : rootsOfUnity 2 K, scalarPoint q K t = x := by
  let A := CommAlgCat.of F K
  let T := (algSpec S).obj (op A)
  let y := (kernelPointsEquiv (π) T).symm ⟨x, hx⟩
  have hy : y ≫ (kernelι (π)).hom.hom = x :=
    congrArg Subtype.val ((kernelPointsEquiv (π) T).apply_symm_apply ⟨x, hx⟩)
  let e := kernelIso q hq
  let a := y ≫ e.hom.hom.hom
  use mu.affinePointsEquiv 2 T.hom a
  apply (affinePairEquiv Q b A).injective
  rw [show affinePairEquiv Q b A (scalarPoint q K (mu.affinePointsEquiv 2 T.hom a)) =
    scalarPair Q K (mu.affinePointsEquiv 2 T.hom a) from MulEquiv.apply_symm_apply _ _]
  have h := affinePair_kernelIso_inv q hq A a
  have ha : a ≫ e.inv.hom.hom = y := by
    change y ≫ e.hom.hom.hom ≫ e.inv.hom.hom = y
    rw [← Grp.comp_hom_hom, e.hom_inv_id]
    rfl
  rw [ha, hy] at h
  exact h.symm

private abbrev component := FiniteTypeIdentityComponent.groupScheme (P)
private abbrev componentInclusion := FiniteTypeIdentityComponent.inclusion (P)

omit [NeZero n] in
private theorem scalarPoint_factors_component (hq : (τ).IsNondegenerateQuadratic q) (hn : 2 ≤ n)
    (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K] (t : rootsOfUnity 2 K) :
    ∃ y : (component q).affinePoints (CommAlgCat.of F K),
      y ≫ (componentInclusion q).hom.hom = scalarPoint q K t := by
  let A := LaurentPolynomial K
  let T := (algSpec S).obj (op (CommAlgCat.of F A))
  let R := (algSpec S).obj (op (CommAlgCat.of F K))
  let v : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  let eval (s : Kˣ) : R ⟶ T := (algSpec S).map (CommAlgCat.ofHom (evaluateLaurent K s)).op
  obtain ⟨x, hx⟩ := exists_laurentPoint_through_scalarKernel q K hq hn
  have he (r : rootsOfUnity 2 K) : eval r.val ≫ x = scalarPoint q K r := hx r
  have h1 : eval 1 ≫ x = 1 := (he 1).trans (scalarPoint_one q K)
  have hpoint : (IdentityComponent.identityPoint (P)) ∈ Set.range x.left := by
    refine ⟨(eval 1).left v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h1]
    change (toUnit R ≫ η[(P).X]).left v = _
    exact IdentityComponent.unit_left_apply (P) _
  have hconn : ConnectedSpace T.left := by
    change ConnectedSpace (Spec (CommRingCat.of A))
    infer_instance
  have hr : Set.range x.left ⊆ Set.range (componentInclusion q).hom.hom.left := by
    rw [FiniteTypeIdentityComponent.range_identityComponentι]
    exact (isConnected_range x.left.continuous).isPreconnected.subset_connectedComponent hpoint
  let y := FiniteEtaleImage.liftOver (componentInclusion q).hom.hom x hr
  refine ⟨eval t.val ≫ y, ?_⟩
  rw [Category.assoc, FiniteEtaleImage.liftOver_fac, he]

/-- Once the target norm-one group is connected, the scalar Clifford lift group is
connected in dimension at least two. The full kernel lies in its identity component. -/
theorem connectedSpace_groupScheme_of_connected (hq : (τ).IsNondegenerateQuadratic q) (hn : 2 ≤ n)
    (hSO : ConnectedSpace (SO).X.left) : ConnectedSpace (P).X.left := by
  let i := componentInclusion q
  let r := i ≫ (π)
  let : ConnectedSpace (SO).X.left := hSO
  let : LocallyOfFiniteType (SO).X.hom :=
    (FirstKindInvolution.isClosedSubgroup_normOneIsometryAmbientι τ q).locallyOfFiniteType
  have hπ := isCentralIsogeny_projection q hq
  let : IsFinite (π).hom.hom.left := hπ.isFinite
  let : Flat (π).hom.hom.left := hπ.flat
  let : Surjective r.hom.hom.left :=
    (FiniteTypeIdentityComponent.inclusion_comp_flat_surjective (P) (π)).2
  let : IsFinite r.hom.hom.left := by
    change IsFinite (i.hom.hom.left ≫ (π).hom.hom.left)
    infer_instance
  have hj : Surjective i.hom.hom.left := by
    apply Langlands.AbelianScheme.surjective_of_algClosed_point_lifting
    intro K _ _ s x
    let : Algebra F K := (Spec.preimage s).hom.toAlgebra
    have hs : Spec.algebraMap F K = s := Spec.map_preimage s
    revert x
    rw [← hs]
    intro x
    change (P).affinePoints (CommAlgCat.of F K) at x
    obtain ⟨y, hy⟩ := Langlands.exists_point_lift_of_locallyOfFiniteType_surjective
      r.hom.hom.left (x ≫ (π).hom.hom).left
    let y₀ : (component q).affinePoints (CommAlgCat.of F K) := Over.homMk y (by
      rw [← Over.w r.hom.hom, ← Category.assoc, hy]
      exact Over.w (x ≫ (π).hom.hom))
    have hy₀ : (y₀ ≫ i.hom.hom) ≫ (π).hom.hom = x ≫ (π).hom.hom := by
      apply Over.OverMorphism.ext
      rw [Category.assoc, ← Grp.comp_hom_hom, Over.comp_left]
      exact hy
    let z := x * (y₀ ≫ i.hom.hom)⁻¹
    have hz : z ≫ (π).hom.hom = 1 := by
      change (x * (y₀ ≫ i.hom.hom)⁻¹) ≫ (π).hom.hom = 1
      rw [MonObj.mul_comp, GrpObj.inv_comp, hy₀, mul_inv_cancel]
    obtain ⟨t, ht⟩ := exists_scalarPoint_of_projection_eq_one q hq K z hz
    obtain ⟨v, hv⟩ := scalarPoint_factors_component q hq hn K t
    refine ⟨v * y₀, ?_⟩
    rw [MonObj.mul_comp, hv, ht]
    change (x * (y₀ ≫ i.hom.hom)⁻¹) * (y₀ ≫ i.hom.hom) = x
    rw [mul_assoc, inv_mul_cancel, mul_one]
  exact hj.surj.connectedSpace i.hom.hom.left.continuous

/-- For a semisimple norm-one isometry group the scalar Clifford lift group is semisimple. -/
theorem isSemisimple_groupScheme (hq : (τ).IsNondegenerateQuadratic q) (hn : 2 ≤ n)
    (hSO : IsSemisimple (SO)) : IsSemisimple (P) := by
  have hs : Smooth (P).X.hom := affineCartierSmooth F (P) inferInstance inferInstance
  exact IsSemisimple.of_isCentralIsogeny (π) (isCentralIsogeny_projection q hq) hSO hs
    (connectedSpace_groupScheme_of_connected q hq hn hSO.isConnectedReductive.connectedSpace)

/-- Connectedness of the norm-one isometry group implies connectedness of the associated
Clifford lift group for regular scalar forms of dimension at least two. -/
def ScalarCliffordConnectednessStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] [Invertible (2 : F)] (n : ℕ) [NeZero n]
    (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n)),
    (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q → 2 ≤ n →
    ConnectedSpace ((FirstKindInvolution.scalar F).normOneIsometryGroup q).X.left →
    ConnectedSpace (groupScheme ((FirstKindInvolution.scalar F).polar q).toQuadraticForm'
      (Pi.basisFun F (Fin n))).X.left

end Langlands.GroupScheme.CliffordSpin
