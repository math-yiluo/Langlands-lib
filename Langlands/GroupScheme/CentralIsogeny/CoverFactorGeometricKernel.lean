import Langlands.GroupScheme.CentralIsogeny.GeometricKernelComparison
import Langlands.GroupScheme.DominantHomFlatProof
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeSurjectionProof

/-! # Finite cover factors with surjective geometric kernel maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable {F : Type u} [Field F] [CharZero F]

local notation "S" => Spec (CommRingCat.of F)

variable {G H Q : GroupScheme (Spec (CommRingCat.of F))}
  (p : G ⟶ Q) (r : H ⟶ Q) (a : G ⟶ H)

omit [CharZero F] in
private theorem lift_from_geometricKernel
    {K : Type u} [Field K] [Algebra F K] [IsAlgClosed K]
    (hp : IsIsogeny p) (ha : a ≫ r = p)
    (hk : ∀ y : H.affinePoints (CommAlgCat.of F K), y ≫ r.hom.hom = 1 →
      ∃ x : G.affinePoints (CommAlgCat.of F K), x ≫ p.hom.hom = 1 ∧ x ≫ a.hom.hom = y)
    (y : H.affinePoints (CommAlgCat.of F K)) :
    ∃ x : G.affinePoints (CommAlgCat.of F K), x ≫ a.hom.hom = y := by
  have : IsFinite p.hom.hom.left := hp.1
  have : Surjective p.hom.hom.left := hp.2.2
  have hlift : ∃ x : Spec (CommRingCat.of K) ⟶ G.X.left,
      x ≫ p.hom.hom.left = (y ≫ r.hom.hom).left :=
    Langlands.exists_point_lift_of_locallyOfFiniteType_surjective (K := K)
      p.hom.hom.left (y ≫ r.hom.hom).left
  obtain ⟨x, hx⟩ := hlift
  let x₀ : G.affinePoints (CommAlgCat.of F K) := Over.homMk x (by
    rw [← Over.w p.hom.hom, ← Category.assoc, hx]
    exact Over.w (y ≫ r.hom.hom))
  have hx₀ : x₀ ≫ p.hom.hom = y ≫ r.hom.hom := Over.OverMorphism.ext hx
  have hcomp : a.hom.hom ≫ r.hom.hom = p.hom.hom :=
    congrArg (fun b : G ⟶ Q => b.hom.hom) ha
  let d := y * (x₀ ≫ a.hom.hom)⁻¹
  have hd : d ≫ r.hom.hom = 1 := by
    change (y * (x₀ ≫ a.hom.hom)⁻¹) ≫ r.hom.hom = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hcomp, hx₀, mul_inv_cancel]
  obtain ⟨c, _, hc⟩ := hk d hd
  refine ⟨c * x₀, ?_⟩
  rw [MonObj.mul_comp, hc]
  change (y * (x₀ ≫ a.hom.hom)⁻¹) * (x₀ ≫ a.hom.hom) = y
  exact inv_mul_cancel_right _ _

/-- A factor between finite covers of the same affine group is an isogeny if
its map on kernels is surjective on every algebraically closed field test. -/
theorem isIsogeny_of_coverFactor_geometricKernel_surjective
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
    (hp : IsIsogeny p) (hr : IsIsogeny r) (ha : a ≫ r = p)
    (hk : ∀ (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K]
      (y : H.affinePoints (CommAlgCat.of F K)), y ≫ r.hom.hom = 1 →
      ∃ x : G.affinePoints (CommAlgCat.of F K), x ≫ p.hom.hom = 1 ∧ x ≫ a.hom.hom = y) :
    IsIsogeny a := by
  have : IsFinite r.hom.hom.left := hr.1
  have : IsFinite (a.hom.hom.left ≫ r.hom.hom.left) := by
    change IsFinite (a ≫ r).hom.hom.left
    rw [ha]
    exact hp.1
  have : IsFinite a.hom.hom.left := IsFinite.of_comp a.hom.hom.left r.hom.hom.left
  have lift (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
      (y : Over.mk s ⟶ H.X) : ∃ x : Over.mk s ⟶ G.X, x ≫ a.hom.hom = y := by
    let : Algebra F K := (Spec.preimage s).hom.toAlgebra
    have hs : Spec.algebraMap F K = s := Spec.map_preimage s
    revert y
    rw [← hs]
    intro y
    exact lift_from_geometricKernel p r a hp ha (hk K) y
  have : Surjective a.hom.hom.left :=
    Langlands.AbelianScheme.surjective_of_algClosed_point_lifting a.hom.hom lift
  have hrel : r.hom.hom.left ≫ Q.X.hom = H.X.hom := Over.w r.hom.hom
  have : IsAffineHom H.X.hom := hrel ▸ inferInstance
  have : LocallyOfFiniteType H.X.hom := hrel ▸ inferInstance
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  have : IsReduced H.X.left := AffineCartierSmoothProof.isReduced H
  have : IsDominant a.hom.hom.left := ⟨a.hom.hom.left.surjective.denseRange⟩
  have : Flat a.hom.hom.left := DominantHomFlat.flat_of_isDominant a
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- With equal positive geometric kernel cardinalities, the specified factor
of finite covers is an isomorphism. -/
theorem isIso_of_coverFactor_geometricKernels
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
    (hp : IsIsogeny p) (hr : IsIsogeny r) (ha : a ≫ r = p)
    (hk : ∀ (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K]
      (y : H.affinePoints (CommAlgCat.of F K)), y ≫ r.hom.hom = 1 →
      ∃ x : G.affinePoints (CommAlgCat.of F K), x ≫ p.hom.hom = 1 ∧ x ≫ a.hom.hom = y)
    {K : Type u} [Field K] [Algebra F K] [IsAlgClosed K]
    (hcard : Nat.card (affinePoints (kernel p) (CommAlgCat.of F K)) =
      Nat.card (affinePoints (kernel r) (CommAlgCat.of F K)))
    (hpos : 0 < Nat.card (affinePoints (kernel r) (CommAlgCat.of F K))) :
    IsIso a :=
  (isIsogeny_of_coverFactor_geometricKernel_surjective p r a hp hr ha hk).isIso_of_geometricKernel_card_eq
    p r ha hcard hpos

/-- A factor of two isogenies over a characteristic-zero field is an
isomorphism when it lifts geometric kernel points and the two geometric
kernels have equal positive cardinalities. -/
def CoverFactorGeometricKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F]
    (G H Q : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
    (p : G ⟶ Q) (r : H ⟶ Q) (a : G ⟶ H),
    IsIsogeny p → IsIsogeny r → a ≫ r = p →
    (∀ (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K]
      (y : H.affinePoints (CommAlgCat.of F K)), y ≫ r.hom.hom = 1 →
      ∃ x : G.affinePoints (CommAlgCat.of F K), x ≫ p.hom.hom = 1 ∧ x ≫ a.hom.hom = y) →
    ∀ (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K],
      Nat.card (affinePoints (kernel p) (CommAlgCat.of F K)) =
        Nat.card (affinePoints (kernel r) (CommAlgCat.of F K)) →
      0 < Nat.card (affinePoints (kernel r) (CommAlgCat.of F K)) → IsIso a

omit [CharZero F] in
theorem coverFactorGeometricKernel : CoverFactorGeometricKernelStatement.{u} := by
  intro F _ _ G H Q _ _ p r a hp hr ha hk K _ _ _ hcard hpos
  exact isIso_of_coverFactor_geometricKernels p r a hp hr ha hk hcard hpos

end Langlands.GroupScheme
