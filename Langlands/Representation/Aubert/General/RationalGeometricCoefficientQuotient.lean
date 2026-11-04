import Langlands.Representation.Aubert.General.RationalGeometricStabilizerProjection
import Langlands.Representation.Aubert.General.GeometricIntersectionTransport
import Langlands.Representation.CuspidalSupport.GroupTransport

/-! # Actual source-radical coefficient quotients for rational geometric terms -/

noncomputable section

universe u uG uR uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section Algebra

variable {A : Type uG} [Group A]

private def stabilizerConjugation (PI PJ : Subgroup A) (n : A) :
    (geometricTargetIntersection PI PJ n).subgroupOf PI →* PJ :=
  (Geometric.General.intersectionToSecond PI PJ n⁻¹).comp
    (MulEquiv.subgroupCongr
      (intersectionIn_inv_eq_geometricTarget_subgroupOf PI PJ n).symm).toMonoidHom

private theorem stabilizerConjugation_apply (PI PJ : Subgroup A) (n : A)
    (h : (geometricTargetIntersection PI PJ n).subgroupOf PI) :
    (stabilizerConjugation PI PJ n h : A) = n⁻¹ * h.val.val * n := by
  change n⁻¹ * h.val.val * n⁻¹⁻¹ = _
  rw [inv_inv]

/-- The actual orbit coefficient projects inverse conjugation into the
original inducing Levi, retaining the literal target-side stabilizer. -/
def geometricCoefficientProjection (PI PJ MJ UJ : Subgroup A)
    (dJ : IsSemidirectDecomposition PJ MJ UJ) (n : A) :
    (geometricTargetIntersection PI PJ n).subgroupOf PI →* MJ :=
  dJ.projection.comp (stabilizerConjugation PI PJ n)

@[simp] theorem geometricCoefficientProjection_apply (PI PJ MJ UJ : Subgroup A)
    (dJ : IsSemidirectDecomposition PJ MJ UJ) (n : A)
    (h : (geometricTargetIntersection PI PJ n).subgroupOf PI) :
    geometricCoefficientProjection PI PJ MJ UJ dJ n h =
      dJ.projection ⟨n⁻¹ * h.val.val * n,
        ((mem_geometricTargetIntersection PI PJ n h.val.val).mp h.property).2⟩ := by
  apply congrArg dJ.projection
  exact Subtype.ext (stabilizerConjugation_apply PI PJ n h)

private def kernelSourceEquiv (PI MI UI PJ : Subgroup A)
    (dI : IsSemidirectDecomposition PI MI UI) (n : A) :
    dI.projection.ker.comap
        ((geometricTargetIntersection PI PJ n).subgroupOf PI).subtype ≃*
      (geometricSourceIntersection UI PJ n).subgroupOf PJ where
  toFun x := by
    let q := stabilizerConjugation PI PJ n x.val
    refine ⟨q, (mem_geometricSourceIntersection UI PJ n (q : A)).mpr
      ⟨q.property, ?_⟩⟩
    have hx : x.val.val.val ∈ UI :=
      (dI.projection_eq_one_iff x.val.val).mp x.property
    simpa [q, stabilizerConjugation_apply, mul_assoc] using hx
  invFun y := by
    let a := n * (y.val : A) * n⁻¹
    have ha : a ∈ UI :=
      ((mem_geometricSourceIntersection UI PJ n (y.val : A)).mp y.property).2
    let p : PI := ⟨a, dI.unipotent_le ha⟩
    let h : (geometricTargetIntersection PI PJ n).subgroupOf PI :=
      ⟨p, (mem_geometricTargetIntersection PI PJ n a).mpr
        ⟨p.property, by simp [a, mul_assoc]⟩⟩
    exact ⟨h, (dI.projection_eq_one_iff p).mpr ha⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    simp [stabilizerConjugation_apply, mul_assoc]
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    simp [stabilizerConjugation_apply, mul_assoc]
  map_mul' x y := Subtype.ext (map_mul (stabilizerConjugation PI PJ n) x.val y.val)

private theorem map_kernel_stabilizerConjugation (PI MI UI PJ : Subgroup A)
    (dI : IsSemidirectDecomposition PI MI UI) (n : A) :
    (dI.projection.ker.comap
        ((geometricTargetIntersection PI PJ n).subgroupOf PI).subtype).map
        (stabilizerConjugation PI PJ n) =
      (geometricSourceIntersection UI PJ n).subgroupOf PJ := by
  ext p
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (kernelSourceEquiv PI MI UI PJ dI n ⟨h, hh⟩).property
  · intro hp
    obtain ⟨x, hx⟩ := (kernelSourceEquiv PI MI UI PJ dI n).surjective ⟨p, hp⟩
    exact ⟨x.val, x.property, congrArg Subtype.val hx⟩

private theorem map_geometricCoefficientKernel_to_source (PI MI UI PJ MJ UJ : Subgroup A)
    (dI : IsSemidirectDecomposition PI MI UI)
    (dJ : IsSemidirectDecomposition PJ MJ UJ) (n : A) :
    (dI.projection.ker.comap
        ((geometricTargetIntersection PI PJ n).subgroupOf PI).subtype).map
        (geometricCoefficientProjection PI PJ MJ UJ dJ n) =
      ((geometricSourceIntersection UI PJ n).subgroupOf PJ).map dJ.projection := by
  rw [geometricCoefficientProjection, ← Subgroup.map_map,
    map_kernel_stabilizerConjugation PI MI UI PJ dI n]

private def coefficientCoinvariantsCongr
    {R : Type uR} [CommRing R] {V : Type uV} [AddCommGroup V] [Module R V]
    (σ : Representation R A V) {N K : Subgroup A} (h : N = K) :
    Jacquet.Coinvariants σ N ≃ₗ[R] Jacquet.Coinvariants σ K := by
  subst K
  exact LinearEquiv.refl R _

private theorem coefficientCoinvariantsCongr_mk
    {R : Type uR} [CommRing R] {V : Type uV} [AddCommGroup V] [Module R V]
    (σ : Representation R A V) {N K : Subgroup A} (h : N = K) (v : V) :
    coefficientCoinvariantsCongr σ h (Jacquet.mk σ N v) = Jacquet.mk σ K v := by
  subst K
  rfl

end Algebra

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (I J : Finset (SimpleRoot i ν))
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))

local notation "H" => Subgroup.subgroupOf
  (geometricTargetIntersection (parabolic i ν I) (parabolic i ν J)
    (n : RationalPoint k G.X)) (parabolic i ν I)
local notation "N" => Subgroup.comap (Subgroup.subtype H) (MonoidHom.ker dI.projection)
local notation "S" => Subgroup.subgroupOf
  (geometricSourceIntersection (unipotent i ν I) (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "f" => geometricCoefficientProjection
  (parabolic i ν I) (parabolic i ν J) (levi i ν J) (unipotent i ν J)
  dJ (n : RationalPoint k G.X)

include hStandard hG hi hν hN in
/-- The coefficient image of the actual stabilizer/kernel intersection is
the literal source radical inside the original inducing Levi. -/
theorem map_geometricCoefficientKernel :
    (N).map f = S :=
  (map_geometricCoefficientKernel_to_source
    (parabolic i ν I) (levi i ν I) (unipotent i ν I)
    (parabolic i ν J) (levi i ν J) (unipotent i ν J) dI dJ
    (n : RationalPoint k G.X)).trans
      (map_sourceRadical_eq i ν hStandard hG hi hν hN I J dJ n)

variable {R : Type uR} [CommRing R] {V : Type uV}
  [AddCommGroup V] [Module R V]

/-- The actual kernel-intersection coefficient quotient and the literal
source-radical Jacquet quotient have the same vector classes. -/
def geometricCoefficientQuotientEquiv (σ : Representation R (levi i ν J) V) :
    Jacquet.Coinvariants (σ.comp f) N ≃ₗ[R] Jacquet.Coinvariants σ S :=
  (Jacquet.coinvariantsMapEquiv σ f N).trans
    (coefficientCoinvariantsCongr σ
      (map_geometricCoefficientKernel i ν hStandard hG hi hν hN I J dI dJ n))

@[simp] theorem geometricCoefficientQuotientEquiv_mk
    (σ : Representation R (levi i ν J) V) (v : V) :
    geometricCoefficientQuotientEquiv i ν hStandard hG hi hν hN I J dI dJ n σ
        (Jacquet.mk (σ.comp f) N v) = Jacquet.mk σ S v := by
  simp only [geometricCoefficientQuotientEquiv, LinearEquiv.trans_apply,
    Jacquet.coinvariantsMapEquiv_mk, coefficientCoinvariantsCongr_mk]

@[simp] theorem geometricCoefficientQuotientEquiv_symm_mk
    (σ : Representation R (levi i ν J) V) (v : V) :
    (geometricCoefficientQuotientEquiv i ν hStandard hG hi hν hN I J dI dJ n σ).symm
        (Jacquet.mk σ S v) = Jacquet.mk (σ.comp f) N v := by
  apply (geometricCoefficientQuotientEquiv i ν hStandard hG hi hν hN I J dI dJ n σ).injective
  rw [LinearEquiv.apply_symm_apply, geometricCoefficientQuotientEquiv_mk]

variable {W : Type uW} [AddCommGroup W] [Module R W]

/-- Pullback of the original coefficient intertwiner along the actual orbit
coefficient projection, preserving its linear map. -/
def geometricCoefficientIntertwiner
    {σ : Representation R (levi i ν J) V} {τ : Representation R (levi i ν J) W}
    (T : σ.IntertwiningMap τ) :
    Representation.IntertwiningMap (σ.comp f) (τ.comp f) where
  toLinearMap := T.toLinearMap
  isIntertwining' h := T.isIntertwining' (f h)

/-- The literal quotient comparison commutes with all coefficient maps,
including maps between modules in independent universes. -/
theorem geometricCoefficientQuotientEquiv_natural
    {σ : Representation R (levi i ν J) V} {τ : Representation R (levi i ν J) W}
    (T : σ.IntertwiningMap τ) (z : Jacquet.Coinvariants (σ.comp f) N) :
    geometricCoefficientQuotientEquiv i ν hStandard hG hi hν hN I J dI dJ n τ
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (geometricCoefficientIntertwiner i ν I J dJ n T) N) z) =
      Representation.Coinvariants.map _ _ (Jacquet.restrictMap T S)
        (geometricCoefficientQuotientEquiv i ν hStandard hG hi hν hN I J dI dJ n σ z) := by
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective (σ.comp f) N z
  change geometricCoefficientQuotientEquiv i ν hStandard hG hi hν hN I J dI dJ n τ
      (Jacquet.mk (τ.comp f) N (T v)) =
    Representation.Coinvariants.map _ _ (Jacquet.restrictMap T S)
      (geometricCoefficientQuotientEquiv i ν hStandard hG hi hν hN I J dI dJ n σ
        (Jacquet.mk (σ.comp f) N v))
  rw [geometricCoefficientQuotientEquiv_mk, geometricCoefficientQuotientEquiv_mk]
  rfl

end RationalPointFamily

end Langlands.Aubert.General
