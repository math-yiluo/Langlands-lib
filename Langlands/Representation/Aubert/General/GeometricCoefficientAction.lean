import Langlands.Representation.Aubert.General.RationalGeometricCoefficientQuotient

/-! # The actual target section and the source coefficient action -/

noncomputable section

universe u uG uR uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section Algebra

variable {A : Type uG} [Group A]

/-- Inverse conjugation between the literal intersection Levis, retaining
both of their original subgroup restrictions. -/
def geometricIntersectionSubgroupEquiv (MI MJ : Subgroup A) (n : A) :
    (geometricTargetIntersection MI MJ n).subgroupOf MI ≃*
      (geometricSourceIntersection MI MJ n).subgroupOf MJ :=
  (MulEquiv.subgroupCongr
    (intersectionIn_inv_eq_geometricTarget_subgroupOf MI MJ n).symm).trans
      ((Geometric.General.intersectionEquiv MJ MI n).symm.trans
        (MulEquiv.subgroupCongr
          (intersectionIn_eq_geometricSource_subgroupOf MI MJ n)))

@[simp] theorem geometricIntersectionSubgroupEquiv_apply
    (MI MJ : Subgroup A) (n : A)
    (l : (geometricTargetIntersection MI MJ n).subgroupOf MI) :
    (geometricIntersectionSubgroupEquiv MI MJ n l).val.val = n⁻¹ * l.val.val * n :=
  Geometric.General.intersectionEquiv_symm_apply MJ MI n _

@[simp] theorem geometricIntersectionSubgroupEquiv_symm_apply
    (MI MJ : Subgroup A) (n : A)
    (l : (geometricSourceIntersection MI MJ n).subgroupOf MJ) :
    ((geometricIntersectionSubgroupEquiv MI MJ n).symm l).val.val =
      n * l.val.val * n⁻¹ :=
  Geometric.General.intersectionEquiv_apply MJ MI n _

/-- The actual target intersection embeds in the orbit stabilizer through
the original ambient Levi section. -/
def geometricCoefficientSection (PI MI UI PJ : Subgroup A)
    (dI : IsSemidirectDecomposition PI MI UI) (n : A) :
    (geometricTargetIntersection MI PJ n).subgroupOf MI →*
      (geometricTargetIntersection PI PJ n).subgroupOf PI where
  toFun l := ⟨⟨l.val, dI.levi_le l.val.property⟩,
    dI.levi_le l.val.property, l.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem geometricCoefficientSection_apply (PI MI UI PJ : Subgroup A)
    (dI : IsSemidirectDecomposition PI MI UI) (n : A)
    (l : (geometricTargetIntersection MI PJ n).subgroupOf MI) :
    (geometricCoefficientSection PI MI UI PJ dI n l).val.val = l.val.val := rfl

/-- Project inside the actual target intersection, then use inverse
conjugation to its literal source Levi. -/
def geometricCoefficientLeviMap (MI PJ MJ UJ : Subgroup A) (n : A)
    (hTarget : IsSemidirectDecomposition
      ((geometricTargetIntersection MI PJ n).subgroupOf MI)
      ((geometricTargetIntersection MI MJ n).subgroupOf MI)
      ((geometricTargetIntersection MI UJ n).subgroupOf MI)) :
    (geometricTargetIntersection MI PJ n).subgroupOf MI →*
      (geometricSourceIntersection MI MJ n).subgroupOf MJ :=
  (geometricIntersectionSubgroupEquiv MI MJ n).toMonoidHom.comp hTarget.projection

/-- The original inducing projection on the target section is exactly the
intersection projection followed by inverse conjugation. -/
theorem geometricCoefficientProjection_section
    (PI MI UI PJ MJ UJ : Subgroup A)
    (dI : IsSemidirectDecomposition PI MI UI)
    (dJ : IsSemidirectDecomposition PJ MJ UJ) (n : A)
    (hTarget : IsSemidirectDecomposition
      ((geometricTargetIntersection MI PJ n).subgroupOf MI)
      ((geometricTargetIntersection MI MJ n).subgroupOf MI)
      ((geometricTargetIntersection MI UJ n).subgroupOf MI))
    (l : (geometricTargetIntersection MI PJ n).subgroupOf MI) :
    geometricCoefficientProjection PI PJ MJ UJ dJ n
        (geometricCoefficientSection PI MI UI PJ dI n l) =
      (geometricCoefficientLeviMap MI PJ MJ UJ n hTarget l : MJ) := by
  rw [geometricCoefficientProjection_apply]
  apply (dJ.projection_eq_iff _ _).mpr
  have hu := hTarget.projection_inv_mul_mem l
  change (hTarget.projection l).val.val⁻¹ * l.val.val ∈
    geometricTargetIntersection MI UJ n at hu
  have hu' := ((mem_geometricTargetIntersection MI UJ n _).mp hu).2
  change (geometricIntersectionSubgroupEquiv MI MJ n (hTarget.projection l)).val.val⁻¹ *
    (n⁻¹ * l.val.val * n) ∈ UJ
  rw [geometricIntersectionSubgroupEquiv_apply]
  simpa [mul_assoc] using hu'

end Algebra

section Topology

variable {A : Type uG} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]

/-- The actual intersection conjugation preserves the induced topologies. -/
def geometricIntersectionSubgroupContinuousEquiv (MI MJ : Subgroup A) (n : A) :
    (geometricTargetIntersection MI MJ n).subgroupOf MI ≃ₜ*
      (geometricSourceIntersection MI MJ n).subgroupOf MJ where
  toMulEquiv := geometricIntersectionSubgroupEquiv MI MJ n
  continuous_toFun :=
    (((continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul
      continuous_const).subtype_mk _).subtype_mk _
  continuous_invFun :=
    (((continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul
      continuous_const).subtype_mk _).subtype_mk _

omit [IsTopologicalGroup A] in
/-- The actual target section is continuous in the original subgroup
topologies. -/
theorem continuous_geometricCoefficientSection (PI MI UI PJ : Subgroup A)
    (dI : IsSemidirectDecomposition PI MI UI) (n : A) :
    Continuous (geometricCoefficientSection PI MI UI PJ dI n) :=
  ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

/-- The orbit coefficient projection inherits continuity from the original
inducing projection. -/
theorem continuous_geometricCoefficientProjection (PI PJ MJ UJ : Subgroup A)
    (dJ : IsSemidirectDecomposition PJ MJ UJ) (n : A)
    (hproj : Continuous dJ.projection) :
    Continuous (geometricCoefficientProjection PI PJ MJ UJ dJ n) := by
  have hEq :
      (geometricCoefficientProjection PI PJ MJ UJ dJ n :
        (geometricTargetIntersection PI PJ n).subgroupOf PI → MJ) =
      fun h => dJ.projection ⟨n⁻¹ * h.val.val * n,
        ((mem_geometricTargetIntersection PI PJ n h.val.val).mp h.property).2⟩ :=
    funext (geometricCoefficientProjection_apply PI PJ MJ UJ dJ n)
  rw [hEq]
  exact hproj.comp
    (((continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul
      continuous_const).subtype_mk _)

/-- Continuity of the actual intersection projection follows from continuity
of the original inducing projection and the given intersection decomposition. -/
theorem continuous_geometricTargetProjection
    (PI MI UI PJ MJ UJ : Subgroup A)
    (dI : IsSemidirectDecomposition PI MI UI)
    (dJ : IsSemidirectDecomposition PJ MJ UJ) (n : A)
    (hTarget : IsSemidirectDecomposition
      ((geometricTargetIntersection MI PJ n).subgroupOf MI)
      ((geometricTargetIntersection MI MJ n).subgroupOf MI)
      ((geometricTargetIntersection MI UJ n).subgroupOf MI))
    (hproj : Continuous dJ.projection) :
    Continuous hTarget.projection := by
  let p := geometricCoefficientLeviMap MI PJ MJ UJ n hTarget
  have hc := (continuous_geometricCoefficientProjection PI PJ MJ UJ dJ n hproj).comp
    (continuous_geometricCoefficientSection PI MI UI PJ dI n)
  have hp : Continuous p :=
    (hc.congr (fun l =>
      geometricCoefficientProjection_section PI MI UI PJ MJ UJ dI dJ n hTarget l)).subtype_mk _
  exact ((geometricIntersectionSubgroupContinuousEquiv MI MJ n).symm.continuous.comp hp).congr
    (fun l => (geometricIntersectionSubgroupEquiv MI MJ n).symm_apply_apply
      (hTarget.projection l))

end Topology

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
local notation "Ls" => Subgroup.subgroupOf
  (geometricSourceIntersection (levi i ν I) (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "f" => geometricCoefficientProjection
  (parabolic i ν I) (parabolic i ν J) (levi i ν J) (unipotent i ν J)
  dJ (n : RationalPoint k G.X)
local notation "s" => geometricCoefficientSection
  (parabolic i ν I) (levi i ν I) (unipotent i ν I) (parabolic i ν J)
  dI (n : RationalPoint k G.X)

variable
  (hSource : GeometricSourceDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  (hTarget : GeometricTargetDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  {R : Type uR} [CommRing R] {V : Type uV} [AddCommGroup V] [Module R V]

local notation "p" => geometricCoefficientLeviMap
  (levi i ν I) (parabolic i ν J) (levi i ν J) (unipotent i ν J)
  (n : RationalPoint k G.X) hTarget

/-- The quotient comparison intertwines the actual target section action
with the inflated, inverse-conjugated source Jacquet action before scalar
normalization. -/
def geometricCoefficientActionEquiv (σ : Representation R (levi i ν J) V) :
    Representation.Equiv
      ((Representation.toCoinvariants (σ.comp f) N).comp s)
      ((Jacquet.action σ S Ls hSource.levi_le_normalizer).comp p) where
  toLinearEquiv :=
    geometricCoefficientQuotientEquiv i ν hStandard hG hi hν hN I J dI dJ n σ
  isIntertwining' l := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change geometricCoefficientQuotientEquiv i ν hStandard hG hi hν hN I J dI dJ n σ
        (Jacquet.mk (σ.comp f) N (σ (f (s l)) v)) =
      Jacquet.action σ S Ls hSource.levi_le_normalizer (p l)
        (geometricCoefficientQuotientEquiv i ν hStandard hG hi hν hN I J dI dJ n σ
          (Jacquet.mk (σ.comp f) N v))
    rw [geometricCoefficientQuotientEquiv_mk, geometricCoefficientQuotientEquiv_mk,
      Jacquet.action_mk,
      geometricCoefficientProjection_section
        (parabolic i ν I) (levi i ν I) (unipotent i ν I)
        (parabolic i ν J) (levi i ν J) (unipotent i ν J) dI dJ
        (n : RationalPoint k G.X) hTarget l]

@[simp] theorem geometricCoefficientActionEquiv_mk
    (σ : Representation R (levi i ν J) V) (v : V) :
    geometricCoefficientActionEquiv i ν hStandard hG hi hν hN I J dI dJ n
        hSource hTarget σ (Jacquet.mk (σ.comp f) N v) =
      Jacquet.mk σ S v :=
  geometricCoefficientQuotientEquiv_mk i ν hStandard hG hi hν hN I J dI dJ n σ v

end RationalPointFamily

end Langlands.Aubert.General
