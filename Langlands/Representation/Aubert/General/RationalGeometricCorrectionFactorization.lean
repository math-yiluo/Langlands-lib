import Langlands.Representation.Aubert.General.RationalGeometricStabilizerProjection
import Langlands.Representation.Aubert.General.SemidirectRestriction
import Langlands.Representation.Aubert.General.RationalPointSecondCountable

/-! # Factorization of actual geometric correction intersections -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General

namespace IsSemidirectDecomposition

variable {A : Type*} [Group A] {P M U : Subgroup A}
  (d : IsSemidirectDecomposition P M U) (F : Subgroup A)
  (hF : ∀ p : P, (p : A) ∈ F → (d.projection p : A) ∈ F)

include d hF

/-- A projection-stable intersection retains the original two factors. -/
theorem interOfProjection :
    IsSemidirectDecomposition (P ⊓ F) (M ⊓ F) (U ⊓ F) := by
  refine ⟨inf_le_inf d.levi_le le_rfl, inf_le_inf d.unipotent_le le_rfl, ?_, ?_⟩
  · apply Subgroup.le_normalizer_iff.mpr
    intro p hp u hu
    exact ⟨(Subgroup.le_normalizer_iff.mp d.le_normalizer) p hp.1 u hu.1,
      F.mul_mem (F.mul_mem hp.2 hu.2) (F.inv_mem hp.2)⟩
  · apply Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mpr
    intro q
    let p : P := ⟨q, q.property.1⟩
    let m : (M ⊓ F).subgroupOf (P ⊓ F) :=
      ⟨⟨d.projection p, d.levi_le (d.projection p).property, hF p q.property.2⟩,
        (d.projection p).property, hF p q.property.2⟩
    refine ⟨m, ⟨d.projection_inv_mul_mem p,
      F.mul_mem (F.inv_mem (hF p q.property.2)) q.property.2⟩, ?_⟩
    intro n hn
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg Subtype.val
      ((d.projection_eq_iff p ⟨n.val.val, n.property.1⟩).mpr hn.1)).symm

/-- The intersection projection has exactly the original ambient value. -/
theorem interOfProjection_projection (p : ↥(P ⊓ F)) :
    ((d.interOfProjection F hF).projection p : A) =
      (d.projection ⟨p, p.property.1⟩ : A) := by
  symm
  have he := (d.projection_eq_iff ⟨p, p.property.1⟩
    ⟨((d.interOfProjection F hF).projection p : A),
      ((d.interOfProjection F hF).projection p).property.1⟩).mpr
        ((d.interOfProjection F hF).projection_inv_mul_mem p).1
  exact congrArg Subtype.val he

variable [TopologicalSpace A]

/-- Restricting the original continuous projection preserves continuity. -/
theorem continuous_interOfProjection_projection (hp : Continuous d.projection) :
    Continuous (d.interOfProjection F hF).projection := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : ↥(P ⊓ F) => ((d.interOfProjection F hF).projection p : A))
  have he : (fun p : ↥(P ⊓ F) => ((d.interOfProjection F hF).projection p : A)) =
      fun p : ↥(P ⊓ F) => (d.projection ⟨p, p.property.1⟩ : A) :=
    funext (d.interOfProjection_projection F hF)
  rw [he]
  exact continuous_subtype_val.comp
    (hp.comp (continuous_subtype_val.subtype_mk _))

end IsSemidirectDecomposition

section Normalizers

variable {A : Type*} [Group A]

/-- A common Levi normalizes the intersection of subgroups normalized by
its two original Levi factors. -/
theorem geometricCommonLevi_normalizes_intersection
    (MI MJ U V : Subgroup A) (n : A)
    (hMIU : MI ≤ Subgroup.normalizer U)
    (hMJV : MJ ≤ Subgroup.normalizer V) :
    geometricTargetIntersection MI MJ n ≤
      Subgroup.normalizer (geometricTargetIntersection U V n : Set A) := by
  intro x hx
  apply Subgroup.inf_normalizer_le_normalizer_inf
  exact ⟨hMIU hx.1,
    Subgroup.le_normalizer_map (MulAut.conj n).toMonoidHom
      ((Subgroup.map_mono hMJV) hx.2)⟩

end Normalizers

namespace IsSemidirectDecomposition

variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [LocallyCompactSpace A] [SecondCountableTopology A]
  {P M U : Subgroup A} (d : IsSemidirectDecomposition P M U)
  (F : Subgroup A)
  (hF : ∀ p : P, (p : A) ∈ F → (d.projection p : A) ∈ F)

include hF

/-- The original Haar characters factor on every subgroup that normalizes
both original factors and the projection-stable intersection. -/
theorem interOfProjection_closedRestrictCharacter
    (hp : Continuous d.projection)
    (hP : IsClosed (P : Set A)) (hM : IsClosed (M : Set A))
    (hU : IsClosed (U : Set A)) (hFc : IsClosed (F : Set A))
    (S : Subgroup A)
    (hSP : S ≤ Subgroup.normalizer P) (hSM : S ≤ Subgroup.normalizer M)
    (hSU : S ≤ Subgroup.normalizer U) (hSF : S ≤ Subgroup.normalizer F) :
    HaarModulus.closedRestrictCharacter (P ⊓ F) (hP.inter hFc) S
        ((le_inf hSP hSF).trans Subgroup.inf_normalizer_le_normalizer_inf) =
      HaarModulus.closedRestrictCharacter (M ⊓ F) (hM.inter hFc) S
        ((le_inf hSM hSF).trans Subgroup.inf_normalizer_le_normalizer_inf) *
      HaarModulus.closedRestrictCharacter (U ⊓ F) (hU.inter hFc) S
        ((le_inf hSU hSF).trans Subgroup.inf_normalizer_le_normalizer_inf) := by
  apply MonoidHom.ext
  intro s
  exact (d.interOfProjection F hF).closedNormalizerCharacter_eq_mul
    (d.continuous_interOfProjection_projection F hF hp)
    (hP.inter hFc) (hM.inter hFc) (hU.inter hFc) (s : A)
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨hSP s.property, hSF s.property⟩)
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨hSM s.property, hSF s.property⟩)
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨hSU s.property, hSF s.property⟩)

end IsSemidirectDecomposition

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

universe u

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (I J : Finset (SimpleRoot i ν))
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))

include hStandard hG hi hν hN dI

/-- The forward-conjugate source correction intersection splits into the
actual target endpoint radical and the common unipotent intersection. -/
theorem geometricCorrectionIntersectionDecomposition :
    IsSemidirectDecomposition
      (geometricTargetIntersection (parabolic i ν I) (unipotent i ν J)
        (n : RationalPoint k G.X))
      (geometricTargetIntersection (levi i ν I) (unipotent i ν J)
        (n : RationalPoint k G.X))
      (geometricTargetIntersection (unipotent i ν I) (unipotent i ν J)
        (n : RationalPoint k G.X)) :=
  dI.interOfProjection
    ((unipotent i ν J).map (MulAut.conj (n : RationalPoint k G.X)).toMonoidHom)
    (projection_mem_conjugate_unipotent i ν hStandard hG hi hν hN I J dI n)

variable [TopologicalSpace (RationalPoint k G.X)]

/-- The correction-intersection projection is continuous as soon as the
original standard Levi projection is continuous. -/
theorem continuous_geometricCorrectionIntersection_projection (hp : Continuous dI.projection) :
    Continuous (geometricCorrectionIntersectionDecomposition
      i ν hStandard hG hi hν hN I J dI n).projection :=
  dI.continuous_interOfProjection_projection
    ((unipotent i ν J).map (MulAut.conj (n : RationalPoint k G.X)).toMonoidHom)
    (projection_mem_conjugate_unipotent i ν hStandard hG hi hν hN I J dI n) hp

section Haar

variable [IsTopologicalGroup (RationalPoint k G.X)]

/-- Multiplication in the actual correction intersection gives continuous
coordinates with the actual endpoint radical and common radical factors. -/
def geometricCorrectionIntersectionCoordinates (hp : Continuous dI.projection) :
    geometricTargetIntersection (levi i ν I) (unipotent i ν J)
        (n : RationalPoint k G.X) ×
      geometricTargetIntersection (unipotent i ν I) (unipotent i ν J)
        (n : RationalPoint k G.X) ≃ₜ
    geometricTargetIntersection (parabolic i ν I) (unipotent i ν J)
        (n : RationalPoint k G.X) :=
  (geometricCorrectionIntersectionDecomposition
    i ν hStandard hG hi hν hN I J dI n).coordinates
    (continuous_geometricCorrectionIntersection_projection
      i ν hStandard hG hi hν hN I J dI n hp)

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [SecondCountableTopology (RationalPoint k G.X)]
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hMI : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hUJ : IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))

local notation "A" => RationalPoint k G.X
local notation "PI" => parabolic i ν I
local notation "MI" => levi i ν I
local notation "UI" => unipotent i ν I
local notation "MJ" => levi i ν J
local notation "UJ" => unipotent i ν J
local notation "L" => geometricTargetIntersection MI MJ (n : A)
local notation "hMIPI" => dI.levi_le.trans (fun _ hx => Subgroup.le_normalizer hx)
local notation "hMIMI" => (fun _ hx => Subgroup.le_normalizer hx : MI ≤ Subgroup.normalizer MI)
local notation "hLP" => geometricCommonLevi_normalizes_intersection
  MI MJ PI UJ (n : A) hMIPI dJ.levi_le_normalizer
local notation "hLM" => geometricCommonLevi_normalizes_intersection
  MI MJ MI UJ (n : A) hMIMI dJ.levi_le_normalizer
local notation "hLU" => geometricCommonLevi_normalizes_intersection
  MI MJ UI UJ (n : A) dI.levi_le_normalizer dJ.levi_le_normalizer

/-- On the actual common Levi, the modulus of `P_I ∩ n U_J n⁻¹`
is the product of the target endpoint-radical modulus and that of the
common unipotent intersection. All normalizer witnesses are derived. -/
theorem geometricCorrectionIntersection_modulus_eq_mul (hp : Continuous dI.projection) :
    HaarModulus.closedRestrictCharacter
        (geometricTargetIntersection PI UJ (n : A))
        (isClosed_geometricTargetIntersection PI UJ hPI hUJ (n : A)) L hLP =
      HaarModulus.closedRestrictCharacter
        (geometricTargetIntersection MI UJ (n : A))
        (isClosed_geometricTargetIntersection MI UJ hMI hUJ (n : A)) L hLM *
      HaarModulus.closedRestrictCharacter
        (geometricTargetIntersection UI UJ (n : A))
        (isClosed_geometricTargetIntersection UI UJ hUI hUJ (n : A)) L hLU := by
  apply dI.interOfProjection_closedRestrictCharacter
    ((unipotent i ν J).map (MulAut.conj (n : A)).toMonoidHom)
    (projection_mem_conjugate_unipotent i ν hStandard hG hi hν hN I J dI n)
    hp hPI hMI hUI (isClosed_map_conj UJ hUJ (n : A)) L
  · exact inf_le_left.trans hMIPI
  · exact inf_le_left.trans hMIMI
  · exact inf_le_left.trans dI.levi_le_normalizer
  · exact inf_le_right.trans
      ((Subgroup.map_mono dJ.levi_le_normalizer).trans (Subgroup.le_normalizer_map _))

end Haar

end RationalPointFamily
end Langlands.Aubert.General
