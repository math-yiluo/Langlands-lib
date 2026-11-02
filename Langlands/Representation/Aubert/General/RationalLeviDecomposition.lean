import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.GroupScheme.Rational.StandardLeviIntersectionStatement

/-! # Restricted standard decompositions inside the actual rational-point Levis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

namespace IsSemidirectDecomposition

/-- A decomposition contained in a subgroup is also a decomposition read
inside that subgroup. -/
theorem subgroupOf {H : Type u} [Group H] {P M U L : Subgroup H}
    (h : IsSemidirectDecomposition P M U) (hPL : P ≤ L) :
    IsSemidirectDecomposition (P.subgroupOf L) (M.subgroupOf L) (U.subgroupOf L) := by
  refine ⟨fun _ hm => h.levi_le hm, fun _ hu => h.unipotent_le hu, ?_, ?_⟩
  · apply Subgroup.le_normalizer_iff.mpr
    intro p hp x hx
    exact (Subgroup.le_normalizer_iff.mp h.le_normalizer) p.val hp x.val hx
  · rw [Subgroup.isComplement'_def, Subgroup.isComplement_iff_existsUnique_inv_mul_mem]
    intro p
    let pH : P := ⟨p.val.val, p.property⟩
    let m := h.projection pH
    refine ⟨⟨⟨⟨m.val, hPL (h.levi_le m.property)⟩, h.levi_le m.property⟩,
      m.property⟩, h.projection_inv_mul_mem pH, ?_⟩
    intro n hn
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : M => (z : H))
      ((h.projection_eq_iff pH ⟨n.val.val.val, n.property⟩).mpr hn).symm

end IsSemidirectDecomposition

/-- Every index of the Levi labelled by `J` is a subset of `J`. -/
theorem leviIndex_subset {Index : Type u} (J : Finset Index) (I : Finset J) :
    leviIndex J I ⊆ J := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  exact b.property

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Specialize the named all-test intersection statement, then restrict to
the exact standard Levi point subgroup. -/
theorem isSemidirectDecomposition_in_levi
    (hInter : StandardLeviIntersectionStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J : Finset (SimpleRoot i ν)) (I : Finset J) :
    IsSemidirectDecomposition
      ((parabolic i ν (leviIndex J I)).subgroupOf (levi i ν J))
      ((levi i ν (leviIndex J I)).subgroupOf (levi i ν J))
      ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)) := by
  have hincl : rootSet i ν (leviIndex J I) ⊆ rootSet i ν J :=
    (rootSet_subset_iff i ν _ J).mpr (leviIndex_subset J I)
  obtain ⟨hUP, hMP, hNormal, hComplement⟩ :=
    (hInter k G hG T i hi ν hν (rootSet i ν (leviIndex J I)) (rootSet i ν J)
      (rootSet_subset i ν _) (rootSet_subset i ν J) hincl).1 (Over.mk (𝟙 _))
  have h : IsSemidirectDecomposition
      (levi i ν J ⊓ parabolic i ν (leviIndex J I))
      (levi i ν (leviIndex J I)) (levi i ν J ⊓ unipotent i ν (leviIndex J I)) :=
    IsSemidirectDecomposition.of_isComplement'_symm hMP hUP
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mp hNormal) hComplement
  simpa only [Subgroup.inf_subgroupOf_left] using h.subgroupOf inf_le_left

/-- The resulting actual projection for a standard parabolic inside `L_J`. -/
def standardLeviProjection
    (hInter : StandardLeviIntersectionStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J : Finset (SimpleRoot i ν)) (I : Finset J) :
    (parabolic i ν (leviIndex J I)).subgroupOf (levi i ν J) →*
      (levi i ν (leviIndex J I)).subgroupOf (levi i ν J) :=
  (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I).projection

end RationalPointFamily

end Langlands.Aubert.General
