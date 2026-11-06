import Langlands.GroupScheme.HomogeneousQuotientBaseChange
import Langlands.GroupScheme.ParabolicQuotientProperProof
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof

/-! # Field fibres of a supplied relative parabolic quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

namespace Langlands.GroupScheme.RelativeParabolicQuotientFibers

variable {S : Scheme.{u}} {G P : GroupScheme S} {i : P ⟶ G}

/-- Smoothness of the ambient group descends to any supplied homogeneous quotient. -/
theorem smooth (Q : HomogeneousQuotient i) [Smooth G.X.hom] :
    Smooth Q.scheme.hom := by
  let : Smooth Q.projection.left := Q.smooth_projection
  let : Surjective Q.projection.left := Q.surjective_projection
  have : Smooth (Q.projection.left ≫ Q.scheme.hom) := by
    rw [Over.w Q.projection]
    infer_instance
  exact Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
    Q.projection.left Q.scheme.hom

/-- Every field fibre of a quotient of a reductive group is connected. -/
theorem connectedSpace_fieldBaseChange (Q : HomogeneousQuotient i) (hG : IsReductive G)
    {k : Type u} [Field k] (f : Spec (CommRingCat.of k) ⟶ S) :
    ConnectedSpace (Q.baseChange f).scheme.left := by
  let : ConnectedSpace (((GroupScheme.baseChange f).obj G).X.left) :=
    (hG.isConnectedReductive_baseChange f).connectedSpace
  let : Surjective (Q.baseChange f).projection.left :=
    (Q.baseChange f).surjective_projection
  exact (Q.baseChange f).projection.left.surjective.connectedSpace
    (Q.baseChange f).projection.left.continuous

/-- The structure morphism of a supplied quotient of a reductive group is
geometrically connected. -/
theorem geometricallyConnected (Q : HomogeneousQuotient i) (hG : IsReductive G) :
    GeometricallyConnected Q.scheme.hom := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun k _ f => ?_⟩
  exact connectedSpace_fieldBaseChange Q hG f

/-- A field fibre is proper when the corresponding subgroup is parabolic. -/
theorem proper_fieldBaseChange (Q : HomogeneousQuotient i) (hG : IsReductive G)
    {k : Type u} [Field k] (f : Spec (CommRingCat.of k) ⟶ S)
    (hP : IsParabolicSubgroup ((GroupScheme.baseChange f).map i)) :
    IsProper (Q.baseChange f).scheme.hom := by
  have hGk := hG.isConnectedReductive_baseChange f
  let : Smooth (((GroupScheme.baseChange f).obj G).X.hom) := hGk.smooth
  let : IsAffineHom (((GroupScheme.baseChange f).obj G).X.hom) := hGk.isAffineHom
  exact parabolicSubgroupQuotientProper k ((GroupScheme.baseChange f).obj G)
    hGk.connectedSpace ((GroupScheme.baseChange f).obj P) ((GroupScheme.baseChange f).map i)
    hP (Q.baseChange f).scheme (Q.baseChange f).projection
    (Q.baseChange f).separated (Q.baseChange f).locallyOfFiniteType
    (Q.baseChange f).quasiCompact (Q.baseChange f).smooth_projection
    (Q.baseChange f).surjective_projection (Q.baseChange f).quasiCompact_projection
    (Q.baseChange f).fibers

section AffineBase

variable {R : Type u} [CommRing R]
    {G P : GroupScheme (Spec (CommRingCat.of R))} {i : P ⟶ G}

/-- Testing all field algebra structures tests every field-valued point of the base. -/
theorem parabolic_atFieldPoint
    (hP : ∀ (k : Type u) [Field k] [Algebra R k],
      IsParabolicSubgroup ((GroupScheme.baseChange (Spec.algebraMap R k)).map i))
    {k : Type u} [Field k]
    (f : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    IsParabolicSubgroup ((GroupScheme.baseChange f).map i) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  let : Algebra R k := φ.hom.toAlgebra
  exact hP k

/-- Retain the actual base-changed quotient, together with its properness,
smoothness and connectedness, at any field-valued point. -/
def properConnectedFieldFiber (Q : HomogeneousQuotient i) (hG : IsReductive G)
    (hP : ∀ (k : Type u) [Field k] [Algebra R k],
      IsParabolicSubgroup ((GroupScheme.baseChange (Spec.algebraMap R k)).map i))
    {k : Type u} [Field k]
    (f : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    {F : HomogeneousQuotient ((GroupScheme.baseChange f).map i) //
      IsProper F.scheme.hom ∧ Smooth F.scheme.hom ∧ ConnectedSpace F.scheme.left} := by
  let : Smooth (((GroupScheme.baseChange f).obj G).X.hom) :=
    (hG.isConnectedReductive_baseChange f).smooth
  exact ⟨Q.baseChange f, proper_fieldBaseChange Q hG f (parabolic_atFieldPoint hP f),
    smooth (Q.baseChange f), connectedSpace_fieldBaseChange Q hG f⟩

@[simp]
theorem properConnectedFieldFiber_val (Q : HomogeneousQuotient i) (hG : IsReductive G)
    (hP : ∀ (k : Type u) [Field k] [Algebra R k],
      IsParabolicSubgroup ((GroupScheme.baseChange (Spec.algebraMap R k)).map i))
    {k : Type u} [Field k]
    (f : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    (properConnectedFieldFiber Q hG hP f).val = Q.baseChange f := rfl

end AffineBase

end Langlands.GroupScheme.RelativeParabolicQuotientFibers
