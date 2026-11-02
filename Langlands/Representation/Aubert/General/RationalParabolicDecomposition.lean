import Langlands.Representation.Aubert.General.RationalPointFamily
import Langlands.Representation.Aubert.General.DynamicParabolic
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.GroupScheme.Rational.PointDecomposition

/-! # Standard rational-point decompositions from the standard-cocharacter statement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Equality with the three dynamic subgroups transports the proved dynamic
decomposition to the exact standard rational-point subgroups. -/
theorem isSemidirectDecomposition_of_dynamic [IsSeparated G.X.hom]
    (I : Finset (SimpleRoot i ν))
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : standardParabolic i ν (rootSet i ν I) = Dynamic.parabolic χ)
    (hM : standardLevi i ν (rootSet i ν I) = Dynamic.centralizer χ)
    (hU : standardUnipotent i ν (rootSet i ν I) = Dynamic.unipotent χ) :
    IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I) := by
  change IsSemidirectDecomposition
    ((standardParabolic i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _)))
    ((standardLevi i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _)))
    ((standardUnipotent i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _)))
  rw [hP, hM, hU]
  exact dynamic_isSemidirectDecomposition χ _

/-- The existing standard-cocharacter assertion supplies both nonvacuity and
all three dynamic comparisons. No standard decomposition is assumed as data. -/
theorem isSemidirectDecomposition_of_standardCocharacterStatement
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν)) :
    IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I) := by
  have := hG.isSeparated
  obtain ⟨hexists, hcompare⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨ζ, hζ⟩ := hexists
  obtain ⟨hP, hM, hU⟩ := hcompare ζ hζ
  exact isSemidirectDecomposition_of_dynamic i ν I
    (CommGroupScheme.groupHom ζ ≫ i) hP hM hU

/-- The Levi projection is constructed on the exact standard point subgroups. -/
def standardProjection
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν)) :
    parabolic i ν I →* levi i ν I :=
  (isSemidirectDecomposition_of_standardCocharacterStatement i ν
    hStandard hG hi hν I).projection

/-- The projection of any decomposition of these exact standard subgroups
equals the actual dynamic limit, on every point and for every realization. -/
theorem projection_eq_dynamic_limit [IsSeparated G.X.hom]
    (I : Finset (SimpleRoot i ν))
    (h : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : parabolic i ν I = (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)))
    (hM : levi i ν I = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
    (hU : unipotent i ν I = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
    (p : parabolic i ν I) :
    (h.projection p : RationalPoint k G.X) =
      Dynamic.limit χ ⟨p, hP ▸ p.property⟩ := by
  let pd : (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) := ⟨p, hP ▸ p.property⟩
  have hz : Dynamic.limit χ pd ∈ levi i ν I := by
    rw [hM]
    exact Dynamic.limit_mem_centralizer χ pd
  apply congrArg Subtype.val ((h.projection_eq_iff p ⟨_, hz⟩).mpr ?_)
  rw [hU]
  have hl := Dynamic.centralizer_le_parabolic χ _ (Dynamic.limit_mem_centralizer χ pd)
  have hu := Dynamic.conj_mem_unipotent χ (inv_mem hl)
    (Dynamic.mul_inv_limit_mem_unipotent χ pd)
  simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hu

end Langlands.Aubert.General.RationalPointFamily
