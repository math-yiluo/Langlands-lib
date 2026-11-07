import Langlands.GroupScheme.Rational.NestedParabolicCocharacterFace
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.StandardLeviStandardFamiliesProof
import Langlands.GroupScheme.Dynamic.LieProof

/-! # Actual roots of the outer Levi in a fine torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

variable {k : Type u} [Field k]
  {G P M Q L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {B A : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {m : M ⟶ P} {b : B.toGrp ⟶ M}
  {q : Q ⟶ G} {l : L ⟶ Q} {a : A.toGrp ⟶ L}
  (fine : ParabolicRootPresentation p m b)
  (outer : ParabolicRootPresentation q l a)
  (i : M ⟶ L) (hi : i ≫ l ≫ q = m ≫ p)

include outer in
private theorem outerLeviClosed : IsClosedSubgroup (l ≫ q) :=
  outer.isCompatible.levi.isClosedSubgroup.comp outer.isCompatible.parabolic.isClosedSubgroup

include outer in
private theorem outerLeviRepresented :
    (SubgroupFunctor.range (l ≫ q)).IsRepresentedBy (l ≫ q) := by
  let := (outerLeviClosed outer).mono
  exact ⟨Over.mono_of_mono_left _, rfl⟩

include outer i hi in
/-- The fine maximal split torus lies in the original outer Levi on every test. -/
theorem range_fineTorus_le_outerLevi :
    SubgroupFunctor.range fine.data.i ≤ SubgroupFunctor.range (l ≫ q) := by
  rw [fine.levi_eq_outerCocharacterInFineTorus outer i hi]
  exact (range_le_torusCentralizer fine.data.i).trans
    (torusCentralizer_le_dynamicCentralizer fine.data.i
      (CommGroupScheme.groupHom (fine.outerCocharacterInFineTorus outer i hi)))

/-- The actual lift of the fine maximal split torus to the original outer Levi. -/
def outerFineTorusFactor : fine.data.T.toGrp ⟶ L :=
  (outerLeviRepresented outer).factorHom fine.data.i
    (fine.range_fineTorus_le_outerLevi outer i hi)

/-- Its composite is the original fine maximal split-torus inclusion. -/
theorem outerFineTorusFactor_comp :
    fine.outerFineTorusFactor outer i hi ≫ (l ≫ q) = fine.data.i :=
  (outerLeviRepresented outer).factorHom_comp _ _

/-- This lift is maximal split in the original outer Levi. -/
theorem isMaximalSplitTorus_outerFineTorusFactor :
    IsMaximalSplitTorus (fine.outerFineTorusFactor outer i hi) :=
  IsMaximalSplitTorus.isMaximalSplitTorus_factorHom fine.isCompatible.maximalSplit
    (outerLeviRepresented outer) (outerLeviClosed outer)
    (fine.range_fineTorus_le_outerLevi outer i hi)

section Roots

variable [IsAffineHom L.X.hom] [LocallyOfFiniteType G.X.hom]
  [LocallyOfFiniteType L.X.hom]

/-- Outer Levi roots are exactly the fine roots killed by the transported cocharacter. -/
theorem relativeRoots_outerFineTorusFactor :
    relativeRoots (fine.outerFineTorusFactor outer i hi) =
      {α | α ∈ relativeRoots fine.data.i ∧
        latticePairing fine.data.T α (fine.outerCocharacterInFineTorus outer i hi) = 0} := by
  apply relativeRoots_centralizer_factor dynamicLie fine.data.i
    (fine.outerFineTorusFactor outer i hi) (l ≫ q)
    (fine.outerFineTorusFactor_comp outer i hi)
    (fine.outerCocharacterInFineTorus outer i hi)
  rw [← fine.levi_eq_outerCocharacterInFineTorus outer i hi]
  exact outerLeviRepresented outer

/-- The same fine generic cocharacter is generic for the torus inside the outer Levi. -/
theorem isGenericCocharacter_outerFineTorusFactor :
    IsGenericCocharacter (fine.outerFineTorusFactor outer i hi) fine.data.ν := by
  intro α hα
  rw [fine.relativeRoots_outerFineTorusFactor outer i hi] at hα
  exact fine.isCompatible.generic α hα.1

variable (hG : IsConnectedReductive G)
  (hP : SubgroupFunctor.range p ≤ SubgroupFunctor.range q)

include hG hP

/-- The outer Levi's actual simple roots are precisely the outer zero face. -/
theorem simpleRelativeRoots_outerFineTorusFactor :
    simpleRelativeRoots (fine.outerFineTorusFactor outer i hi) fine.data.ν =
      fine.outerSimpleRootFace outer i hi := by
  have hroots := fine.relativeRoots_outerFineTorusFactor outer i hi
  have hsub : relativeRoots (fine.outerFineTorusFactor outer i hi) ⊆
      relativeRoots fine.data.i := by
    intro α hα
    exact (hroots ▸ hα).1
  apply Set.Subset.antisymm
  · intro α hα
    have hαambient : α ∈ positiveRelativeRoots fine.data.i fine.data.ν :=
      ⟨hsub hα.1.1, hα.1.2⟩
    have hαzero := (hroots ▸ hα.1.1).2
    refine ⟨⟨hαambient, ?_⟩, hαzero⟩
    rintro ⟨beta, hbeta, gamma, hgamma, heq⟩
    have hbnonneg := fine.outerCocharacterInFineTorus_nonneg outer i hi hG hP hbeta
    have hgnonneg := fine.outerCocharacterInFineTorus_nonneg outer i hi hG hP hgamma
    have hsum : latticePairing fine.data.T beta (fine.outerCocharacterInFineTorus outer i hi) +
        latticePairing fine.data.T gamma (fine.outerCocharacterInFineTorus outer i hi) = 0 := by
      simpa only [heq, map_add, LinearMap.add_apply] using hαzero
    have hbzero : latticePairing fine.data.T beta
        (fine.outerCocharacterInFineTorus outer i hi) = 0 := by omega
    have hgzero : latticePairing fine.data.T gamma
        (fine.outerCocharacterInFineTorus outer i hi) = 0 := by omega
    exact hα.2 ⟨beta, ⟨hroots.symm ▸ ⟨hbeta.1, hbzero⟩, hbeta.2⟩,
      gamma, ⟨hroots.symm ▸ ⟨hgamma.1, hgzero⟩, hgamma.2⟩, heq⟩
  · intro α hα
    have hαL : α ∈ relativeRoots (fine.outerFineTorusFactor outer i hi) :=
      hroots.symm ▸ ⟨hα.1.1.1, hα.2⟩
    refine ⟨⟨hαL, hα.1.1.2⟩, ?_⟩
    rintro ⟨beta, hbeta, gamma, hgamma, heq⟩
    exact hα.1.2 ⟨beta, ⟨hsub hbeta.1, hbeta.2⟩,
      gamma, ⟨hsub hgamma.1, hgamma.2⟩, heq⟩

end Roots

end Langlands.GroupScheme.ParabolicRootPresentation
