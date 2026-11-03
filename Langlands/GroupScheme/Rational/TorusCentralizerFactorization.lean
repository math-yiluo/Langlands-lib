import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # A commutative subgroup inside its represented whole-group centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {G M : GroupScheme S} {B : CommGroupScheme S}

/-- If the containing subgroup centralizes the ambient image of a commutative
subgroup, that commutative subgroup is central in the containing subgroup. -/
theorem isCentral_of_range_le_torusCentralizer
    {b : B.toGrp ⟶ M} {j : M ⟶ G} (hj : Mono j.hom.hom)
    (hcentralizer : SubgroupFunctor.range j ≤ torusCentralizer (b ≫ j)) :
    IsCentral b := by
  intro U x V q y
  apply (commute_iff_eq _ _).mpr
  apply hj.right_cancellation
  rw [MonObj.mul_comp, MonObj.mul_comp]
  have hy := hcentralizer V (show y ≫ j.hom.hom ∈
    (SubgroupFunctor.range j).carrier V from ⟨y, rfl⟩)
  have hc := hy V (𝟙 V) (q ≫ x)
  simpa only [Grp.comp_hom_hom, Category.assoc, Category.id_comp] using hc.symm.eq

variable (b : B.toGrp ⟶ G) {j : M ⟶ G}

/-- The canonical factor of a commutative subgroup through a representative of
its whole-group centralizer, using containment on every test scheme. -/
def torusCentralizerFactor (hj : (torusCentralizer b).IsRepresentedBy j) :
    B.toGrp ⟶ M :=
  hj.factorHom b (range_le_torusCentralizer b)

theorem torusCentralizerFactor_comp
    (hj : (torusCentralizer b).IsRepresentedBy j) :
    torusCentralizerFactor b hj ≫ j = b :=
  hj.factorHom_comp _ _

/-- The original commutative subgroup becomes central in the representative of
its centralizer. No centrality in the ambient group is assumed. -/
theorem isCentral_torusCentralizerFactor
    (hj : (torusCentralizer b).IsRepresentedBy j) :
    IsCentral (torusCentralizerFactor b hj) := by
  apply isCentral_of_range_le_torusCentralizer hj.1
  rw [torusCentralizerFactor_comp]
  exact hj.2.le

/-- A closed embedding stays closed after factoring through a closed
representative of its centralizer. -/
theorem isClosedSubgroup_torusCentralizerFactor
    (hj : (torusCentralizer b).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (hb : IsClosedSubgroup b) :
    IsClosedSubgroup (torusCentralizerFactor b hj) :=
  IsClosedSubgroup.of_comp hjc (by rwa [torusCentralizerFactor_comp])

end Base

section Field

variable {k : Type u} [Field k]
  {G M : GroupScheme (Spec (CommRingCat.of k))}
  {B : CommGroupScheme (Spec (CommRingCat.of k))}

variable {b : B.toGrp ⟶ G} {j : M ⟶ G}

/-- A split subtorus becomes a central split torus in a closed representative
of its whole-torus centralizer. -/
theorem IsSplitSubtorus.isCentralSplitTorus_torusCentralizerFactor
    (hb : IsSplitSubtorus b) (hj : (torusCentralizer b).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) :
    IsCentralSplitTorus (torusCentralizerFactor b hj) :=
  ⟨⟨hb.1, isClosedSubgroup_torusCentralizerFactor b hj hjc hb.2⟩,
    isCentral_torusCentralizerFactor b hj⟩

/-- Ambient maximal splitness is preserved by the canonical factor through a
closed representative of the whole-torus centralizer. -/
theorem IsMaximalSplitTorus.isMaximalSplitTorus_torusCentralizerFactor
    (hb : IsMaximalSplitTorus b) (hj : (torusCentralizer b).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) :
    IsMaximalSplitTorus (torusCentralizerFactor b hj) := by
  apply IsMaximalSplitTorus.of_comp hjc
  rwa [torusCentralizerFactor_comp]

/-- Ambient maximal-torus structure is likewise preserved by the canonical
factor through a closed representative of the whole-torus centralizer. -/
theorem IsMaximalTorus.isMaximalTorus_torusCentralizerFactor
    (hb : IsMaximalTorus b) (hj : (torusCentralizer b).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) :
    IsMaximalTorus (torusCentralizerFactor b hj) := by
  apply IsMaximalTorus.of_comp hjc
  rwa [torusCentralizerFactor_comp]

end Field

end Langlands.GroupScheme
