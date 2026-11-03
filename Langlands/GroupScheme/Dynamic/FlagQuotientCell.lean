import Langlands.GroupScheme.QuotientCell
import Langlands.GroupScheme.Dynamic.FlagQuotientTranslations

/-! # Sections from an actual group cell in a scheme quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable (k : Type u) [Field k]
variable {G P U : GroupScheme (Spec (CommRingCat.of k))}
    (iP : P ⟶ G) (iU : U ⟶ G) {Q : Over (Spec (CommRingCat.of k))}
    (q : G.X ⟶ Q)
    (hf : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range iP).carrier T)
    [Mono iP.hom.hom] [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsOpenImmersion (QuotientCell.multiplication iP iU.hom.hom).left]

/-- The open image of a group cell together with its actual section in the group. -/
def flagQuotientCell : Σ V : Q.left.Opens, (openOver k Q V ⟶ G.X) := by
  letI := QuotientCell.isOpenImmersion iP iU.hom.hom q hf
  exact ⟨(iU.hom.hom ≫ q).left.opensRange,
    QuotientCell.sectionOverImage iU.hom.hom q⟩

/-- The cell section composes with the quotient projection to the open inclusion. -/
theorem flagQuotientCell_comp :
    (flagQuotientCell k iP iU q hf).2 ≫ q =
      openOverι k Q (flagQuotientCell k iP iU q hf).1 := by
  let := QuotientCell.isOpenImmersion iP iU.hom.hom q hf
  exact QuotientCell.sectionOverImage_comp iU.hom.hom q

/-- The entire range of the identity coset lies in the constructed cell open. -/
theorem range_identity_subset_flagQuotientCell :
    Set.range
      (rationalPointEquiv k Q ((1 : RationalPoint k G.X) ≫ q)).left ⊆
        (flagQuotientCell k iP iU q hf).1 := by
  let := QuotientCell.isOpenImmersion iP iU.hom.hom q hf
  have hi : (1 : RationalPoint k U.X) ≫ iU.hom.hom =
      (1 : RationalPoint k G.X) := MonObj.one_comp _
  have he :
      rationalPointEquiv k Q ((1 : RationalPoint k G.X) ≫ q) =
        rationalPointEquiv k U.X (1 : RationalPoint k U.X) ≫ (iU.hom.hom ≫ q) := by
    rw [← rationalPointEquiv_natural, ← Category.assoc, hi]
  rw [he]
  exact QuotientCell.range_subset_image iU.hom.hom q _

include iP iU hf in
/-- Rational lifts and an open group multiplication cell give actual sections
near every rational point of the same quotient model. -/
theorem localSections_of_open_multiplication
    (hlift : ∀ p : RingPoint k Q k, ∃ g : RingPoint k G.X k, g ≫ q = p) :
    ∀ p : RingPoint k Q k,
      ∃ (V : Q.left.Opens) (s : openOver k Q V ⟶ G.X),
        Set.range p.left ⊆ V ∧ s ≫ q = openOverι k Q V :=
  localSections_of_rational_lifts k G (SubgroupFunctor.range iP) q hf hlift
    (flagQuotientCell k iP iU q hf).1 (flagQuotientCell k iP iU q hf).2
    (range_identity_subset_flagQuotientCell k iP iU q hf)
    (flagQuotientCell_comp k iP iU q hf)

end Langlands.GroupScheme.Dynamic
