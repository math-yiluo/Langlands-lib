import Langlands.GroupScheme.PseudoComplete
import Langlands.GroupScheme.PseudoParabolic
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.PseudoParabolicQuotientStatement

/-! # The dynamic pseudo-reductive case of CGP Proposition C.1.6

Interface for the assembly of C.1.6: the DVR lifting property for homogeneous quotients of a
pseudo-reductive group by an actual dynamic parabolic subgroup `P_G(χ)`, over a fixed field.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over the field `k`, every homogeneous quotient `q : G ⟶ Q` of a pseudo-reductive group by an
actual dynamic parabolic `P_G(χ)` (all-test right-coset fibers) has the DVR lifting property. -/
def DynamicParabolicQuotientDVRLifting (k : Type u) [Field k] : Prop :=
  ∀ (G : GroupScheme (Spec (CommRingCat.of k)))
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
    IsPseudoReductive G → Smooth q.left → Surjective q.left → QuasiCompact q.left →
    (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ).carrier T) →
    PseudoComplete.HasDVRLifting Q

/-- C.1.6 from the pseudo-reductive reduction (CGP 2.2.10, stated as the hypothesis `hred`) and
the dynamic case over every field. -/
theorem pseudoParabolicQuotientPseudoComplete_of_dynamic
    (hred : ∀ (k : Type u) [Field k] (G P : GroupScheme (Spec (CommRingCat.of k)))
      (i : P ⟶ G),
      IsPseudoParabolicSubgroup i →
        ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
          Smooth q.left → Surjective q.left → QuasiCompact q.left →
          (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
            g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) →
          ∃ (G' : GroupScheme (Spec (CommRingCat.of k)))
            (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G') (q' : G'.X ⟶ Q),
            IsPseudoReductive G' ∧
              Smooth q'.left ∧ Surjective q'.left ∧ QuasiCompact q'.left ∧
              ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G'.X),
                g ≫ q' = h ≫ q' ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ).carrier T)
    (hdyn : ∀ (k : Type u) [Field k], DynamicParabolicQuotientDVRLifting k) :
    PseudoParabolicQuotientPseudoCompleteStatement.{u} := by
  intro k _ G P i hP Q q hsep hlft hqc hsm hsurj hqcq hfib
  obtain ⟨G', χ, q', hG', hsm', hsurj', hqc', hfib'⟩ := hred k G P i hP Q q hsm hsurj hqcq hfib
  exact ⟨hsep, hlft, hqc, hdyn k G' χ Q q' hG' hsm' hsurj' hqc' hfib'⟩

end Langlands.GroupScheme
