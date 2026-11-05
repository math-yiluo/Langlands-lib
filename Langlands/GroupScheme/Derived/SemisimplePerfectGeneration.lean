import Langlands.GroupScheme.Derived.SemisimplePerfectReduction
import Langlands.GroupScheme.Derived.SemisimpleTorusContainment
import Langlands.GroupScheme.Reductive.TorusGenerationStatement
import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection

/-! # Semisimple perfectness from torus containment and generation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The remaining maximal-torus containment obligation over algebraically
closed fields. The conclusion is on all test schemes. -/
def AlgebraicallyClosedSemisimpleMaximalTorusDerivedStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))), IsSemisimple G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalTorus i → SubgroupFunctor.range i ≤ derivedSubgroup G

/-- Actual root-datum existence supplies maximal-torus containment; the
reducedness part of the root-datum existence input is not used. -/
theorem algebraicallyClosedSemisimpleMaximalTorusDerived_of_rootDatumExistence
    (hex : RootDatumExistenceStatement.{u}) :
    AlgebraicallyClosedSemisimpleMaximalTorusDerivedStatement.{u} := by
  intro k _ _ G hG T i hi
  have := hG.isConnectedReductive.isAffineHom
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have hT := hi.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨J, _, P, hP, _⟩ := hex k G hG.isConnectedReductive T hT i hi
  exact hG.range_torus_le_derivedSubgroup_of_rootDatum i hT hi.2.1 hP

/-- Maximal-torus containment and finite torus generation imply perfectness
over algebraically closed fields. -/
theorem algebraicallyClosedSemisimplePerfect_of_maximalTorusDerived_of_torusGeneration
    (hmax : AlgebraicallyClosedSemisimpleMaximalTorusDerivedStatement.{u})
    (hgen : ReductiveFiniteTorusGenerationStatement.{u}) :
    AlgebraicallyClosedSemisimplePerfectStatement.{u} := by
  intro k _ _ G hG
  have := hG.isConnectedReductive.isAffineHom
  have := hG.isConnectedReductive.smooth
  obtain ⟨m, T, t, hT, ht, hgenerate⟩ := hgen k G hG.isConnectedReductive
  apply SubgroupFunctor.ext
  intro U
  change (derivedSubgroup G).carrier U = ⊤
  apply top_unique
  intro x _ H j hj hcomm
  have hall : ∀ a, FactorsThrough (t a).hom.hom j := by
    intro a
    let A : CommGroupScheme (Spec (CommRingCat.of k)) :=
      { T a with comm := (hT a).isCommMonObj }
    obtain ⟨M, i, hi, f, hf⟩ :=
      exists_maximalTorus_extension_of_finiteType G (T := A) (t a) (hT a) (ht a)
    have hiD : SubgroupFunctor.range i ≤ derivedSubgroup G := hmax k G hG M i hi
    have hti : SubgroupFunctor.range (t a) ≤ SubgroupFunctor.range j := by
      rw [← hf]
      exact (SubgroupFunctor.range_comp_le f i).trans
        (hiD.trans (derivedSubgroup_le_range j hj hcomm))
    have hpoint := hti (T a).X
      (SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩)
    exact SubgroupFunctor.mem_range.mp hpoint
  rw [hgenerate H j hj hall]
  exact Subgroup.mem_top _

/-- The same two structural inputs imply the original arbitrary-field
perfectness statement by fpqc descent from the algebraic closure. -/
theorem semisimplePerfect_of_maximalTorusDerived_of_torusGeneration
    (hmax : AlgebraicallyClosedSemisimpleMaximalTorusDerivedStatement.{u})
    (hgen : ReductiveFiniteTorusGenerationStatement.{u}) :
    SemisimplePerfectStatement.{u} :=
  semisimplePerfect_of_algebraicallyClosed
    (algebraicallyClosedSemisimplePerfect_of_maximalTorusDerived_of_torusGeneration hmax hgen)

/-- Root-datum existence and finite torus generation suffice for the full
semisimple perfectness statement. Both structural premises remain explicit. -/
theorem semisimplePerfect_of_rootDatumExistence_of_torusGeneration
    (hex : RootDatumExistenceStatement.{u})
    (hgen : ReductiveFiniteTorusGenerationStatement.{u}) :
    SemisimplePerfectStatement.{u} :=
  semisimplePerfect_of_maximalTorusDerived_of_torusGeneration
    (algebraicallyClosedSemisimpleMaximalTorusDerived_of_rootDatumExistence hex) hgen

end Langlands.GroupScheme
