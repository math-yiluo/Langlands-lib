import Langlands.GroupScheme.Reductive.DerivedCentralIsogenyReduction
import Langlands.GroupScheme.Reductive.MaximalCentralTorusReduction
import Langlands.GroupScheme.Reductive.MaximalCentralTorusFieldMultiplication
import Langlands.GroupScheme.Reductive.MultiplicationBaseChange
import Langlands.GroupScheme.Reductive.RelativeDerivedReduction
import Langlands.GroupScheme.Reductive.RelativeProducts
import Langlands.GroupScheme.Reductive.FibrewiseCentralIsogenyStatement
import Langlands.GroupScheme.Derived.TorusQuotientCommutators
import Langlands.GroupScheme.Torus.RelativeReductive
import Langlands.AbelianScheme.FiberwiseIsogeny

/-! # Derived central isogenies from three structural statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G D Z : GroupScheme S}

/-- Field multiplication and the supplied fibre criterion give the actual
product-map isogeny when maximality and commutator containment hold on fibres. -/
theorem isCentralIsogeny_prodHom_of_residueFibres
    (hCriterion : ReductiveFibrewiseCentralIsogenyStatement.{u})
    (hG : IsReductive G) (hD : IsReductive D)
    {d : D ⟶ G} (hd : IsClosedSubgroup d)
    (hss : ∀ s : S, IsSemisimple (geometricFiber D s))
    {z : Z ⟶ G} (hz : IsMaximalCentralRelativeTorus z)
    (hmax : ∀ s : S, IsMaximalCentralRelativeTorus
      ((GroupScheme.baseChange (S.fromSpecResidueField s)).map z))
    (hcomm : ∀ s : S, (SubgroupFunctor.range
      ((GroupScheme.baseChange (S.fromSpecResidueField s)).map d)).ContainsCommutators) :
    IsCentralIsogeny (prodHom z d (hz.2.1.commute_values d)) := by
  let f := prodHom z d (hz.2.1.commute_values d)
  have hf : ∀ s : S, IsCentralIsogeny
      ((GroupScheme.baseChange (S.fromSpecResidueField s)).map f) := by
    intro s
    let b := S.fromSpecResidueField s
    have hm := (hmax s).isCentralIsogeny_commutingMultiplication
      (hG.isConnectedReductive_baseChange b)
      ((GroupScheme.baseChange b).map d) (hd.baseChange b) (hcomm s)
      (isSemisimple_residueFiber hss s).hasFiniteCenter
    change IsCentralIsogeny
      (commutingSubgroupMultiplicationHom ((GroupScheme.baseChange b).map z)
        ((GroupScheme.baseChange b).map d)
        ((hmax s).2.1.commute_values ((GroupScheme.baseChange b).map d))) at hm
    rw [← prodHom_eq_commutingSubgroupMultiplicationHom
      ((GroupScheme.baseChange b).map z) ((GroupScheme.baseChange b).map d)
      ((hmax s).2.1.commute_values ((GroupScheme.baseChange b).map d))] at hm
    exact (isCentralIsogeny_baseChange_prodHom_iff b z d
      (hz.2.1.commute_values d)
      ((hmax s).2.1.commute_values ((GroupScheme.baseChange b).map d))).mpr hm
  have hsurj : Surjective f.hom.hom.left :=
    surjective_of_fiber f.hom.hom fun s => (hf s).surjective
  exact (hCriterion S (Z ⊗ D) G (hz.2.2.1.isReductive.tensor hD) hG f hsurj).mpr
    fun s => ⟨(hf s).kernel_isFinite, (hf s).isCentral_kernelι⟩

/-- The unchanged full target follows from the three displayed structural
premises, with no additional hypotheses on the base or the reductive group. -/
def ReductiveDerivedCentralIsogenyStructuralReductionStatement : Prop :=
  ReductiveRelativeCenterStatement.{u} →
    RelativeMultiplicativeTypeLargestSubtorusStatement.{u} →
      ReductiveFibrewiseCentralIsogenyStatement.{u} →
        ReductiveDerivedCentralIsogenyStatement.{u}

/-- Assemble maximal central tori, fibre multiplication, and the quotient
pairing, retaining all unproved structural inputs as explicit premises. -/
theorem reductiveDerivedCentralIsogeny_of_structuralInputs :
    ReductiveDerivedCentralIsogenyStructuralReductionStatement.{u} := by
  intro hCenter hLargest hCriterion
  apply reductiveDerivedCentralIsogeny_of_multiplication
  intro S G hG
  obtain ⟨hex, hbase⟩ := maximalCentralRelativeTorusReduction hCenter hLargest S G hG
  refine ⟨hex, ?_⟩
  intro D d hd _ hD hss Q q hQ hq Z z hz hZ
  change IsMaximalCentralRelativeTorus z at hZ
  exact isCentralIsogeny_prodHom_of_residueFibres hCriterion hG hD hd hss hZ
    (fun s => hbase Z z hZ _ (S.fromSpecResidueField s))
    (fun s => hq.containsCommutators_range_baseChange_of_isTorus hQ
      (S.fromSpecResidueField s))

end Langlands.GroupScheme
