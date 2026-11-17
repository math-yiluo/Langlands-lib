import Langlands.GroupScheme.FppfQuotientKernelGeometry
import Langlands.GroupScheme.Reductive.RelativeCentralQuotientReductivity
import Langlands.GroupScheme.Reductive.RelativeCenterProof
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeSubgroupStatement
import Langlands.GroupScheme.RelativeCentralMultiplicativeTypeQuotientStatement
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Geometric reduction for supplied relative central quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The two multiplicative-type inputs supply kernel multiplicative type,
affinity and reductivity for every supplied relative central quotient. -/
def RelativeCentralQuotientGeometryReductionStatement : Prop :=
  RelativeMultiplicativeTypeClosedSubgroupStatement.{u} →
  RelativeCentralMultiplicativeTypeQuotientStatement.{u} →
  ∀ (S : Scheme.{u}) (G Z Q : GroupScheme S), IsReductive G →
    ∀ z : Z ⟶ G, IsClosedSubgroup z → IsCentral z →
    ∀ q : G ⟶ Q, RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q →
      RelativeMultiplicativeType.IsMultiplicativeType Z ∧
      IsAffineHom Q.X.hom ∧ IsReductive Q

/-- Given the relative closed-subgroup theorem for multiplicative type,
a closed central full kernel in a reductive group is of multiplicative type.
Flatness and local finite presentation follow from the supplied quotient. -/
theorem centralKernel_isMultiplicativeType_of_closedSubgroups
    (hsubgroup : RelativeMultiplicativeTypeClosedSubgroupStatement.{u})
    {S : Scheme.{u}} {G Z Q : GroupScheme S} (hG : IsReductive G)
    (z : Z ⟶ G) (hz : IsClosedSubgroup z) (hcentral : IsCentral z)
    {q : G ⟶ Q} (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q) :
    RelativeMultiplicativeType.IsMultiplicativeType Z := by
  let : IsClosedImmersion z.hom.hom.left := hz
  let : Mono z.hom.hom := Over.mono_of_mono_left _
  obtain ⟨C, c, hc, hC, _⟩ := reductiveRelativeCenter S G hG
  let f := hc.isRepresentedBy.factorHom z ((isCentral_iff_range_le_center z).mp hcentral)
  have hfc : f ≫ c = z := SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _
  have hf : IsClosedSubgroup f :=
    IsClosedSubgroup.of_comp hc.1 (hfc.symm ▸ hz)
  exact hsubgroup S Z C f hC hf
    (hq.flat_representedKernel ⟨inferInstance, rfl⟩)
    (hq.locallyOfFinitePresentation_representedKernel ⟨inferInstance, rfl⟩)

namespace RelativeRoot.IsFppfQuotient

/-- The affine quotient construction for central multiplicative-type
subgroups makes every supplied quotient with the same kernel affine. -/
theorem isAffineHom_target_of_centralMultiplicativeTypeQuotients
    (hquotient : RelativeCentralMultiplicativeTypeQuotientStatement.{u})
    {S : Scheme.{u}} {G Z Q : GroupScheme S} (hG : IsReductive G)
    (z : Z ⟶ G) (hz : IsClosedSubgroup z) (hcentral : IsCentral z)
    (hZ : RelativeMultiplicativeType.IsMultiplicativeType Z)
    {q : G ⟶ Q} (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q) :
    IsAffineHom Q.X.hom := by
  obtain ⟨R, r, hR, hr⟩ := hquotient S G hG.smooth hG.isAffineHom
    (fun s => (hG.geometricFiber s).connectedSpace) Z z hz hcentral hZ
  let : IsAffineHom R.X.hom := hR
  exact FppfQuotientComparison.isAffineHom_target hq hr

/-- The geometry clause of the relative central quotient theorem follows
from the two independent multiplicative-type inputs. -/
theorem isReductive_target_of_multiplicativeType_geometry
    (hsubgroup : RelativeMultiplicativeTypeClosedSubgroupStatement.{u})
    (hquotient : RelativeCentralMultiplicativeTypeQuotientStatement.{u})
    {S : Scheme.{u}} {G Z Q : GroupScheme S} (hG : IsReductive G)
    (z : Z ⟶ G) (hz : IsClosedSubgroup z) (hcentral : IsCentral z)
    {q : G ⟶ Q} (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q) :
    IsReductive Q := by
  have hZ := centralKernel_isMultiplicativeType_of_closedSubgroups
    hsubgroup hG z hz hcentral hq
  let : IsAffineHom Q.X.hom :=
    isAffineHom_target_of_centralMultiplicativeTypeQuotients
      hquotient hG z hz hcentral hZ hq
  exact hq.isReductive_target_of_central hG
    ((isCentral_iff_range_le_center z).mp hcentral)

end RelativeRoot.IsFppfQuotient

/-- The named geometry reduction follows from the three parameterized adapters. -/
theorem relativeCentralQuotientGeometryReduction :
    RelativeCentralQuotientGeometryReductionStatement.{u} := by
  intro hsubgroup hquotient S G Z Q hG z hz hc q hq
  have hZ := centralKernel_isMultiplicativeType_of_closedSubgroups
    hsubgroup hG z hz hc hq
  exact ⟨hZ,
    hq.isAffineHom_target_of_centralMultiplicativeTypeQuotients
      hquotient hG z hz hc hZ,
    hq.isReductive_target_of_multiplicativeType_geometry
      hsubgroup hquotient hG z hz hc⟩

end Langlands.GroupScheme
