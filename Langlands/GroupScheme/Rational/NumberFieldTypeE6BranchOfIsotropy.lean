import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexTypeE6Isotropy
import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexTypeD4VectorIsotropy
import Langlands.GroupScheme.Rational.TypeE6BranchCocharacter
import Langlands.GroupScheme.Rational.TypeE6BranchMarkingFromRoots
import Langlands.GroupScheme.Rational.TypeE6EndpointKernel
import Langlands.GroupScheme.Reductive.TitsIndexSplitRankProof

/-! # The distinguished short-arm vertex from E6 isotropy -/

noncomputable section

universe u

open AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

/-- Over a totally complex number field, isotropy suffices for the short-arm
vertex of the actual E6 index to be distinguished. -/
def NumberFieldTypeE6BranchOfIsotropyStatement : Prop :=
  NumberFieldTotallyComplexTypeE6IsotropyStatement.{u} →
    NumberFieldTotallyComplexTypeE6BranchDistinguishedStatement.{u}

theorem TitsIndexData.typeE6Branch_distinguished_of_not_isAnisotropic
    {F : Type u} [Field F] [NumberField F] (hF : IsTotallyComplex F)
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    (hsc : IsSimplyConnected G)
    (hcart : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b))
    (hIso : ¬ IsAnisotropic G) : e.symm 1 ∈ d.distinguishedVertices := by
  classical
  let : IsTotallyComplex F := hF
  have hne : d.distinguishedVertices.Nonempty := by
    by_contra hn
    let : IsEmpty d.DistinguishedOrbit := ⟨fun q => Quotient.inductionOn q fun a => hn ⟨a, a.property⟩⟩
    have hrank := (titsIndexSplitRank F G d).1
    rw [Nat.card_of_isEmpty, Nat.cast_zero] at hrank
    exact hIso hrank.symm
  by_contra hbranch
  have hEnds := typeE6UnmarkedBranchMarking F G d e hcart hsc hbranch hne
  let p := d.anisotropicKernelIndex
  obtain ⟨hSimple, e', hD4, hStar, w, hw, hObs⟩ := typeE6EndpointKernel F G d e hsc hcart hEnds
  exact (numberFieldTotallyComplexTypeD4VectorIsotropy F p.kernel p.index e'
    (p.isSimplyConnected hsc) hSimple hD4 hStar w hw hObs) p.anisotropic

theorem numberFieldTotallyComplexTypeE6BranchDistinguished_of_isotropy :
    NumberFieldTypeE6BranchOfIsotropyStatement.{u} := by
  intro hIso F _ _ hF G _ _ d e hsc habs hcart
  exact d.typeE6Branch_distinguished_of_not_isAnisotropic hF e hsc hcart
    (hIso F hF G d e hsc habs hcart)

end Langlands.GroupScheme
