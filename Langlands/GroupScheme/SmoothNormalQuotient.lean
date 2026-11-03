import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.NormalQuotientGroup
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof

/-! # Actual smooth quotients by smooth normal closed subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G N : GroupScheme (Spec (CommRingCat.of k))}

/-- An actual quotient group scheme, with the geometric properties inherited
from the smooth homogeneous quotient and its exact represented fppf kernel. -/
structure SmoothNormalQuotient (i : N ⟶ G) where
  quotient : GroupScheme (Spec (CommRingCat.of k))
  projection : G ⟶ quotient
  smooth : Smooth quotient.X.hom
  separated : IsSeparated quotient.X.hom
  locallyOfFiniteType : LocallyOfFiniteType quotient.X.hom
  quasiCompact : QuasiCompact quotient.X.hom
  smooth_projection : Smooth projection.hom.hom.left
  surjective_projection : Surjective projection.hom.hom.left
  quasiCompact_projection : QuasiCompact projection.hom.hom.left
  isFppfQuotient : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) projection

namespace SmoothNormalQuotient

variable (i : N ⟶ G) [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- Choose the published smooth homogeneous quotient and descend the actual
group law using normality of the specified subgroup on all tests. -/
def ofClosedNormal (hi : IsClosedSubgroup i) (hN : Smooth N.X.hom)
    (hn : (SubgroupFunctor.range i).IsNormal) : SmoothNormalQuotient i :=
  Classical.choice (by
    obtain ⟨Q, q, hsep, hlft, hqc, hsm, hsurj, hqqc, hfib⟩ :=
      smoothSubgroupQuotientExistence k G N i hi hN
    have : IsSeparated Q.hom := hsep
    have : LocallyOfFiniteType Q.hom := hlft
    have : QuasiCompact Q.hom := hqc
    have : Smooth q.left := hsm
    have : Surjective q.left := hsurj
    have : QuasiCompact q.left := hqqc
    have : Smooth (q.left ≫ Q.hom) := by
      rw [Over.w q]
      infer_instance
    have hQ : Smooth Q.hom :=
      Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp q.left Q.hom
    exact ⟨{
      quotient := NormalQuotient.groupScheme G (SubgroupFunctor.range i) hn q hfib
      projection := NormalQuotient.hom G (SubgroupFunctor.range i) hn q hfib
      smooth := hQ
      separated := hsep
      locallyOfFiniteType := hlft
      quasiCompact := hqc
      smooth_projection := hsm
      surjective_projection := hsurj
      quasiCompact_projection := hqqc
      isFppfQuotient := NormalQuotient.isFppfQuotient G (SubgroupFunctor.range i) hn q hfib
    }⟩)

variable {i}

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
/-- Connectedness of the actual source descends along the quotient projection. -/
theorem connectedSpace (D : SmoothNormalQuotient i) [ConnectedSpace G.X.left] :
    ConnectedSpace D.quotient.X.left := by
  have : Surjective D.projection.hom.hom.left := D.surjective_projection
  exact D.projection.hom.hom.left.surjective.connectedSpace
    D.projection.hom.hom.left.continuous

end SmoothNormalQuotient

end Langlands.GroupScheme
