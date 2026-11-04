import Langlands.GroupScheme.Adjoint.Action
import Langlands.GroupScheme.Derived.CenterReduction
import Langlands.GroupScheme.HomImageEmbedding
import Langlands.GroupScheme.SubgroupFunctor.QuotientEmbedding
import Langlands.GroupScheme.SubgroupFunctor.QuotientNormality

/-! # Closed normal inclusions induced on supplied adjoint quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IsAdjointQuotient

variable {k : Type u} [Field k]
    {S H G R Q : GroupScheme (Spec (CommRingCat.of k))}
    {p : H ⟶ R} {q : G ⟶ Q}
    (hq : IsAdjointQuotient q) (hp : IsAdjointQuotient p)

/-- The canonical homomorphism between supplied adjoint quotients when the
source full centre maps into the ambient full centre. -/
def subgroupHom (i : H ⟶ G) (hcenter : center H ≤ (center G).comap i) : R ⟶ Q :=
  hp.desc (i ≫ q) (by
    intro T x hx
    change (x ≫ i.hom.hom) ≫ q.hom.hom = 1
    exact hq.killsCenter T (x ≫ i.hom.hom) (hcenter T hx))

/-- The induced homomorphism completes the supplied adjoint quotient square. -/
theorem subgroupHom_square (i : H ⟶ G) (hcenter : center H ≤ (center G).comap i) :
    i ≫ q = p ≫ hq.subgroupHom hp i hcenter :=
  (hp.comp_desc (i ≫ q) _).symm

/-- The commuting quotient square uniquely determines the induced homomorphism. -/
theorem subgroupHom_unique (i : H ⟶ G) (hcenter : center H ≤ (center G).comap i)
    (j : R ⟶ Q) (hj : i ≫ q = p ≫ j) :
    j = hq.subgroupHom hp i hcenter := by
  apply hp.hom_ext
  rw [← hj, ← hq.subgroupHom_square hp i hcenter]

/-- Monicity of the original inclusion gives exact inverse image of full
centres, and hence monicity of the induced adjoint homomorphism. -/
theorem subgroupHom_mono (i : H ⟶ G) [Mono i.hom.hom]
    (hcenter : center H ≤ (center G).comap i) :
    Mono (hq.subgroupHom hp i hcenter).hom.hom := by
  let := hp.flat
  let := hp.surjective
  let := hp.isConnectedReductive.isAffineHom
  let := hp.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : IsAffine R.X.left := isAffine_of_isAffineHom R.X.hom
  have hk : SubgroupFunctor.range (kernelι p) ≤
      (SubgroupFunctor.range (kernelι q)).comap i := by
    rw [hp.kernel_range_eq_center, hq.kernel_range_eq_center]
    exact hcenter
  have heq := SubgroupFunctor.quotientSubgroupHom_unique i q p hk
    (hq.subgroupHom hp i hcenter) (hq.subgroupHom_square hp i hcenter)
  rw [heq]
  apply SubgroupFunctor.quotientSubgroupHom_mono
  rw [hp.kernel_range_eq_center, hq.kernel_range_eq_center]
  exact center_comap_le_of_mono i

/-- The induced adjoint inclusion is closed, without requiring that the
original subgroup contain the ambient full centre. -/
theorem subgroupHom_isClosedSubgroup (i : H ⟶ G) [Mono i.hom.hom]
    (hcenter : center H ≤ (center G).comap i) :
    IsClosedSubgroup (hq.subgroupHom hp i hcenter) := by
  have := hq.subgroupHom_mono hp i hcenter
  let := hp.isAdjoint.isSemisimple.isConnectedReductive.smooth
  let := hp.isAdjoint.isSemisimple.isConnectedReductive.connectedSpace
  let := hp.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let := hq.isAdjoint.isSemisimple.isConnectedReductive.smooth
  let := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  exact HomImage.isClosedSubgroup_of_mono _

/-- Normality of the original inclusion descends to the actual adjoint inclusion. -/
theorem subgroupHom_isNormal (i : H ⟶ G) [Mono i.hom.hom]
    (hcenter : center H ≤ (center G).comap i)
    (hnormal : (SubgroupFunctor.range i).IsNormal) :
    (SubgroupFunctor.range (hq.subgroupHom hp i hcenter)).IsNormal := by
  have := hq.subgroupHom_mono hp i hcenter
  let := hp.flat
  let := hp.surjective
  let := hq.flat
  let := hq.surjective
  let := hp.isConnectedReductive.isAffineHom
  let := hq.isConnectedReductive.isAffineHom
  let := hp.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine R.X.left := isAffine_of_isAffineHom R.X.hom
  let : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  exact SubgroupFunctor.isNormal_range_of_fpqc_square i q p _
    (hq.subgroupHom_square hp i hcenter) hnormal

/-- Equivariance of the original inclusion gives equivariance of the
constructed inclusion for the canonical actions on the adjoint quotients. -/
theorem subgroupHom_isEquivariant
    (b : AutomorphicAction S G) (c : AutomorphicAction S H)
    (i : H ⟶ G) (hcenter : center H ≤ (center G).comap i)
    (hi : c.IsEquivariant b i) :
    (hp.action c).IsEquivariant (hq.action b) (hq.subgroupHom hp i hcenter) :=
  hq.action_isEquivariant_of_square hp b c i _
    (hq.subgroupHom_square hp i hcenter) hi

end Langlands.GroupScheme.IsAdjointQuotient
