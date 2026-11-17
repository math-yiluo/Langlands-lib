import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeNormalizerSmooth
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeCentralizerOpen
import Langlands.GroupScheme.OpenSubgroupQuotientEtale
import Langlands.GroupScheme.HomogeneousQuotientGroup
import Langlands.GroupScheme.Rational.EnvelopeCentralizerGeometry

/-! # Multiplicative-type Weyl quotients from centralizer quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

open HomogeneousQuotientFromEmbedding

/-- Every supplied normalizer representative inherits the closedness of the
chosen closed normalizer. -/
theorem relativeMultiplicativeTypeNormalizer_isClosedSubgroup
    {S : Scheme.{u}} {G H N : GroupScheme S} [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (hi : IsClosedSubgroup i)
    (n : N ⟶ G) (hnrep : (SubgroupFunctor.range i).normalizer.IsRepresentedBy n) :
    IsClosedSubgroup n := by
  obtain ⟨N', n', hn', hnrep'⟩ :=
    relativeMultiplicativeTypeNormalizer_hasClosedRepresentative i hH hi
  rw [← hnrep.isoOfIsRepresentedBy_hom_comp hnrep']
  exact (IsClosedSubgroup.of_iso (hnrep.isoOfIsRepresentedBy hnrep')).comp hn'

/-- Factor a multiplicative-type subgroup into any represented normalizer;
its centralizer there is exactly the original centralizer's full preimage. -/
def multiplicativeTypeSubgroupInNormalizer
    {S : Scheme.{u}} {G N : GroupScheme S} {T : CommGroupScheme S}
    [IsAffineHom G.X.hom]
    (t : T.toGrp ⟶ G) (hT : RelativeMultiplicativeType.IsMultiplicativeType T.toGrp)
    (ht : IsClosedSubgroup t)
    (n : N ⟶ G) (hnrep : (torusNormalizer t).IsRepresentedBy n) :
    {j : T.toGrp ⟶ N // j ≫ n = t ∧ IsClosedSubgroup j ∧
      torusCentralizer j = (torusCentralizer t).comap n} := by
  let j := hnrep.factorHom t (SubgroupFunctor.le_normalizer _)
  have hj : j ≫ n = t := hnrep.factorHom_comp _ _
  have hnclosed := relativeMultiplicativeTypeNormalizer_isClosedSubgroup t hT ht n hnrep
  have hjclosed : IsClosedSubgroup j := IsClosedSubgroup.of_comp hnclosed (by rwa [hj])
  let : Mono n.hom.hom := hnrep.1
  have hcent : torusCentralizer j = (torusCentralizer t).comap n := by
    rw [torusCentralizer_eq_comap_of_mono j n, hj]
  exact ⟨j, hj, hjclosed, hcent⟩

/-- A supplied homogeneous quotient by the centralizer preimage in a
multiplicative-type normalizer is a separated quasi-compact etale group quotient. -/
def multiplicativeTypeWeylQuotientOfHomogeneousQuotient
    {S : Scheme.{u}} {G N Z : GroupScheme S} {T : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (t : T.toGrp ⟶ G) (hT : RelativeMultiplicativeType.IsMultiplicativeType T.toGrp)
    (ht : IsClosedSubgroup t)
    (n : N ⟶ G) (hnrep : (torusNormalizer t).IsRepresentedBy n)
    (c : Z ⟶ N) (hcrep : ((torusCentralizer t).comap n).IsRepresentedBy c)
    (D : HomogeneousQuotient c) :
    Σ W : GroupScheme S, {q : N ⟶ W //
      RelativeRoot.IsFppfQuotient ((torusCentralizer t).comap n) q ∧
        Etale W.X.hom ∧ IsSeparated W.X.hom ∧ QuasiCompact W.X.hom} := by
  let : Smooth N.X.hom := relativeMultiplicativeTypeNormalizer_smooth t hT ht n hnrep
  let : Mono c.hom.hom := hcrep.1
  have hcopen : IsOpenImmersion c.hom.hom.left :=
    relativeMultiplicativeTypeCentralizer_isOpenImmersion t hT ht n hnrep c hcrep
  let : Smooth D.projection.left := D.smooth_projection
  let : Surjective D.projection.left := D.surjective_projection
  have hnormal : (SubgroupFunctor.range c).IsNormal := by
    rw [hcrep.2]
    intro U g x _ hx
    change (g * x * g⁻¹) ≫ n.hom.hom ∈ (torusCentralizer t).carrier U
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    apply torusCentralizer_isNormalizedBy_torusNormalizer t U
      (g ≫ n.hom.hom) (x ≫ n.hom.hom) ?_ hx
    rw [← hnrep.2]
    exact ⟨g, rfl⟩
  let W := D.groupScheme hnormal
  let q : N ⟶ W := D.groupProjection hnormal
  have hq : RelativeRoot.IsFppfQuotient ((torusCentralizer t).comap n) q := by
    rw [← hcrep.2]
    exact D.groupProjection_isFppfQuotient hnormal
  have hWe : Etale W.X.hom :=
    etale_of_open_subgroup_quotient c hcopen D.projection D.fibers
  exact ⟨W, q, hq, hWe, D.separated, D.quasiCompact⟩

/-- Centralizer-quotient existence applied inside the actual normalizer
supplies its etale Weyl quotient, on any given centralizer representative. -/
def multiplicativeTypeWeylQuotientOfCentralizerQuotients
    {S : Scheme.{u}} {G N Z : GroupScheme S} {T : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (t : T.toGrp ⟶ G) (hT : RelativeMultiplicativeType.IsMultiplicativeType T.toGrp)
    (ht : IsClosedSubgroup t)
    (n : N ⟶ G) (hnrep : (torusNormalizer t).IsRepresentedBy n)
    (c : Z ⟶ N) (hcrep : ((torusCentralizer t).comap n).IsRepresentedBy c)
    (hQ : ∀ (j : T.toGrp ⟶ N), IsClosedSubgroup j →
      ∀ (Z' : GroupScheme S) (c' : Z' ⟶ N), (torusCentralizer j).IsRepresentedBy c' →
        Nonempty (HomogeneousQuotient c')) :
    Σ W : GroupScheme S, {q : N ⟶ W //
      RelativeRoot.IsFppfQuotient ((torusCentralizer t).comap n) q ∧
        Etale W.X.hom ∧ IsSeparated W.X.hom ∧ QuasiCompact W.X.hom} := by
  let E := multiplicativeTypeSubgroupInNormalizer t hT ht n hnrep
  have hcint : (torusCentralizer E.val).IsRepresentedBy c := by
    rw [E.property.2.2]
    exact hcrep
  let D : HomogeneousQuotient c := Classical.choice (hQ E.val E.property.2.1 Z c hcint)
  exact multiplicativeTypeWeylQuotientOfHomogeneousQuotient t hT ht n hnrep c hcrep D

end Langlands.GroupScheme
