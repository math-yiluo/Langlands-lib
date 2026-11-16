import Langlands.GroupScheme.RelativeLevi.BorelPreservingRefinement
import Langlands.GroupScheme.SectionedWeilInnerDescent

/-! # Descent of inner local isomorphisms through Borel stabilizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SectionedQuotientExtension

variable {R C : CommRingCat.{u}} [Algebra R C]
    [Module.Finite R C] [Module.Projective R C]
    {K B T Z P D : GroupScheme (Spec R)}
    (i : K ⟶ B) (p : B ⟶ T) (t : T ⟶ B) (z : Z ⟶ T)
    (qB : B ⟶ P) (qT : T ⟶ D)
    (ht : t ≫ p = 𝟙 T)
    (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p)
    (hB : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (z ≫ t)) qB)
    (hT : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) qT)
    [Mono i.hom.hom] [IsAffine P.X.left] [IsAffineHom K.X.hom]
    (hK : RelativeUnipotent.HasFiniteVectorBundleSeries K)
    (eD : D ≅ WeilGm.groupScheme R C)
    {G H Gad B' : GroupScheme (Spec R)}
    (qG : G ⟶ Gad) (hqG : RelativeRoot.IsFppfQuotient (center G) qG)
    (c : AutomorphicAction Gad G)
    (hc : c.restrict qG = AutomorphicAction.conjugation (𝟙 G))
    (iG : B ⟶ G) (jH : B' ⟶ H)
    (hG : IsReductive G) (hH : IsReductive H)
    (hiG : IsRelativeBorelSubgroup iG) (hjH : IsRelativeBorelSubgroup jH)
    (k : P ⟶ Gad)
    (hk : (c.subgroupStabilizer (SubgroupFunctor.range iG)).IsRepresentedBy k)
    {V : Over (Spec R)} [Flat V.hom] [Surjective V.hom]
    [LocallyOfFinitePresentation V.hom]

include ht hp hB hT hK eD hqG hc hG hH hiG hjH hk

/-- Actual Borel correction and stabilizer reduction descend the original
inner local family using the supplied sectioned quotient geometry. -/
def borelInnerIsoOfPicTrivial [Subsingleton (CommRing.Pic C)]
    (e : LocalGroupIso G H V) (he : e.HasInnerDiscrepancy c) : G ≅ H := by
  let d := e.borelPreservingFppfRefinement hG hH iG jH hiG hjH
  let : Flat d.cover.hom := d.flat
  let : Surjective d.cover.hom := d.surjective
  let : LocallyOfFinitePresentation d.cover.hom := d.locallyOfFinitePresentation
  let E := (e.refine d.map).twist c (d.cochain ≫ qG.hom.hom)
  have hE : E.HasInnerDiscrepancy c := d.hasInnerDiscrepancy c qG he
  have hpres : E.PreservesSubgroup (SubgroupFunctor.range iG) (SubgroupFunctor.range jH) :=
    d.preservesSubgroup c qG hc
  have hfaith : c.IsFaithful := c.centralQuotient_action_isFaithful qG hqG hc
  let ξ := E.subgroupInnerCocycle c hfaith hE
    (SubgroupFunctor.range iG) (SubgroupFunctor.range jH) hpres k hk
  have hξ : ξ.IsTrivial :=
    cocycle_isTrivial_of_pic_trivial i p t z qB qT ht hp hB hT hK eD ξ
  exact E.isoOfTrivialSubgroupInnerCocycle c hfaith hE
    (SubgroupFunctor.range iG) (SubgroupFunctor.range jH) hpres k hk hξ

/-- Finite-algebra Picard triviality supplies the coefficient Picard hypothesis. -/
def borelInnerIsoOfFiniteAlgebrasHaveTrivialPicard
    (hR : Langlands.Algebra.FiniteAlgebrasHaveTrivialPicard.{u, u} R)
    (e : LocalGroupIso G H V) (he : e.HasInnerDiscrepancy c) : G ≅ H := by
  let : Subsingleton (CommRing.Pic C) := hR C
  exact borelInnerIsoOfPicTrivial i p t z qB qT ht hp hB hT hK eD
    qG hqG c hc iG jH hG hH hiG hjH k hk e he

/-- Over a semi-local ring, the remaining hypotheses are the supplied
sectioned quotient and actual Borel-stabilizer geometry. -/
def borelInnerIsoOfSemilocal [Finite (MaximalSpectrum R)]
    (e : LocalGroupIso G H V) (he : e.HasInnerDiscrepancy c) : G ≅ H :=
  borelInnerIsoOfFiniteAlgebrasHaveTrivialPicard i p t z qB qT ht hp hB hT hK eD
    qG hqG c hc iG jH hG hH hiG hjH k hk
    (Langlands.Algebra.finiteAlgebrasHaveTrivialPicard_of_semilocal R) e he

end Langlands.GroupScheme.SectionedQuotientExtension
