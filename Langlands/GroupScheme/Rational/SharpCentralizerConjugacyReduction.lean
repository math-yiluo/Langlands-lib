import Langlands.GroupScheme.Rational.SharpCentralizerConjugacyReductionStatement
import Langlands.GroupScheme.Rational.ConjugacyStatement
import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductStatement
import Langlands.GroupScheme.Rational.SubgroupConjugacy
import Langlands.GroupScheme.Rational.TorusCentralizerConjugacy

/-! # Sharp conjugacy of represented centralizers from rational product decompositions -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G C Z Z' : GroupScheme (Spec (CommRingCat.of k))}
  {A A' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A product decomposition by the actual image of `p` upgrades ordinary conjugacy
of commutative subgroups to image-valued conjugacy of their represented centralizers. -/
theorem exists_range_conjugacy_of_centralizer_product
    (a : A.toGrp ⟶ G) (a' : A'.toGrp ⟶ G)
    (j : Z ⟶ G) (j' : Z' ⟶ G) (p : C ⟶ G)
    (hj : (torusCentralizer a).IsRepresentedBy j)
    (hj' : (torusCentralizer a').IsRepresentedBy j')
    (hconj : SubgroupConjugate a a')
    (hprod : ∀ g : rationalPoints G,
      ∃ c : rationalPoints C, ∃ z : rationalPoints Z,
        g = rationalPoints.map p c * rationalPoints.map j z) :
    ∃ g ∈ (rationalPoints.map p).range, ∃ e : Z ≅ Z',
      j ≫ (G.innerIso g).hom = e.hom ≫ j' := by
  obtain ⟨g, eA, ha⟩ := hconj
  obtain ⟨c, z, hg⟩ := hprod g
  have hz : rationalPoints.map j z ∈
      (torusCentralizer a).carrier (Over.mk (𝟙 _)) := by
    rw [← hj.2]
    exact ⟨z, rfl⟩
  have hfix := (mem_torusCentralizer_base_iff a _).mp hz
  have haC : a ≫ (G.innerIso (rationalPoints.map p c)).hom = eA.hom ≫ a' := by
    rw [hg, innerIso_mul_hom, ← Category.assoc, hfix] at ha
    exact ha
  have hjC := hj.torusCentralizer_of_iso_square eA
    (G.innerIso (rationalPoints.map p c)) haC
  refine ⟨rationalPoints.map p c, ⟨c, rfl⟩,
    hjC.isoOfIsRepresentedBy hj', ?_⟩
  exact (hjC.isoOfIsRepresentedBy_hom_comp hj').symm

/-- Ordinary maximal split torus conjugacy and the simply connected centralizer
product imply sharp conjugacy of any supplied representatives of their centralizers.
The two structural statements are explicit premises of this reduction. -/
theorem exists_cover_conjugacy_of_maximal_split_centralizers
    (hconj : MaximalSplitTorusConjugacyStatement.{u})
    (hprod : SimplyConnectedCentralizerProductStatement.{u})
    {D : GroupScheme (Spec (CommRingCat.of k))}
    (a : A.toGrp ⟶ G) (a' : A'.toGrp ⟶ G)
    (j : Z ⟶ G) (j' : Z' ⟶ G) (d : D ⟶ G) (π : C ⟶ D)
    (hcover : IsSimplyConnectedDerivedCover d π)
    (ha : IsMaximalSplitTorus a) (ha' : IsMaximalSplitTorus a')
    (hj : (torusCentralizer a).IsRepresentedBy j)
    (hj' : (torusCentralizer a').IsRepresentedBy j') :
    ∃ g ∈ (rationalPoints.map (π ≫ d)).range, ∃ e : Z ≅ Z',
      j ≫ (G.innerIso g).hom = e.hom ≫ j' := by
  apply exists_range_conjugacy_of_centralizer_product a a' j j' (π ≫ d) hj hj'
  · exact (hconj k G hcover.isConnectedReductive).1 A A' a a' ha ha'
  · exact hprod k A G Z C D a j d π hcover ha hj

/-- Exact proof of the published generic actual-image reduction proposition. -/
theorem sharpCentralizerConjugacyReduction :
    SharpCentralizerConjugacyReductionStatement.{u} :=
  @exists_range_conjugacy_of_centralizer_product

end Langlands.GroupScheme
