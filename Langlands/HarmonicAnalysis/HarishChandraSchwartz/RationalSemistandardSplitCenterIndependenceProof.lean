import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitSections
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.CorepresentedComultiplication

/-! # Split-center independence on the identical actual Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  [TopologicalSpace F] [IsAffineHom G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology

private theorem splitCenter_le_of_factor
    {p : SemistandardSpectralIndex i} (m n : LeviModel p)
    {A B : CommGroupScheme (Spec (CommRingCat.of F))}
    (a : A.toGrp ⟶ m.scheme) (b : B.toGrp ⟶ n.scheme)
    (f : A.toGrp ⟶ B.toGrp) (hf : f ≫ b = a ≫ (m.schemeIso n).hom) :
    m.splitCenter a ≤ n.splitCenter b := by
  rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
  refine ⟨rationalPoints.map b (rationalPoints.map f x),
    ⟨rationalPoints.map f x, rfl⟩, ?_⟩
  have hx : rationalPoints.map b (rationalPoints.map f x) =
      rationalPoints.map (m.schemeIso n).hom (rationalPoints.map a x) := by
    change (x ≫ f.hom.hom) ≫ b.hom.hom =
      (x ≫ a.hom.hom) ≫ (m.schemeIso n).hom.hom.hom
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun q => x ≫ q.hom.hom) hf
  rw [hx]
  apply Subtype.ext
  change ((rationalPoints.map a x) ≫ (m.schemeIso n).hom.hom.hom) ≫
      n.inclusion.hom.hom = (rationalPoints.map a x) ≫ m.inclusion.hom.hom
  simpa only [LeviModel.schemeIso, Grp.comp_hom_hom, Category.assoc] using
    congrArg (fun q => (rationalPoints.map a x) ≫ q.hom.hom)
      (m.represents.isoOfIsRepresentedBy_hom_comp n.represents)

/-- All split-component presentations have the same literal point image. -/
theorem splitCenterChoiceIndependence :
    SplitCenterChoiceIndependenceStatement (F := F) (G := G) (i := i) := by
  intro p m n A B a b ha hb
  let : IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom
  let : IsAffineHom n.scheme.X.hom := n.reductive.isAffineHom
  apply le_antisymm
  · obtain ⟨f, hf⟩ := hb.exists_factor ha.1.1.1
      (ha.1.2.comp_iso (m.schemeIso n))
    exact splitCenter_le_of_factor m n a b f hf
  · obtain ⟨f, hf⟩ := ha.exists_factor hb.1.1.1
      (hb.1.2.comp_iso (n.schemeIso m))
    exact splitCenter_le_of_factor n m b a f hf

end Langlands.HarishChandraSchwartz.RationalSemistandard
