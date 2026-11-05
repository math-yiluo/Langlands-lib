import Langlands.GroupScheme.Rational.SplitTorusImageDominant
import Langlands.GroupScheme.Rational.MaximalSplitTorusExtension
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Absolute.BorelStatement

/-! # Maximal split tori adapted to a dynamic solvable subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A ground-field cocharacter factors through an actual maximal split torus.
Its whole-torus centralizer lies in the cocharacter's dynamic centralizer. -/
theorem exists_maximalSplitTorus_through_cocharacter
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G),
      IsMaximalSplitTorus a ∧
      ∃ ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ A.toGrp,
        ν ≫ a = χ ∧ torusCentralizer a ≤ Dynamic.centralizer χ := by
  let d := isSplitTorus_gm.dominantFactorization χ
  obtain ⟨A, a, ha, f, hf⟩ :=
    exists_maximalSplitTorus_extension G d.inclusion d.isSplitSubtorus
  let ν := d.factor ≫ f
  have hν : ν ≫ a = χ := by
    rw [Category.assoc, hf, d.factor_comp]
  refine ⟨A, a, ha, ν, hν, ?_⟩
  have hle := torusCentralizer_le_dynamicCentralizer a ν
  rwa [hν] at hle

/-- A maximal split torus together with a factorization of a prescribed
cocharacter and the resulting inclusion of whole centralizers. -/
structure MaximalSplitTorusThroughCocharacter
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : torus.toGrp ⟶ G
  isMaximalSplitTorus : IsMaximalSplitTorus inclusion
  cocharacter : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ torus.toGrp
  cocharacter_comp : cocharacter ≫ inclusion = χ
  centralizer_le : torusCentralizer inclusion ≤ Dynamic.centralizer χ

/-- Choose the actual maximal split torus through a prescribed cocharacter. -/
def maximalSplitTorusThroughCocharacter
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    MaximalSplitTorusThroughCocharacter χ :=
  Classical.choice <| by
    obtain ⟨A, a, ha, ν, hν, hZ⟩ := exists_maximalSplitTorus_through_cocharacter χ
    exact ⟨⟨A, a, ha, ν, hν, hZ⟩⟩

/-- If a subgroup is a dynamic parabolic, one maximal split torus has its
whole centralizer contained in that exact subgroup on every test scheme. -/
theorem exists_maximalSplitTorus_centralizer_le_dynamicParabolic_range
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {P : GroupScheme (Spec (CommRingCat.of k))} {j : P ⟶ G}
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : (Dynamic.parabolic χ).IsRepresentedBy j) :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G),
      IsMaximalSplitTorus a ∧ torusCentralizer a ≤ SubgroupFunctor.range j := by
  obtain ⟨A, a, ha, ν, hν, hZ⟩ := exists_maximalSplitTorus_through_cocharacter χ
  refine ⟨A, a, ha, ?_⟩
  rw [hP.2]
  exact hZ.trans (Dynamic.centralizer_le_parabolic χ)

/-- A representative of a whole-torus centralizer contained in a solvable
subgroup is solvable. All containment and factorization are on scheme tests. -/
theorem isSolvableGroupScheme_of_torusCentralizer_le_range
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ G)
    {B H : GroupScheme (Spec (CommRingCat.of k))} {j : B ⟶ G} {h : H ⟶ G}
    (hj : (SubgroupFunctor.range j).IsRepresentedBy j)
    (hB : IsSolvableGroupScheme B)
    (hH : (torusCentralizer a).IsRepresentedBy h)
    (hle : torusCentralizer a ≤ SubgroupFunctor.range j) :
    IsSolvableGroupScheme H := by
  let f := hj.factorHom h (by rw [hH.2]; exact hle)
  have hf : f ≫ j = h := hj.factorHom_comp h _
  let : Mono h.hom.hom := hH.1
  let : Mono f.hom.hom := mono_of_mono_fac (congrArg (fun b => b.hom.hom) hf)
  exact hB.of_mono f

/-- The parabolic/cocharacter comparison supplies a maximal split torus
whose entire centralizer lies in the given geometric Borel. -/
theorem IsGeometricBorelSubgroup.exists_maximalSplitTorus_centralizer_le_range
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    {B : GroupScheme (Spec (CommRingCat.of k))} {j : B ⟶ G}
    (hB : IsGeometricBorelSubgroup j) :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G),
      IsMaximalSplitTorus a ∧ torusCentralizer a ≤ SubgroupFunctor.range j := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨χ, hχ⟩ := (hPD k G hG B j hB.1.isClosedSubgroup).mp hB.isParabolicSubgroup
  let : IsClosedImmersion j.hom.hom.left := hB.1.isClosedSubgroup
  have hP : (Dynamic.parabolic χ).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, hχ⟩
  exact exists_maximalSplitTorus_centralizer_le_dynamicParabolic_range χ hP

end Langlands.GroupScheme
