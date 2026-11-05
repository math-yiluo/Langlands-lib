import Langlands.GroupScheme.Rational.QuasiSplitAdaptedSplitTorus
import Langlands.GroupScheme.Rational.ReductiveSolvableTorus
import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.FieldCentralizerRepresentabilityProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveStatement

/-! # Torus centralizers from containment in a solvable subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G C : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Dynamic centralizer reductivity gives reductivity of every closed
representative of a split-torus centralizer. Maximal splitness is unnecessary. -/
theorem IsSplitTorus.isConnectedReductive_centralizer_of_dynamic
    (hA : IsSplitTorus A.toGrp)
    (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hG : IsConnectedReductive G) (a : A.toGrp ⟶ G) (c : C ⟶ G)
    (hc : (torusCentralizer a).IsRepresentedBy c) (hclosed : IsClosedSubgroup c) :
    IsConnectedReductive C := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let χ := CommGroupScheme.groupHom (centralizingCocharacter hA a) ≫ a
  apply hDCR k G hG χ C c hclosed
  rw [centralizingCocharacter_spec hA a]
  exact hc

/-- A split-torus centralizer contained in a solvable subgroup is a torus,
given the universal dynamic centralizer reductivity statement. -/
theorem IsSplitTorus.isTorus_centralizer_of_le_solvable
    (hA : IsSplitTorus A.toGrp)
    (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hG : IsConnectedReductive G) (a : A.toGrp ⟶ G) (c : C ⟶ G)
    (hc : (torusCentralizer a).IsRepresentedBy c) (hclosed : IsClosedSubgroup c)
    {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ G)
    (hb : (SubgroupFunctor.range b).IsRepresentedBy b)
    (hB : IsSolvableGroupScheme B)
    (hle : torusCentralizer a ≤ SubgroupFunctor.range b) :
    IsTorus C :=
  (hA.isConnectedReductive_centralizer_of_dynamic hDCR hG a c hc hclosed).isTorus_of_isSolvableGroupScheme
      (isSolvableGroupScheme_of_torusCentralizer_le_range a hb hB hc hle)

/-- An actual closed torus representing the whole centralizer of the
specified commutative subgroup, including every scheme test and refinement. -/
structure TorusCentralizerTorusData (a : A.toGrp ⟶ G) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : torus.toGrp ⟶ G
  isTorus : IsTorus torus.toGrp
  isClosedSubgroup : IsClosedSubgroup inclusion
  represents : (torusCentralizer a).IsRepresentedBy inclusion

/-- Choose a torus presentation of the full centralizer from solvable
containment and dynamic centralizer reductivity. -/
def torusCentralizerTorusDataOfSolvableContainment
    (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hG : IsConnectedReductive G) (hA : IsSplitTorus A.toGrp) (a : A.toGrp ⟶ G)
    {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ G)
    (hb : IsClosedSubgroup b) (hB : IsSolvableGroupScheme B)
    (hle : torusCentralizer a ≤ SubgroupFunctor.range b) :
    TorusCentralizerTorusData a := by
  apply Classical.choice
  obtain ⟨C, c, hc, hclosed⟩ :=
    fieldCentralizerRepresentability k A G hA.isAffineHom a
  let : IsClosedImmersion b.hom.hom.left := hb
  have hbrep : (SubgroupFunctor.range b).IsRepresentedBy b :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hC : IsTorus C :=
    hA.isTorus_centralizer_of_le_solvable hDCR hG a c hc hclosed b hbrep hB hle
  exact ⟨{
    torus := { toGrp := C, comm := hC.isCommMonObj }
    inclusion := c
    isTorus := hC
    isClosedSubgroup := hclosed
    represents := hc }⟩

/-- A geometric Borel supplies a maximal split torus with a closed torus
centralizer, conditional on the two displayed structural statements. -/
theorem IsGeometricBorelSubgroup.exists_maximalSplitTorus_with_torusCentralizer
    (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    {B : GroupScheme (Spec (CommRingCat.of k))} {b : B ⟶ G}
    (hB : IsGeometricBorelSubgroup b) :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G),
      IsMaximalSplitTorus a ∧
        ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
          (torusCentralizer a).IsRepresentedBy c ∧ IsClosedSubgroup c ∧ IsTorus C := by
  obtain ⟨A, a, ha, hle⟩ :=
    hB.exists_maximalSplitTorus_centralizer_le_range hPD hG
  let d := torusCentralizerTorusDataOfSolvableContainment hDCR hG ha.1.1 a b
    hB.1.isClosedSubgroup hB.1.isSolvableGroupScheme hle
  exact ⟨A, a, ha, d.torus.toGrp, d.inclusion, d.represents, d.isClosedSubgroup, d.isTorus⟩

/-- Every quasi-split group has one maximal split torus with a closed torus
centralizer, conditional on dynamic reductivity and parabolic realization. -/
theorem IsQuasiSplit.exists_maximalSplitTorus_with_torusCentralizer
    (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsQuasiSplit G) :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G),
      IsMaximalSplitTorus a ∧
        ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
          (torusCentralizer a).IsRepresentedBy c ∧ IsClosedSubgroup c ∧ IsTorus C := by
  obtain ⟨B, b, hB⟩ := hG.exists_isGeometricBorelSubgroup
  exact hB.exists_maximalSplitTorus_with_torusCentralizer hDCR hPD hG.isConnectedReductive

end Langlands.GroupScheme
