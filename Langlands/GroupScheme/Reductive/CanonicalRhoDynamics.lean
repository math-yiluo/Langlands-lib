import Langlands.GroupScheme.Reductive.IntegralOppositionRepresentative
import Langlands.GroupScheme.SplitExistence.IntegralBase
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Reductive.SameTorusDiagonalizable

/-! # Canonical polarized-rho dynamics on the original maximal torus -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.IntegralWeylVector

variable {J : Type u} {X : Type v} {Y : Type w}
    [AddCommGroup X] [AddCommGroup Y] [Fintype J]
    (P : RootDatum J X Y) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)

/-- The canonical root form pairs rho positively with every positive root. -/
theorem rootForm_rho_root_pos_of_isPos {i : J} (hi : b.IsPos i) :
    0 < P.RootForm (rho P b hspan) (P.root i) := by
  have hs (j : J) (hj : j ∈ b.support) :
      0 < P.RootForm (rho P b hspan) (P.root j) := by
    have he := GroupScheme.SplitExistence.two_mul_rootForm_root P (rho P b hspan) j
    rw [pairing_rho_simple P b hspan ⟨j, hj⟩, one_mul] at he
    have hl := GroupScheme.SplitExistence.four_le_rootForm_root P j
    omega
  apply hi.induction_on_add hs
  intro j l m hm hj hl
  rw [hm, map_add]
  exact add_pos hj (hs l hl)

/-- The polarization of rho has precisely the positive-root signs of the base. -/
theorem pairing_root_polarization_rho_pos_iff (i : J) :
    0 < P.toLinearMap (P.root i) (P.Polarization (rho P b hspan)) ↔ b.IsPos i := by
  rw [P.toLinearMap_apply_apply_Polarization]
  constructor
  · intro hp
    by_contra hn
    let := P.indexNeg
    have hneg := rootForm_rho_root_pos_of_isPos P b hspan
      ((RootPairing.Base.IsPos.neg_iff_not b i).mpr hn)
    change 0 < P.RootForm (rho P b hspan) (P.root (P.reflectionPerm i i)) at hneg
    simp only [P.root_reflectionPerm, P.reflection_apply_self, map_neg] at hneg
    omega
  · exact rootForm_rho_root_pos_of_isPos P b hspan

end Langlands.IntegralWeylVector

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {j : T.toGrp ⟶ G}
    {J : Type v} [Fintype J]
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)

namespace IsRootDatumOf

variable {P} (hP : IsRootDatumOf j P)

include hP

/-- Pairing an actual root with polarized rho detects the supplied base's sign. -/
theorem latticePairing_root_polarization_rho_pos_iff (i : J) :
    0 < latticePairing T (P.root i) (P.Polarization (IntegralWeylVector.rho P b hspan)) ↔
      b.IsPos i := by
  rw [← hP.1]
  exact IntegralWeylVector.pairing_root_polarization_rho_pos_iff P b hspan i

/-- The actual positive-root set is exactly the image of the base-positive indices. -/
theorem positiveRoots_polarization_rho :
    {a ∈ roots j | 0 < latticePairing T a
      (P.Polarization (IntegralWeylVector.rho P b hspan))} =
        P.root '' {i | b.IsPos i} := by
  ext a
  constructor
  · rintro ⟨ha, hp⟩
    obtain ⟨i, rfl⟩ : ∃ i, P.root i = a := by
      rwa [← hP.2.1, Set.mem_range] at ha
    exact ⟨i, (hP.latticePairing_root_polarization_rho_pos_iff b hspan i).mp hp, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨?_, (hP.latticePairing_root_polarization_rho_pos_iff b hspan i).mpr hi⟩
    rw [← hP.2.1]
    exact Set.mem_range_self i

/-- The canonical rho cocharacter, certified generic with the exact root signs. -/
def positiveRhoCocharacter :
    {ν : cocharacterLattice T // IsGenericCocharacter j ν ∧
      ∀ i : J, (0 < latticePairing T (P.root i) ν ↔ b.IsPos i)} :=
  ⟨P.Polarization (IntegralWeylVector.rho P b hspan),
    hP.polarization_rho_isGeneric b hspan,
    hP.latticePairing_root_polarization_rho_pos_iff b hspan⟩

@[simp] theorem positiveRhoCocharacter_val :
    (hP.positiveRhoCocharacter b hspan).val =
      P.Polarization (IntegralWeylVector.rho P b hspan) := rfl

variable (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hj : IsMaximalTorus j)

include hG hT hj

/-- Polarized rho centralizes exactly the original maximal torus on all tests. -/
theorem centralizer_polarization_rho :
    Dynamic.centralizer (CommGroupScheme.groupHom
      (P.Polarization (IntegralWeylVector.rho P b hspan)) ≫ j) =
        SubgroupFunctor.range j := by
  rw [genericCentralizer k G hG T j (hj.isMaximalSplitTorus hT) _
    (hP.polarization_rho_isGeneric b hspan)]
  exact maximalTorusCentralizer k G hG T j hj

/-- The original torus embedding represents the canonical dynamic centralizer. -/
theorem isRepresentedBy_centralizer_polarization_rho :
    (Dynamic.centralizer (CommGroupScheme.groupHom
      (P.Polarization (IntegralWeylVector.rho P b hspan)) ≫ j)).IsRepresentedBy j := by
  let : IsClosedImmersion j.hom.hom.left := hj.2.1
  exact ⟨Over.mono_of_mono_left _,
    (hP.centralizer_polarization_rho b hspan hG hT hj).symm⟩

end IsRootDatumOf

end Langlands.GroupScheme
