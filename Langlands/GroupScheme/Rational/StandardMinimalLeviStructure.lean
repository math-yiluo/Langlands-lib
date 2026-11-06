import Langlands.GroupScheme.Rational.StandardMinimalLeviMultiplication
import Langlands.GroupScheme.Rational.AffineGeometricUnipotentRadical
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Reductivity and geometric radicals for the canonical minimal standard Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Standard

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hG hi hν

/-- The actual canonical empty-index standard Levi is connected reductive. -/
theorem isConnectedReductive_emptyLevi :
    IsConnectedReductive (leviScheme i ν ∅) := by
  have hL : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
      (leviHom i ν ∅) := by
    rw [← standardLevi_empty_eq_dynamic_of_generic i ν hG hi hν]
    exact isRepresentedBy_leviHom i ν ∅
  exact dynamicCentralizerReductive k G hG (CommGroupScheme.groupHom ν ≫ i)
    (leviScheme i ν ∅) (leviHom i ν ∅) (isClosedSubgroup_leviHom i ν ∅) hL

/-- The canonical empty-index unipotent inclusion has the full geometric
unipotent radical property, including geometric greatestness. -/
theorem isGeometricUnipotentRadical_empty :
    IsGeometricUnipotentRadical (unipotentToParabolic i ν ∅) := by
  let : Smooth G.X.hom := hG.smooth
  have hP : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
      (parabolicHom i ν ∅) := by
    rw [← standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν]
    exact isRepresentedBy_parabolicHom i ν ∅
  have hU : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
      (unipotentToParabolic i ν ∅ ≫ parabolicHom i ν ∅) := by
    rw [unipotentToParabolic_comp, ← standardUnipotent_empty_eq_dynamic i ν hG hi]
    exact isRepresentedBy_unipotentHom i ν ∅
  have hL : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
      (leviHom i ν ∅) := by
    rw [← standardLevi_empty_eq_dynamic_of_generic i ν hG hi hν]
    exact isRepresentedBy_leviHom i ν ∅
  exact Dynamic.isGeometricUnipotentRadical_of_centralizer
    (CommGroupScheme.groupHom ν ≫ i) (leviHom i ν ∅)
    (parabolicHom i ν ∅) (unipotentToParabolic i ν ∅) hP hU hL
    (isConnectedReductive_emptyLevi i ν hG hi hν)

/-- The canonical empty-index unipotent inclusion is the radical over the
ground field and remains the radical after algebraic closure. -/
theorem isLeviGeometricUnipotentRadical_empty :
    LeviSubgroup.IsGeometricUnipotentRadical (unipotentToParabolic i ν ∅) := by
  let : IsAffineHom (parabolicScheme i ν ∅).X.hom :=
    (isClosedSubgroup_parabolicHom i ν ∅).isAffineHom
  exact (isGeometricUnipotentRadical_empty i ν hG hi hν).leviSubgroup

/-- The actual canonical empty-index Levi inclusion is a rational Levi. -/
theorem isRationalLeviSubgroup_empty :
    IsRationalLeviSubgroup (leviToParabolic i ν ∅) := by
  let : IsAffineHom (parabolicScheme i ν ∅).X.hom :=
    (isClosedSubgroup_parabolicHom i ν ∅).isAffineHom
  have hl : IsClosedSubgroup (leviToParabolic i ν ∅) :=
    IsClosedSubgroup.of_comp (isClosedSubgroup_parabolicHom i ν ∅)
      (by rw [leviToParabolic_comp]; exact isClosedSubgroup_leviHom i ν ∅)
  exact IsRationalLeviSubgroup.of_geometricUnipotentRadical hl
    (isConnectedReductive_emptyLevi i ν hG hi hν)
    (isGeometricUnipotentRadical_empty i ν hG hi hν)
    (isIso_emptySubgroupMultiplication i ν hG hi hν)

end Standard

/-- The canonical Levi and geometric radical clauses needed in the minimal
standard Siegel setup, for a maximal split torus and a generic cocharacter. -/
def StandardMinimalLeviStructureStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T),
    IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
      IsConnectedReductive (Standard.leviScheme i ν ∅) ∧
        IsRationalLeviSubgroup (Standard.leviToParabolic i ν ∅) ∧
        LeviSubgroup.IsGeometricUnipotentRadical (Standard.unipotentToParabolic i ν ∅)

/-- The canonical Levi and radical clauses follow from the published dynamic
centralizer theorem and the canonical all-test comparisons. -/
theorem standardMinimalLeviStructure : StandardMinimalLeviStructureStatement.{u} := by
  intro k _ G _ T i ν hG hi hν
  exact ⟨Standard.isConnectedReductive_emptyLevi i ν hG hi hν,
    Standard.isRationalLeviSubgroup_empty i ν hG hi hν,
    Standard.isLeviGeometricUnipotentRadical_empty i ν hG hi hν⟩

end Langlands.GroupScheme
