import Langlands.GroupScheme.Reductive.AlmostSimpleGenerationStatement
import Langlands.GroupScheme.Derived.ConnectedSmoothness
import Langlands.GroupScheme.Derived.Functoriality
import Langlands.GroupScheme.Derived.SemisimplePerfectReduction

/-! # Almost-simple perfectness and its generation consequence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An almost-simple group over any field is perfect for the full
scheme-theoretic derived subgroup functor. -/
theorem IsAlmostSimple.derivedSubgroup_eq_top
    {k : Type u} [Field k] {A : GroupScheme (Spec (CommRingCat.of k))}
    (hA : IsAlmostSimple A) : derivedSubgroup A = ⊤ := by
  let E := smoothConnectedCommutatorImage k A
    hA.isSemisimple.isConnectedReductive.smooth
    hA.isSemisimple.isConnectedReductive.isAffineHom
    hA.isSemisimple.isConnectedReductive.connectedSpace
  have hd := E.val.isDerivedSubgroup
  let : GeometricallyConnected E.val.group.X.hom := E.property.2.2.1
  have hconn : ConnectedSpace E.val.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := E.val.group.X.hom)
  rcases hA.normalSubgroup_trivial_or_full E.val.group E.val.inclusion
      hd.1 E.property.1 hconn hd.isNormal with hbot | htop
  · exfalso
    apply hA.noncommutative
    intro T x y
    have h := hd.containsCommutators T x y
    rw [hbot] at h
    change x * y * x⁻¹ * y⁻¹ = 1 at h
    change x * y = y * x
    rwa [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
  · exact hd.2.symm.trans htop

/-- Generation by normal almost-simple subgroups implies semisimple
perfectness over algebraically closed fields. -/
theorem algebraicallyClosedSemisimplePerfect_of_almostSimpleGeneration
    (hgen : SemisimpleAlmostSimpleGenerationStatement.{u}) :
    AlgebraicallyClosedSemisimplePerfectStatement.{u} := by
  intro k _ _ G hG
  let E := smoothConnectedCommutatorImage k G
    hG.isConnectedReductive.smooth hG.isConnectedReductive.isAffineHom
    hG.isConnectedReductive.connectedSpace
  have hd := E.val.isDerivedSubgroup
  have htop : SubgroupFunctor.range E.val.inclusion = ⊤ := by
    apply hgen k G hG E.val.group E.val.inclusion hd.1
    intro A a hA _ _ T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [hd.2]
    apply mem_derivedSubgroup_comp a
    rw [hA.derivedSubgroup_eq_top]
    exact Subgroup.mem_top y
  exact hd.2.symm.trans htop

/-- The same generation premise implies full semisimple perfectness over
arbitrary fields by faithfully flat descent from an algebraic closure. -/
theorem semisimplePerfect_of_almostSimpleGeneration
    (hgen : SemisimpleAlmostSimpleGenerationStatement.{u}) :
    SemisimplePerfectStatement.{u} :=
  semisimplePerfect_of_algebraicallyClosed
    (algebraicallyClosedSemisimplePerfect_of_almostSimpleGeneration hgen)

end Langlands.GroupScheme
