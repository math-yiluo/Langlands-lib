import Langlands.GroupScheme.Rational.DerivedRootTransport
import Langlands.GroupScheme.Derived.TorusTangent
import Langlands.GroupScheme.Lie.TargetCoefficients
import Langlands.GroupScheme.Torus.WeightRestriction

/-! # Relative roots through the actual derived inclusion -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {T A S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (e : T ⟶ S) (c : A ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (d : D ⟶ G) (hd : IsDerivedSubgroup d)
    (h : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp) (hS : IsSplitTorus S.toGrp)
    (hA : IsSplitTorus A.toGrp)
    [hpflat : Flat (centralComplementProduct e c).hom.hom.left]
    [hpsurj : Surjective (centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))

include hpflat hpsurj hd h hT hS hA hc in
/-- Restriction of an actual ambient root is an actual derived root. -/
theorem mem_relativeRoots_precomp_derived
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    e ≫ a ∈ relativeRoots j := by
  classical
  have hz := root_restrict_eq_zero_of_isCentral i c hA hc ha
  refine ⟨precomp_ne_zero_of_centralComplement e c a hz ha.1, ?_⟩
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha.2
  have hXe : X ∈ weightSpace (j ≫ d) (e ≫ a) := by
    rw [h]
    exact weightSpace_le_comp e i a hX
  have hXrange : X ∈ LinearMap.range (Lie.targetMapLinear d k) :=
    hd.weightSpace_le_range_targetMapLinear i hS ha.1 hX
  obtain ⟨Y, hY, hYX⟩ := Lie.exists_weightSpace_preimage d j hT hXe hXrange
  intro hbot
  rw [hbot, Submodule.mem_bot] at hY
  rw [hY, map_zero] at hYX
  exact hX0 hYX.symm

include hd h hT hS in
omit [LocallyOfFiniteType D.X.hom] in
/-- Every derived root is the restriction of an ambient root. -/
theorem exists_relativeRoot_precomp_eq_derived
    {b : characterLattice T} (hb : b ∈ relativeRoots j) :
    ∃ a ∈ relativeRoots i, e ≫ a = b := by
  have : Mono d.hom.hom := hd.isRepresentedBy.1
  have hb' : b ∈ roots (CommGroupScheme.groupHom e ≫ i) := by
    rw [← h]
    exact roots_subset_comp d j hb
  exact ((mem_roots_comp_iff hS hT e i b).mp hb').2

include hpflat hpsurj hA hc in
/-- Restriction is injective on the actual ambient root set because every
root vanishes on the central complement. -/
theorem precomp_injective_relativeRoots_derived
    {a b : characterLattice S} (ha : a ∈ relativeRoots i)
    (hb : b ∈ relativeRoots i) (hab : e ≫ a = e ≫ b) : a = b := by
  by_contra hne
  have hz : c ≫ (a - b) = 0 := by
    rw [Preadditive.comp_sub, root_restrict_eq_zero_of_isCentral i c hA hc ha,
      root_restrict_eq_zero_of_isCentral i c hA hc hb, sub_self]
  have he := precomp_ne_zero_of_centralComplement e c (a - b) hz (sub_ne_zero.mpr hne)
  apply he
  rw [Preadditive.comp_sub, hab, sub_self]

/-- The actual relative-root bijection through a derived inclusion, with
forward map literal character restriction to the retained torus. -/
def derivedRelativeRootEquiv : relativeRoots i ≃ relativeRoots j :=
  Equiv.ofBijective
    (fun a => ⟨e ≫ a.val,
      mem_relativeRoots_precomp_derived e c j i d hd h hT hS hA hc a.property⟩)
    ⟨fun a b hab => Subtype.ext
      (precomp_injective_relativeRoots_derived e c i hA hc a.property b.property
        (congrArg Subtype.val hab)), by
      intro b
      obtain ⟨a, ha, hab⟩ := exists_relativeRoot_precomp_eq_derived e j i d hd h hT hS b.property
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩⟩

@[simp]
theorem derivedRelativeRootEquiv_val (a : relativeRoots i) :
    (derivedRelativeRootEquiv e c j i d hd h hT hS hA hc a : characterLattice T) =
      e ≫ a.val := rfl

end Langlands.GroupScheme.RelativeRoot
