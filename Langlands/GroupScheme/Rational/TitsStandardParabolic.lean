import Langlands.GroupScheme.Rational.StandardParabolic
import Mathlib.GroupTheory.DoubleCoset

/-! # Representative maps into double cosets of standard parabolics

The centralizer points `Z(k)` lie in every standard Levi and standard parabolic, so a
class `w ∈ relativeWeylGroup i = N(k)/Z(k)` has a well-defined double coset
`P_J(k) n P_K(k)` for any representative `n` (Borel–Tits 5.15, 5.20; Renard V.4.3).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

section Points

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Points centralizing the torus lie in every standard Levi. -/
theorem centralizerPoints_le_standardLeviPoints (J : Set (characterLattice T)) :
    centralizerPoints i ≤ standardLeviPoints i ν J := by
  rw [← torusCentralizer_carrier_base i]
  exact torusCentralizer_le_standardLevi i ν J _

/-- Points centralizing the torus lie in every standard parabolic. -/
theorem centralizerPoints_le_standardParabolicPoints (J : Set (characterLattice T)) :
    centralizerPoints i ≤ standardParabolicPoints i ν J :=
  fun _ hg => standardLevi_le_standardParabolic i ν J _
    (centralizerPoints_le_standardLeviPoints i ν J hg)

/-- The representative map `w ↦ P_J(k) n P_K(k)` from the relative Weyl group to the
double cosets of two standard parabolics, for any representative `n` of `w` in the
normalizer points. It does not depend on `n` since `Z(k) ≤ P_K(k)`. -/
def relativeWeylDoubleCoset (J K : Set (characterLattice T)) (w : relativeWeylGroup i) :
    DoubleCoset.Quotient
      (standardParabolicPoints i ν J : Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
      (standardParabolicPoints i ν K) :=
  Quotient.liftOn' w
    (fun n => DoubleCoset.mk (standardParabolicPoints i ν J) (standardParabolicPoints i ν K)
      (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab
      rw [DoubleCoset.eq]
      refine ⟨1, Subgroup.one_mem _, ((a⁻¹ * b : normalizerPoints i) :
        Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
        centralizerPoints_le_standardParabolicPoints i ν K hab, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, one_mul, mul_inv_cancel_left])

@[simp]
theorem relativeWeylDoubleCoset_mk (J K : Set (characterLattice T)) (n : normalizerPoints i) :
    relativeWeylDoubleCoset i ν J K (QuotientGroup.mk n) =
      DoubleCoset.mk (standardParabolicPoints i ν J) (standardParabolicPoints i ν K)
        (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
  rfl

/-- A normalizing point whose class lies in `standardRelativeWeylGroup i ν J` lies in the
standard Levi `L_J(k)`: it differs from a representative in `L_J(k)` by a point of `Z(k)`. -/
theorem coe_mem_standardLeviPoints_of_mk_mem (J : Set (characterLattice T))
    {n : normalizerPoints i}
    (hn : (QuotientGroup.mk n : relativeWeylGroup i) ∈ standardRelativeWeylGroup i ν J) :
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈ standardLeviPoints i ν J := by
  obtain ⟨m, hm, hmn⟩ := (mem_standardRelativeWeylGroup_iff i ν).1 hn
  have hz : m⁻¹ * n ∈ (centralizerPoints i).subgroupOf (normalizerPoints i) :=
    QuotientGroup.eq.1 hmn
  have hz' : ((m⁻¹ * n : normalizerPoints i) : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈
      centralizerPoints i := Subgroup.mem_subgroupOf.1 hz
  have h := Subgroup.mul_mem _ hm (centralizerPoints_le_standardLeviPoints i ν J hz')
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using h

/-- A normalizing point whose class lies in `standardRelativeWeylGroup i ν J` lies in the
standard parabolic `P_J(k)`. -/
theorem coe_mem_standardParabolicPoints_of_mk_mem (J : Set (characterLattice T))
    {n : normalizerPoints i}
    (hn : (QuotientGroup.mk n : relativeWeylGroup i) ∈ standardRelativeWeylGroup i ν J) :
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈ standardParabolicPoints i ν J :=
  standardLevi_le_standardParabolic i ν J _ (coe_mem_standardLeviPoints_of_mk_mem i ν J hn)

end Points

end Langlands.GroupScheme
