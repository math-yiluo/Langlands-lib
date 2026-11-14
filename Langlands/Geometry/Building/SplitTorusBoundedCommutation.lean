import Langlands.Geometry.Building.SplitTorusBoundedDetection
import Langlands.GroupScheme.Rational.TorusCentralizer

/-! # All-test commutation from bounded rational split-torus points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation k Γ₀)
    {A B G : GroupScheme (Spec (CommRingCat.of k))}

/-- Every rational point in the first group commutes with every bounded rational
point in the second group, after mapping both into the ambient group. -/
def KernelPointwiseCommute (i : A ⟶ G) (j : B ⟶ G) : Prop :=
  ∀ s : rationalPoints A, ∀ t : rationalPoints B,
    t ∈ characterValuationKernel v B →
      Commute (rationalPoints.map i s) (rationalPoints.map j t)

/-- For split tori in an affine group, rational commutation against the
character-valuation kernel implies commutation over every test scheme. -/
theorem commute_of_kernelPointwiseCommute
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)] [IsAffine G.X.left]
    (hA : IsSplitTorus A) (hB : IsSplitTorus B)
    (i : A ⟶ G) (j : B ⟶ G) (h : KernelPointwiseCommute v i j)
    (U : Over (Spec (CommRingCat.of k))) (s : U ⟶ A.X) (t : U ⟶ B.X) :
    Commute (s ≫ i.hom.hom) (t ≫ j.hom.hom) := by
  have he :
      (fst A.X B.X ≫ i.hom.hom) * (snd A.X B.X ≫ j.hom.hom) =
        (snd A.X B.X ≫ j.hom.hom) * (fst A.X B.X ≫ i.hom.hom) := by
    apply hom_ext_characterValuationKernel v (hA.tensor hB)
    intro x hx
    have ht : x ≫ snd A.X B.X ∈ characterValuationKernel v B :=
      map_characterValuationKernel_le v (snd A B) ⟨x, hx, rfl⟩
    simpa only [MonObj.comp_mul, Category.assoc, rationalPoints.map_apply] using
      (h (x ≫ fst A.X B.X) (x ≫ snd A.X B.X) ht).eq
  have hh := congrArg (fun q : (A ⊗ B).X ⟶ G.X => lift s t ≫ q) he
  change (s ≫ i.hom.hom) * (t ≫ j.hom.hom) =
    (t ≫ j.hom.hom) * (s ≫ i.hom.hom)
  simpa only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc] using hh

/-- The image of the first split torus is contained in the all-test centralizer
of the second if the required bounded rational points commute. -/
theorem range_le_torusCentralizer_of_kernelPointwiseCommute
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)] [IsAffine G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hA : IsSplitTorus A) (hT : IsSplitTorus T.toGrp)
    (i : A ⟶ G) (j : T.toGrp ⟶ G) (h : KernelPointwiseCommute v i j) :
    SubgroupFunctor.range i ≤ torusCentralizer j := by
  intro U g hg
  obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  intro V a t
  rw [← Category.assoc]
  exact commute_of_kernelPointwiseCommute v hA hT i j h V (a ≫ s) t

end Langlands.Geometry.Building
