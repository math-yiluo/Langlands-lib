import Langlands.GroupScheme.Rational.SplitUnipotentRationalDensity
import Langlands.GroupScheme.Rational.SplitTorusRationalDetection
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Detection of functions and factorizations by rational points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RationalDensity

open Langlands.AlgebraicGeometry.PointTopology RelativeRoot

variable {k : Type u} [Field k]

/-- A morphism to an affine scheme factors through a closed immersion when the kernel of the
closed immersion on global sections is contained in the kernel of the morphism. -/
theorem exists_factor_of_ker_le {X Y Z : Over (Spec (CommRingCat.of k))} [IsAffine Z.left]
    (j : Y ⟶ Z) [IsClosedImmersion j.left] (f : X ⟶ Z)
    (hk : RingHom.ker j.left.appTop.hom ≤ RingHom.ker f.left.appTop.hom) :
    ∃ l : X ⟶ Y, l ≫ j = f := by
  have hker : j.left.ker ≤ f.left.ker := by
    rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
    apply Scheme.IdealSheafData.le_of_isAffine
    simpa using hk
  let l := IsClosedImmersion.lift j.left f.left hker
  have hlj : l ≫ j.left = f.left := IsClosedImmersion.lift_fac _ _ _
  refine ⟨Over.homMk l ?_, ?_⟩
  · rw [← Over.w j, ← Category.assoc, hlj, Over.w f]
  · exact Over.OverMorphism.ext hlj

/-- On a reduced scheme with dense rational points, rational points detect global functions. -/
theorem rationalPointsDetectFunctions_of_dense {X : Over (Spec (CommRingCat.of k))}
    [IsReduced X.left] (hX : HasDenseRationalPoints k X) : RationalPointsDetectFunctions X := by
  intro s hs
  rw [← AlgebraicGeometry.basicOpen_eq_bot_iff]
  by_contra hne
  obtain ⟨z, hzO, hz⟩ := hX.inter_open_nonempty (X.left.basicOpen s : Set X.left)
    (X.left.basicOpen s).isOpen ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne)
  simp only [Set.mem_iUnion, Set.mem_range] at hz
  obtain ⟨x, a, rfl⟩ := hz
  have ha : a ∈ x.left ⁻¹ᵁ X.left.basicOpen s := hzO
  rw [Scheme.preimage_basicOpen_top, hs x, Scheme.basicOpen_zero] at ha
  simp at ha

/-- A morphism whose rational points detect functions on its source factors through a closed
immersion into an affine scheme as soon as it does so at every rational point. -/
theorem RationalPointsDetectFunctions.exists_factor {X Y Z : Over (Spec (CommRingCat.of k))}
    (hX : RationalPointsDetectFunctions X) [IsAffine Z.left]
    (j : Y ⟶ Z) [IsClosedImmersion j.left] (f : X ⟶ Z)
    (h : ∀ x : RationalPoint k X, ∃ y : RationalPoint k Y, y ≫ j = x ≫ f) :
    ∃ l : X ⟶ Y, l ≫ j = f := by
  apply exists_factor_of_ker_le j f
  intro s hs
  change f.left.appTop s = 0
  apply hX
  intro x
  obtain ⟨y, hy⟩ := h x
  have hh := congrArg (fun q : RationalPoint k Z => q.left.appTop s) hy
  simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hh
  rw [← hh, RingHom.mem_ker.mp hs, map_zero]

/-- The unit object over a field has dense rational points. -/
theorem hasDenseRationalPoints_tensorUnit :
    HasDenseRationalPoints k (𝟙_ (Over (Spec (CommRingCat.of k)))) := by
  apply Dense.mono (Set.subset_iUnion _ (𝟙 _ : RationalPoint k (𝟙_ _)))
  apply Function.Surjective.denseRange
  intro z
  exact ⟨z, rfl⟩

/-- An object smooth over a field with dense rational points: rational points detect functions. -/
theorem rationalPointsDetectFunctions_of_smooth {X : Over (Spec (CommRingCat.of k))}
    [Smooth X.hom] (hX : HasDenseRationalPoints k X) : RationalPointsDetectFunctions X := by
  have : IsReduced X.left :=
    AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ X.hom
  exact rationalPointsDetectFunctions_of_dense hX

end Langlands.GroupScheme.RationalDensity
