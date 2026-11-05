import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionRepresentability
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteAffineOpen
import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneAmpleProof
import Langlands.AlgebraicGeometry.ProjectiveSpace.Structure

/-! # Weil restriction from an actual quasi-projective immersion -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

/-- A locally closed subscheme of a scheme carrying an ample line bundle
has affine neighborhoods for all its finite sets of underlying points. -/
theorem hasFiniteAffineNeighborhoods_of_immersion_into_ample
    {X Z : Scheme.{u}} (f : X ⟶ Z) [IsImmersion f]
    (L : Picard.LineBundle Z) (hL : L.IsAmple) :
    HasFiniteAffineNeighborhoods X := by
  intro E hE
  let W := f.coborderRange
  have hEW : f '' E ⊆ (W : Set Z) := by
    rintro _ ⟨x, _, rfl⟩
    change f x ∈ f.coborderRange
    have hx : (f.liftCoborder ≫ f.coborderRange.ι) x = f x :=
      congrArg (fun g : X ⟶ Z => g x) f.liftCoborder_ι
    exact hx ▸ (f.liftCoborder x).property
  obtain ⟨V, hV, hEV, hVW⟩ := Picard.exists_isAffineOpen_of_finite_of_ample
    Z L hL (f '' E) W (hE.image f) hEW
  have ha : IsAffineOpen (W.ι ⁻¹ᵁ V) :=
    hV.preimage_of_isOpenImmersion W.ι (by
      rintro x hx
      exact ⟨⟨x, hVW hx⟩, rfl⟩)
  have hb : IsAffineOpen (f.liftCoborder ⁻¹ᵁ (W.ι ⁻¹ᵁ V)) :=
    ha.preimage f.liftCoborder
  have hc : f.liftCoborder ⁻¹ᵁ (W.ι ⁻¹ᵁ V) = f ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, f.liftCoborder_ι]
  refine ⟨⟨f ⁻¹ᵁ V, hc ▸ hb⟩, ?_⟩
  intro x hx
  exact hEV ⟨x, hx, rfl⟩

/-- Every finite set on a scheme with an actual projective-space immersion
is contained in an affine open, using the proved ampleness of `𝒪(1)`. -/
theorem hasFiniteAffineNeighborhoods_of_projectiveImmersion
    (R : Type u) [CommRing R] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ ProjectiveSpace R n) [IsImmersion i] :
    HasFiniteAffineNeighborhoods X := by
  obtain ⟨L, _, hL⟩ := projectiveSpaceTwistOneAmple R n
  exact hasFiniteAffineNeighborhoods_of_immersion_into_ample i L hL

/-- An immersion over the base into actual projective space makes the
original structure morphism separated. -/
theorem isSeparated_of_projectiveImmersion
    (R : Type u) [CommRing R] (Y : Over (Spec (CommRingCat.of R)))
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace R n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec R n = Y.hom) :
    IsSeparated Y.hom := by
  rw [← hi]
  infer_instance

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

/-- The actual affine-chart gluing represents restriction of scalars for
a scheme with a given projective-space immersion over the base. The affine
neighborhood and separatedness premises are proved from that immersion. -/
def projectiveImmersionWeilRestrictionTestEquiv
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ affineChartWeilRestriction A B Y) ≃ (ringBaseChange A B T ⟶ Y) := by
  letI := isSeparated_of_projectiveImmersion B Y n i hi
  exact affineChartWeilRestrictionTestEquiv A B Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n i) T

/-- The forward map is exactly the previously constructed counit comparison. -/
@[simp]
theorem projectiveImmersionWeilRestrictionTestEquiv_apply
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A B Y) :
    projectiveImmersionWeilRestrictionTestEquiv A B Y n i hi T p =
      affineChartWeilRestrictionComparison A B Y T p := rfl

/-- The representing equivalence is natural for all test schemes. -/
theorem projectiveImmersionWeilRestrictionTestEquiv_natural
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    {T S : Over (Spec (CommRingCat.of A))} (f : T ⟶ S)
    (p : S ⟶ affineChartWeilRestriction A B Y) :
    projectiveImmersionWeilRestrictionTestEquiv A B Y n i hi T (f ≫ p) =
      (Over.pullback (Spec.algebraMap A B)).map f ≫
        projectiveImmersionWeilRestrictionTestEquiv A B Y n i hi S p :=
  affineChartWeilRestrictionComparison_natural A B Y f p

/-- The inverse is natural as an actual morphism into the same glued scheme. -/
theorem projectiveImmersionWeilRestrictionTestEquiv_symm_natural
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    {T S : Over (Spec (CommRingCat.of A))} (f : T ⟶ S)
    (q : ringBaseChange A B S ⟶ Y) :
    (projectiveImmersionWeilRestrictionTestEquiv A B Y n i hi T).symm
        ((Over.pullback (Spec.algebraMap A B)).map f ≫ q) =
      f ≫ (projectiveImmersionWeilRestrictionTestEquiv A B Y n i hi S).symm q := by
  let := isSeparated_of_projectiveImmersion B Y n i hi
  exact affineChartWeilRestrictionInverse_natural A B Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n i) f q

end Langlands.AlgebraicGeometry.PointTopology
