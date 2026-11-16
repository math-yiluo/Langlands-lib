import Langlands.GroupScheme.Reductive.DvrFpqcIsogenyReduction
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Affine and locally noetherian reductions for fibrewise isogenies -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- The reductive fibrewise-isogeny criterion over all affine bases. -/
def AffineReductiveFibrewiseIsogenyStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    ∀ f : G ⟶ H, IsFibrewiseIsogeny f → IsIsogeny f

/-- Isogenies of a specified homomorphism glue on any open cover of the base. -/
theorem isogeny_of_openCover {S : Scheme.{u}} (U : S.OpenCover)
    {G H : GroupScheme S} (f : G ⟶ H)
    (hf : ∀ i, IsIsogeny ((baseChange (U.f i)).map f)) : IsIsogeny f := by
  change isogenyProperty f.hom.hom.left
  let : IsZariskiLocalAtTarget isogenyProperty := by
    unfold isogenyProperty
    infer_instance
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := isogenyProperty)
    (U.pullback₁ H.X.hom)]
  intro i
  have hi : isogenyProperty ((baseChange (U.f i)).map f).hom.hom.left := hf i
  have hp := (baseChange_map_isPullback (U.f i) f).flip
  rw [← hp.isoPullback_hom_snd] at hi
  exact (isogenyProperty.cancel_left_of_respectsIso _ _).mp hi

/-- The affine criterion implies the unchanged criterion over every scheme. -/
theorem reductiveFibrewiseIsogeny_of_affine
    (haff : AffineReductiveFibrewiseIsogenyStatement.{u}) :
    ReductiveFibrewiseIsogenyStatement.{u} := by
  intro S G H hG hH f hf
  apply isogeny_of_openCover S.affineOpenCover.openCover f
  intro i
  exact haff (S.affineOpenCover.X i) _ _
    (hG.baseChange (S.affineOpenCover.f i))
    (hH.baseChange (S.affineOpenCover.f i)) _
    ((show IsFibrewiseIsogeny f from hf).baseChange (S.affineOpenCover.f i))

/-- The original criterion is equivalent to its restriction to affine bases. -/
theorem reductiveFibrewiseIsogeny_iff_affine :
    ReductiveFibrewiseIsogenyStatement.{u} ↔
      AffineReductiveFibrewiseIsogenyStatement.{u} := by
  constructor
  · intro h R _ G H hG hH f hf
    exact h _ G H hG hH f hf
  · exact reductiveFibrewiseIsogeny_of_affine

/-- The DVR criterion proves the result over every locally noetherian base. -/
theorem isogeny_of_fibrewise_of_dvr_criterion_of_locallyNoetherian
    (hdvr : DvrFibrewiseIsogenyStatement.{u})
    {S : Scheme.{u}} [IsLocallyNoetherian S] {G H : GroupScheme S}
    (hG : IsReductive G) (hH : IsReductive H)
    (f : G ⟶ H) (hf : IsFibrewiseIsogeny f) : IsIsogeny f := by
  apply isogeny_of_openCover S.affineOpenCover.openCover f
  intro i
  let : IsNoetherianRing (S.affineOpenCover.X i) :=
    isLocallyNoetherian_Spec.mp
      (inferInstance : IsLocallyNoetherian (S.affineOpenCover.openCover.X i))
  exact isogeny_of_fibrewise_of_dvr_criterion (R := S.affineOpenCover.X i) hdvr
    (hG.baseChange (S.affineOpenCover.f i))
    (hH.baseChange (S.affineOpenCover.f i)) _ (hf.baseChange (S.affineOpenCover.f i))

end Langlands.GroupScheme
