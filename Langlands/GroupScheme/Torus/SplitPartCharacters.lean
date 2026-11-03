import Langlands.GroupScheme.Torus.CocharacterDetection
import Langlands.GroupScheme.Rational.TorusSplitPart

/-! # Rational characters on the largest split subtorus of a torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Restriction to the largest split subtorus detects every rational character of a torus. -/
theorem IsLargestSplitSubtorus.characterRestrict_injective
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    {i : A.toGrp ⟶ T.toGrp} (hi : IsLargestSplitSubtorus i)
    (hT : IsTorus T.toGrp) : Function.Injective (characterRestrict i) := by
  rw [injective_iff_map_eq_zero]
  intro χ hχ
  by_contra hne
  obtain ⟨φ, hφ⟩ :=
    CocharacterDetection.exists_gm_characterRestrict_ne_zero_of_isTorus hT hne
  obtain ⟨g, hg, _⟩ := hi.2 (Gm (Spec (CommRingCat.of k))) φ isSplitTorus_gm
  apply hφ
  rw [← hg, characterRestrict_comp, AddMonoidHom.comp_apply, hχ, map_zero]

/-- Identify rational torus characters with their image in the characters of the split part. -/
noncomputable def IsLargestSplitSubtorus.characterRestrictEquivRange
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    {i : A.toGrp ⟶ T.toGrp} (hi : IsLargestSplitSubtorus i)
    (hT : IsTorus T.toGrp) :
    rationalCharacters T.toGrp ≃+ (characterRestrict i).range :=
  AddMonoidHom.ofInjective (hi.characterRestrict_injective hT)

@[simp]
theorem IsLargestSplitSubtorus.characterRestrictEquivRange_apply
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    {i : A.toGrp ⟶ T.toGrp} (hi : IsLargestSplitSubtorus i)
    (hT : IsTorus T.toGrp) (χ : rationalCharacters T.toGrp) :
    (hi.characterRestrictEquivRange hT χ : rationalCharacters A.toGrp) =
      characterRestrict i χ := rfl

/-- The same detection holds for any maximal split subtorus of an affine torus. -/
theorem IsMaximalSplitTorus.characterRestrict_injective_of_isTorus
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    {i : A.toGrp ⟶ T.toGrp} (hi : IsMaximalSplitTorus i)
    (hT : IsTorus T.toGrp) : Function.Injective (characterRestrict i) := by
  have : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  exact hi.isLargestSplitSubtorus.characterRestrict_injective hT

end Langlands.GroupScheme
