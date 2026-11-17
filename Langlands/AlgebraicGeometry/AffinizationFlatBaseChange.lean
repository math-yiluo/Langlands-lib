import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Core

/-! # The canonical affinization square under flat affine base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffinizationFlatBaseChange

variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    [IsAffine Z] [IsAffine Y] [Flat g] [CompactSpace X] [QuasiSeparatedSpace X]

include h

/-- The naturality square of canonical affinization is cartesian after a
flat change between affine bases. -/
theorem isPullback_toSpecΓ :
    IsPullback P.toSpecΓ fst (Spec.map fst.appTop) X.toSpecΓ := by
  have hpo := LocallyQuasiFiniteDescent.isPushout_appTop_of_isPullback h
  have hR := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  have hY : IsPullback Y.toSpecΓ g (Spec.map g.appTop) Z.toSpecΓ :=
    IsPullback.of_horiz_isIso ⟨(Scheme.toSpecΓ_naturality g).symm⟩
  have hbig := h.flip.paste_horiz hY
  rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality] at hbig
  exact IsPullback.of_right hbig (Scheme.toSpecΓ_naturality fst).symm hR.flip

/-- The actual comparison isomorphism exhibiting that cartesian naturality square. -/
def naturalityPullbackIso :
    P ≅ pullback (Spec.map fst.appTop) X.toSpecΓ :=
  (isPullback_toSpecΓ h).isoPullback

@[reassoc (attr := simp)]
theorem naturalityPullbackIso_hom_fst :
    (naturalityPullbackIso h).hom ≫ pullback.fst _ _ = P.toSpecΓ :=
  (isPullback_toSpecΓ h).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem naturalityPullbackIso_hom_snd :
    (naturalityPullbackIso h).hom ≫ pullback.snd _ _ = fst :=
  (isPullback_toSpecΓ h).isoPullback_hom_snd

end Langlands.AlgebraicGeometry.AffinizationFlatBaseChange
