import Langlands.AlgebraicGeometry.Modules.PushforwardBaseChangeComposition

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {S S' X X' : Scheme.{u}} (b : S' ⟶ S) (f : X ⟶ S)
  (f' : X' ⟶ S') (p : X' ⟶ X) [IsOpenImmersion b] [IsOpenImmersion p]
  (h : IsPullback p f' f b)

include h in
lemma isIso_restrict_pushforward_restrictionUnit (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor b).map ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction p).unit.app M))) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  change IsIso (((Scheme.Modules.restrictAdjunction p).unit.app M).app (f ⁻¹ᵁ b ''ᵁ U))
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  have he : p ''ᵁ p ⁻¹ᵁ (f ⁻¹ᵁ b ''ᵁ U) = f ⁻¹ᵁ b ''ᵁ U := by
    rw [← IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h.flip U,
      p.preimage_image_eq]
  have hi : homOfLE (p.image_preimage_le (f ⁻¹ᵁ b ''ᵁ U)) = eqToHom he := Subsingleton.elim _ _
  rw [hi]
  infer_instance

/-- The comparison computed using restriction adjunctions. -/
def restrictionCartesianBaseChange (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict b ⟶
      (Scheme.Modules.pushforward f').obj (M.restrict p) :=
  ((Scheme.Modules.restrictAdjunction b).homEquiv _ _).symm
    ((Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictAdjunction p).unit.app M) ≫
      (pushforwardSquareIso b f f' p h.w).hom.app (M.restrict p))

lemma isIso_restrictionCartesianBaseChange (M : X.Modules) :
    IsIso (restrictionCartesianBaseChange b f f' p h M) := by
  unfold restrictionCartesianBaseChange
  rw [Adjunction.homEquiv_counit, Functor.map_comp]
  haveI := isIso_restrict_pushforward_restrictionUnit b f f' p h M
  infer_instance

lemma pushforwardBaseChange_eq_restrictionCartesianBaseChange (M : X.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback b).hom.app ((Scheme.Modules.pushforward f).obj M) ≫
      pushforwardBaseChange b f f' p h.w M =
    restrictionCartesianBaseChange b f f' p h M ≫
      (Scheme.Modules.pushforward f').map ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app M) := by
  apply ((Scheme.Modules.restrictAdjunction b).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  change (Scheme.Modules.restrictAdjunction b).homEquiv _ _
      (((Scheme.Modules.restrictAdjunction b).leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction b)).hom.app _) ≫ _ = _
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    ← Adjunction.homEquiv_unit, pushforwardBaseChange, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, restrictionCartesianBaseChange, Equiv.apply_symm_apply]
  have hn := (pushforwardSquareIso b f f' p h.w).hom.naturality
    ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp]
  rw [Scheme.Modules.restrictFunctorIsoPullback, Adjunction.unit_leftAdjointUniq_hom_app]

lemma isIso_pushforwardBaseChange_of_isOpenImmersion (M : X.Modules) :
    IsIso (pushforwardBaseChange b f f' p h.w M) := by
  haveI := isIso_restrictionCartesianBaseChange b f f' p h M
  have hi : IsIso ((Scheme.Modules.restrictFunctorIsoPullback b).hom.app
      ((Scheme.Modules.pushforward f).obj M) ≫ pushforwardBaseChange b f f' p h.w M) := by
    rw [pushforwardBaseChange_eq_restrictionCartesianBaseChange b f f' p h M]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((Scheme.Modules.restrictFunctorIsoPullback b).hom.app ((Scheme.Modules.pushforward f).obj M))
    (pushforwardBaseChange b f f' p h.w M)

/-- The actual Cartesian base-change comparison for an open immersion. -/
def openCartesianBaseChangeIso (M : X.Modules) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pushforward f).obj M) ≅
      (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback p).obj M) := by
  haveI := isIso_pushforwardBaseChange_of_isOpenImmersion b f f' p h M
  exact asIso (pushforwardBaseChange b f f' p h.w M)

end Langlands.AlgebraicGeometry.Modules.DerivedSections
