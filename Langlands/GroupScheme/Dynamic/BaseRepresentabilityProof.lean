import Langlands.GroupScheme.Dynamic.BaseRepresentabilityStatement
import Langlands.GroupScheme.Dynamic.AffineFinitePresentation
import Langlands.GroupScheme.Dynamic.OrbitLocality
import Langlands.GroupScheme.Dynamic.BaseChange
import Langlands.GroupScheme.SubgroupFunctor.ClosedGluing

/-! # Finitely presented closed dynamic subgroups over arbitrary base schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open SubgroupFunctor Langlands.GroupScheme.Dynamic DynamicBaseRepresentability

/-- **Dynamic representability over an arbitrary base scheme.**
The orbit-extension, identity-limit and centralizer subgroups of an affine,
locally finitely presented group scheme are finitely presented closed
subgroup schemes. -/
theorem dynamicBaseRepresentability : DynamicBaseRepresentabilityStatement.{u} := by
  intro S G _ _ χ
  let 𝒜 := S.affineOpenCover
  have hglobal (F : SubgroupFunctor G) (hF : IsZariskiLocal F)
      (h : ∀ i, ∃ (H : GroupScheme (𝒜.openCover.X i))
        (j : H ⟶ (GroupScheme.baseChange (𝒜.f i)).obj G),
        IsClosedImmersion j.hom.hom.left ∧
          LocallyOfFinitePresentation j.hom.hom.left ∧
            (F.baseChange (𝒜.f i)).IsRepresentedBy j) :
      ∃ (H : GroupScheme S) (j : H ⟶ G),
        IsClosedImmersion j.hom.hom.left ∧
          LocallyOfFinitePresentation H.X.hom ∧ F.IsRepresentedBy j := by
    obtain ⟨H, j, hc, hlfp, hr⟩ :=
      F.exists_closed_finitelyPresented_of_openCover hF 𝒜.openCover h
    refine ⟨H, j, hc, ?_, hr⟩
    have : LocallyOfFinitePresentation j.hom.hom.left := hlfp
    rw [← Over.w j.hom.hom]
    infer_instance
  refine ⟨hglobal _ (DynamicLocality.parabolic_isZariskiLocal χ) ?_,
    hglobal _ (DynamicLocality.unipotent_isZariskiLocal χ) ?_,
    hglobal _ (DynamicLocality.centralizer_isZariskiLocal χ) ?_⟩
  · intro i
    let Gi := (GroupScheme.baseChange (𝒜.f i)).obj G
    have : IsAffineHom Gi.X.hom :=
      inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (𝒜.f i)))
    have : IsAffine Gi.X.left := isAffine_of_isAffineHom Gi.X.hom
    have : LocallyOfFiniteType Gi.X.hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom (𝒜.f i)))
    let χi := baseChangeCocharacter (𝒜.f i) χ
    refine ⟨Affine.parabolicScheme χi, Affine.parabolicHom χi,
      Affine.isClosedSubgroup_parabolicHom χi,
      locallyOfFinitePresentation_parabolicHom χi, ?_⟩
    rw [← parabolic_baseChange]
    exact Affine.isRepresentedBy_parabolicHom χi
  · intro i
    let Gi := (GroupScheme.baseChange (𝒜.f i)).obj G
    have : IsAffineHom Gi.X.hom :=
      inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (𝒜.f i)))
    have : IsAffine Gi.X.left := isAffine_of_isAffineHom Gi.X.hom
    have : LocallyOfFiniteType Gi.X.hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom (𝒜.f i)))
    let χi := baseChangeCocharacter (𝒜.f i) χ
    refine ⟨Affine.unipotentScheme χi, Affine.unipotentHom χi,
      Affine.isClosedSubgroup_unipotentHom χi,
      locallyOfFinitePresentation_unipotentHom χi, ?_⟩
    rw [← unipotent_baseChange]
    exact Affine.isRepresentedBy_unipotentHom χi
  · intro i
    let Gi := (GroupScheme.baseChange (𝒜.f i)).obj G
    have : IsAffineHom Gi.X.hom :=
      inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (𝒜.f i)))
    have : IsAffine Gi.X.left := isAffine_of_isAffineHom Gi.X.hom
    have : LocallyOfFiniteType Gi.X.hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom (𝒜.f i)))
    let χi := baseChangeCocharacter (𝒜.f i) χ
    refine ⟨Affine.centralizerScheme χi, Affine.centralizerHom χi,
      Affine.isClosedSubgroup_centralizerHom χi,
      locallyOfFinitePresentation_centralizerHom χi, ?_⟩
    rw [← centralizer_baseChange]
    exact Affine.isRepresentedBy_centralizerHom χi

end Langlands.GroupScheme
