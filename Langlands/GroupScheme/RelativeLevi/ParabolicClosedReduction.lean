import Langlands.GroupScheme.RelativeLevi.ParabolicLocalDynamicStatement
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedStatement
import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget

/-! # Closedness from an etale-local dynamic description -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A representative of a dynamic parabolic in an affine, locally finitely
presented group is closed, over any base scheme. -/
theorem isClosedSubgroup_of_isRepresentedBy_dynamicParabolic
    {S : Scheme.{u}} {G P : GroupScheme S} [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] (χ : (Gm S).toGrp ⟶ G) (i : P ⟶ G)
    (hi : (Dynamic.parabolic χ).IsRepresentedBy i) : IsClosedSubgroup i := by
  obtain ⟨H, j, hj, _, hrep⟩ := (dynamicBaseRepresentability S G χ).1
  exact hi.isClosedSubgroup hrep hj

set_option backward.isDefEq.respectTransparency.types false in
/-- Closedness of a monic group-scheme homomorphism can be checked on an
etale cover of the base scheme. -/
theorem isClosedSubgroup_of_etaleCover
    {S : Scheme.{u}} {G P : GroupScheme S} (i : P ⟶ G) [Mono i.hom.hom]
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hi : ∀ a, IsClosedSubgroup ((GroupScheme.baseChange (𝒰.f a)).map i)) :
    IsClosedSubgroup i := by
  have : Mono i.hom.hom.left := Over.mono_left_of_mono _
  apply (IsClosedImmersion.iff_isFinite_and_mono i.hom.hom.left).mpr
  refine ⟨?_, inferInstance⟩
  let 𝒱 := Scheme.Cover.changeProp (𝒰.pullback₁ G.X.hom)
    (Q := @Flat ⊓ @LocallyOfFinitePresentation)
    (fun a => by
      have := Scheme.Cover.map_prop (𝒰.pullback₁ G.X.hom) a
      exact ⟨inferInstance, inferInstance⟩)
  have : MorphismProperty.IsLocalAtTarget (@IsFinite.{u})
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage (@IsFinite.{u})
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd 𝒱.mem₀ ?_
  intro Y f _ hf
  obtain ⟨a⟩ := hf
  have hclosed : IsClosedImmersion ((GroupScheme.baseChange (𝒰.f a)).map i).hom.hom.left := hi a
  have hpb := (baseChange_map_isPullback (𝒰.f a) i).flip
  have hfinite : IsFinite ((GroupScheme.baseChange (𝒰.f a)).map i).hom.hom.left := inferInstance
  rw [← hpb.isoPullback_hom_snd,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)] at hfinite
  exact hfinite

set_option backward.isDefEq.respectTransparency.types false in
/-- The local dynamic description of a relative parabolic implies its
closedness, with exactly the quantifiers of the published target. -/
theorem relativeParabolicClosed_of_etaleLocalDynamic
    (hlocal : RelativeParabolicEtaleLocalDynamicStatement.{u}) :
    RelativeParabolicClosedStatement.{u} := by
  intro S G P i hG hi
  let := hi.mono
  obtain ⟨𝒰, h𝒰⟩ := hlocal S G P i hG hi
  apply isClosedSubgroup_of_etaleCover i 𝒰
  intro a
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have : IsAffineHom ((GroupScheme.baseChange (𝒰.f a)).obj G).X.hom :=
    MorphismProperty.pullback_snd _ _ hG.isAffineHom
  have : LocallyOfFinitePresentation ((GroupScheme.baseChange (𝒰.f a)).obj G).X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom (𝒰.f a)))
  obtain ⟨χ, hχ⟩ := h𝒰 a
  exact isClosedSubgroup_of_isRepresentedBy_dynamicParabolic χ _ hχ

end Langlands.GroupScheme
