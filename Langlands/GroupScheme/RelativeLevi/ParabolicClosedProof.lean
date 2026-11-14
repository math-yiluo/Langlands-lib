import Langlands.GroupScheme.RelativeLevi.ParabolicClosedReduction
import Langlands.GroupScheme.RelativeLevi.ParabolicPointedLifting
import Langlands.GroupScheme.RelativeLevi.LocalDynamicComparison
import Langlands.GroupScheme.RelativeParabolicNormalizerReduction

/-! # Relative parabolic closedness from pointed dynamic comparison -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- An actual representative on an iterated pullback gives one on the direct
pullback, with the cocharacter transported by the canonical ambient comparison. -/
theorem isRepresentedBy_dynamicParabolic_direct
    {S U V : Scheme.{u}} {G P : GroupScheme S} (i : P ⟶ G)
    (p : U ⟶ S) (q : V ⟶ U)
    (χ : (Gm V).toGrp ⟶ (baseChange q).obj ((baseChange p).obj G))
    (hχ : (Dynamic.parabolic χ).IsRepresentedBy
      ((baseChange q).map ((baseChange p).map i))) :
    (Dynamic.parabolic (χ ≫
      (Descent.pullbackComparison p q (q ≫ p) rfl G).hom)).IsRepresentedBy
        ((baseChange (q ≫ p)).map i) := by
  let eG := Descent.pullbackComparison p q (q ≫ p) rfl G
  let eP := Descent.pullbackComparison p q (q ≫ p) rfl P
  have hsquare := Descent.pullbackComparison_naturality p q (q ≫ p) rfl i
  have ht := hχ.comp_iso eG
  have hdyn : (Dynamic.parabolic χ).comap eG.inv =
      Dynamic.parabolic (χ ≫ eG.hom) := by
    rw [Dynamic.parabolic_eq_comap_of_iso χ eG,
      ← SubgroupFunctor.comap_comp, Iso.inv_hom_id, SubgroupFunctor.comap_id]
  rw [hdyn] at ht
  change (Dynamic.parabolic (χ ≫ eG.hom)).IsRepresentedBy
    ((baseChange q).map ((baseChange p).map i) ≫ eG.hom) at ht
  change (baseChange q).map ((baseChange p).map i) ≫ eG.hom =
    eP.hom ≫ (baseChange (q ≫ p)).map i at hsquare
  rw [hsquare] at ht
  refine ⟨?_, ?_⟩
  · have : IsIso eP.hom.hom.hom := inferInstanceAs
      (IsIso ((Grp.forget _).mapIso eP).hom)
    change Mono ((baseChange (q ≫ p)).map i).hom.hom
    apply (mono_comp_iff_of_isIso eP.hom.hom.hom _).mp
    exact ht.1
  · simpa only [SubgroupFunctor.range_iso_comp] using ht.2

/-- A pointed dynamic neighbourhood at every base point forms an etale cover. -/
theorem exists_etaleCover_of_pointedDynamic
    {S : Scheme.{u}} {G P : GroupScheme S} (i : P ⟶ G)
    (h : ∀ s : S, ∃ (U : Scheme.{u}) (p : U ⟶ S)
      (b : Spec (S.residueField s) ⟶ U)
      (_hb : b ≫ p = S.fromSpecResidueField s)
      (χ : (Gm U).toGrp ⟶ (baseChange p).obj G),
      Etale p ∧ (Dynamic.parabolic χ).IsRepresentedBy ((baseChange p).map i)) :
    ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ a : 𝒰.I₀, ∃ χ : (Gm (𝒰.X a)).toGrp ⟶ (baseChange (𝒰.f a)).obj G,
        (Dynamic.parabolic χ).IsRepresentedBy ((baseChange (𝒰.f a)).map i) := by
  choose U p b hb χ hp hχ using h
  refine ⟨Scheme.Cover.mkOfCovers S U p ?_ hp, ?_⟩
  · intro s
    refine ⟨s, b s (IsLocalRing.closedPoint (S.residueField s)), ?_⟩
    rw [← Scheme.Hom.comp_apply, hb]
    exact S.fromSpecResidueField_apply s _
  · intro s
    exact ⟨χ s, hχ s⟩

/-- Pointed cocharacter lifting and the open dynamic comparison give the
etale-local dynamic description for an arbitrary relative parabolic. -/
theorem relativeParabolicEtaleLocalDynamic :
    RelativeParabolicEtaleLocalDynamicStatement.{u} := by
  intro S G P i hG hi
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : GeometricallyConnected G.X.hom := hG.geometricallyConnected
  let : Smooth P.X.hom := hi.smooth
  let : IsAffineHom P.X.hom := hi.isAffineHom
  let : GeometricallyConnected P.X.hom := hi.geometricallyConnected hG
  let : Mono i.hom.hom := hi.mono
  apply exists_etaleCover_of_pointedDynamic i
  intro s
  obtain ⟨U, p, b, hb, χ, hp, hc, hχ⟩ :=
    relativeParabolicPointedDynamicLifting S G P i hG hi s
  let : Etale p := hp
  let : Smooth ((baseChange p).obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom p))
  let : IsAffineHom ((baseChange p).obj G).X.hom :=
    MorphismProperty.pullback_snd _ _ hG.isAffineHom
  let : GeometricallyConnected ((baseChange p).obj G).X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.X.hom p))
  let : Smooth ((baseChange p).obj P).X.hom :=
    inferInstanceAs (Smooth (pullback.snd P.X.hom p))
  let : IsAffineHom ((baseChange p).obj P).X.hom :=
    MorphismProperty.pullback_snd _ _ hi.isAffineHom
  let : GeometricallyConnected ((baseChange p).obj P).X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd P.X.hom p))
  let : Mono ((baseChange p).map i).hom.hom :=
    inferInstanceAs (Mono ((Over.pullback p).map i.hom.hom))
  obtain ⟨V, q, hq, a, ha, hv⟩ :=
    LocalDynamicComparison.exists_open ((baseChange p).map i) χ
      (S.residueField s) b hc hχ
  let : IsOpenImmersion q := hq
  refine ⟨V, q ≫ p, a, ?_,
    Dynamic.baseChangeCocharacter q (χ ≫ (baseChange p).map i) ≫
      (Descent.pullbackComparison p q (q ≫ p) rfl G).hom,
    inferInstance, ?_⟩
  · rw [← Category.assoc, ha, hb]
  · exact isRepresentedBy_dynamicParabolic_direct i p q _ hv

/-- Relative parabolic subgroup inclusions are closed over every base scheme. -/
theorem relativeParabolicClosed : RelativeParabolicClosedStatement.{u} :=
  relativeParabolicClosed_of_etaleLocalDynamic relativeParabolicEtaleLocalDynamic

end Langlands.GroupScheme
