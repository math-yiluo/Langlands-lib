import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocus.BundleNormalization
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso

/-! # The closed agreement locus of line bundles modulo base twists -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open LineBundle (IsoClasses isoClass pullbackHom pullbackHom_comp_eq pullbackHom_id)

variable (P : Prerequisites.{u}) {S : Scheme.{u}} (A : AbelianScheme S)

private def normalizedIdentityFamily (L : LineBundle A.X.left) :
    RigidifiedFamily A (Over.mk (𝟙 S)) :=
  (RigidifiedLineBundle.pullback (pullback.snd (𝟙 S) A.X.hom) (𝟙 S)
    ((relativeSection_snd A.X.hom (unitSection A) (unitSection_comp A)
      (Over.mk (𝟙 S))).trans (Category.id_comp _))).obj (normalizedBundle P A L)

private def normalizedClassAt (L : LineBundle A.X.left) (T : Over S) : RigidifiedClasses A T :=
  RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
    (Over.mkIdTerminal.from T)
    (RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
      (normalizedIdentityFamily P A L))

private lemma normalizedClassAt_agree (L M : LineBundle A.X.left) (T : Over S) :
    normalizedClassAt P A L T = normalizedClassAt P A M T ↔
      normalizedBundleClass P ((baseChange T.hom).obj A) (isoClass P.preservation
        ((LineBundle.pullback (pullback.fst A.X.hom T.hom)).obj L)) =
      normalizedBundleClass P ((baseChange T.hom).obj A) (isoClass P.preservation
        ((LineBundle.pullback (pullback.fst A.X.hom T.hom)).obj M)) := by
  let h : T ⟶ Over.mk (𝟙 S) := Over.mkIdTerminal.from T
  let F (N : LineBundle A.X.left) := (RigidifiedLineBundle.relativePullback A.X.hom
    (unitSection A) (unitSection_comp A) h).obj (normalizedIdentityFamily P A N)
  let e := pullbackSymmetry T.hom A.X.hom
  have hn (N : LineBundle A.X.left) :
      isoClass P.preservation ((RigidifiedLineBundle.forget _).obj (F N)) =
        pullbackHom P.preservation e.hom (normalizedBundleClass P ((baseChange T.hom).obj A)
          (isoClass P.preservation ((LineBundle.pullback (pullback.fst A.X.hom T.hom)).obj N))) := by
    change isoClass P.preservation ((LineBundle.pullback ((relativeSpace A.X.hom).map h)).obj
      ((LineBundle.pullback (pullback.snd (𝟙 S) A.X.hom)).obj
        ((RigidifiedLineBundle.forget _).obj (normalizedBundle P A N)))) = _
    have hp : (relativeSpace A.X.hom).map h ≫ pullback.snd (𝟙 S) A.X.hom =
        pullback.snd T.hom A.X.hom := relativeSpace_map_snd A.X.hom h
    rw [← LineBundle.pullbackHom_isoClass, ← LineBundle.pullbackHom_isoClass,
      pullbackHom_comp_eq P.preservation _ _ hp,
      isoClass_of_normalizedBundle]
    let q := isoClass P.preservation N
    let π := pullback.fst A.X.hom T.hom
    have he : e.hom ≫ π = pullback.snd T.hom A.X.hom :=
      pullbackSymmetry_hom_comp_fst T.hom A.X.hom
    exact (pullbackHom_comp_eq P.preservation e.hom π he
      (normalizedBundleClass P A q)).symm.trans
      (congrArg (pullbackHom P.preservation e.hom) (pullback_normalizedBundleClass P A T.hom q))
  have hinj : Function.Injective (pullbackHom P.preservation e.hom) := by
    intro a b hab
    have hp (q : IsoClasses P.preservation ((baseChange T.hom).obj A).X.left) :
        pullbackHom P.preservation e.inv (pullbackHom P.preservation e.hom q) = q :=
      (pullbackHom_comp_eq P.preservation e.inv e.hom e.inv_hom_id q).trans
        (pullbackHom_id P.preservation q)
    exact (hp a).symm.trans ((congrArg (pullbackHom P.preservation e.inv) hab).trans (hp b))
  change (Quotient.mk _ (F L) : RigidifiedClasses A T) = Quotient.mk _ (F M) ↔ _
  rw [← hinj.eq_iff, ← hn, ← hn]
  constructor
  · intro he
    obtain ⟨i⟩ : Nonempty (F L ≅ F M) := Quotient.exact he
    exact LineBundle.isoClass_eq_of_iso ((RigidifiedLineBundle.forget _).mapIso i)
  · intro he
    obtain ⟨i⟩ := (LineBundle.isoClass_eq_iff (preservation := P.preservation)).mp he
    exact Quotient.sound (RigidifiedLineBundle.nonempty_iso_of_forget_iso P.preservation
      ((relativeProjection A.X.hom).app T)
      (relativeSection_projection A.X.hom (unitSection A) (unitSection_comp A) T) i)

/-- Agreement modulo an actual line bundle from the test base is represented by a closed subscheme on every test. -/
theorem exists_normalizedBundle_agreementLocus (L M : LineBundle A.X.left) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ S), IsClosedImmersion j ∧
      ∀ (T : Scheme.{u}) (t : T ⟶ S), (∃ t' : T ⟶ Z, t' ≫ j = t) ↔
        ∃ N : LineBundle T, Nonempty (
          (LineBundle.pullback (pullback.fst A.X.hom t)).obj L ≅
            LineBundle.tensor P.preservation ((LineBundle.pullback (pullback.fst A.X.hom t)).obj M)
              ((LineBundle.pullback ((baseChange t).obj A).X.hom).obj N)) := by
  obtain ⟨Z, j, hj, hZ⟩ := rigidifiedClassesEqualizerClosed S A (Over.mk (𝟙 S))
    (RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
      (normalizedIdentityFamily P A L))
    (RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A)
      (normalizedIdentityFamily P A M))
  refine ⟨Z, j, hj, fun T t ↦ ?_⟩
  have h : (∃ t' : T ⟶ Z, t' ≫ j = t) ↔
      normalizedClassAt P A L (Over.mk t) = normalizedClassAt P A M (Over.mk t) := by
    let T' : Over S := Over.mk t
    have hmap : (Over.mkIdTerminal.from T').left = t := Over.mkIdTerminal_from_left T'
    have ht := hZ T' (Over.mkIdTerminal.from T')
    rw [hmap] at ht
    exact ht
  refine h.trans ((normalizedClassAt_agree P A L M (Over.mk t)).trans ?_)
  exact normalizedBundleClass_eq_iff P ((baseChange t).obj A)
    ((LineBundle.pullback (pullback.fst A.X.hom t)).obj L)
    ((LineBundle.pullback (pullback.fst A.X.hom t)).obj M)

end Langlands.AbelianScheme.PolarizedFiniteLevel
