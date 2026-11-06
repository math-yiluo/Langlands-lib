import Langlands.AlgebraicGeometry.AffineSchemePushoutAlgebra

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace Langlands.AlgebraicGeometry.AffineSchemePushout

variable {B C D B' C' D' : Type u}
  [CommRing B] [CommRing C] [CommRing D]
  [CommRing B'] [CommRing C'] [CommRing D']
  [Algebra B B'] [Algebra C C'] [Algebra D D']
  (f : B →+* D) (g : C →+* D) (f' : B' →+* D') (g' : C' →+* D')
  (hf : f'.comp (algebraMap B B') = (algebraMap D D').comp f)
  (hg : g'.comp (algebraMap C C') = (algebraMap D D').comp g)

include hf hg in
/-- A compatible square of localizations of a canonical ring pullback is a pullback. -/
theorem isPullback_localization (a : f.pullback g)
    [IsLocalization.Away a.1.1 B'] [IsLocalization.Away a.1.2 C']
    [IsLocalization.Away (f a.1.1) D']
    (A' : Type u) [CommRing A'] [Algebra (f.pullback g) A']
    [IsLocalization.Away a A'] (i : A' →+* B') (j : A' →+* C')
    (hi : i.comp (algebraMap (f.pullback g) A') =
      (algebraMap B B').comp (f.pullbackFst g))
    (hj : j.comp (algebraMap (f.pullback g) A') =
      (algebraMap C C').comp (f.pullbackSnd g))
    (hij : f'.comp i = g'.comp j) :
    IsPullback (CommRingCat.ofHom i) (CommRingCat.ofHom j)
      (CommRingCat.ofHom f') (CommRingCat.ofHom g') := by
  let h : A' →+* f'.pullback g' := (i.prod j).codRestrict _
    (fun x => DFunLike.congr_fun hij x)
  let := (pullbackMap f g f' g' hf hg).toAlgebra
  let := isLocalization_pullback f g f' g' hf hg a
  have hh : h.comp (algebraMap (f.pullback g) A') =
      algebraMap (f.pullback g) (f'.pullback g') := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    exact Prod.ext (DFunLike.congr_fun hi x) (DFunLike.congr_fun hj x)
  let e : CommRingCat.of A' ≅ CommRingCat.of (f'.pullback g') :=
    (RingEquiv.ofBijective h (IsLocalization.bijective (Submonoid.powers a) h hh)).toCommRingCatIso
  have H := IsPullback.of_isLimit
    (CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom f') (CommRingCat.ofHom g'))
  exact H.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by rfl) (by rfl) (by simp) (by simp)

include hf hg in
/-- The limit structure on a compatible localized pullback cone. -/
def localizationPullbackConeIsLimit (a : f.pullback g)
    [IsLocalization.Away a.1.1 B'] [IsLocalization.Away a.1.2 C']
    [IsLocalization.Away (f a.1.1) D']
    (A' : Type u) [CommRing A'] [Algebra (f.pullback g) A']
    [IsLocalization.Away a A'] (i : A' →+* B') (j : A' →+* C')
    (hi : i.comp (algebraMap (f.pullback g) A') =
      (algebraMap B B').comp (f.pullbackFst g))
    (hj : j.comp (algebraMap (f.pullback g) A') =
      (algebraMap C C').comp (f.pullbackSnd g))
    (hij : f'.comp i = g'.comp j) :
    IsLimit (PullbackCone.mk (CommRingCat.ofHom i) (CommRingCat.ofHom j)
      (show CommRingCat.ofHom i ≫ CommRingCat.ofHom f' =
        CommRingCat.ofHom j ≫ CommRingCat.ofHom g' from
        CommRingCat.hom_ext hij)) :=
  (isPullback_localization f g f' g' hf hg a A' i j hi hj hij).isLimit

end Langlands.AlgebraicGeometry.AffineSchemePushout
