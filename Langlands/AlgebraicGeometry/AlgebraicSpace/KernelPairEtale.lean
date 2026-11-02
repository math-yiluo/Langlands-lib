import Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPairDiagonal
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Étaleness of a quotient map from its kernel pair

Let `Q` be a presheaf over `S` with representable diagonal and a locally surjective map `a` from
a scheme `U` whose kernel pair is represented by `t s : R ⟶ U`, with `s` étale. Then `a` is
étale: a base change of `a` to a scheme `T` becomes, after further base change to a member of
the fppf covering sieve of `T` on which the section lifts to `U`, a base change of `s`, and
étaleness is fppf local on the target.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPair

variable {S : Scheme.{u}} {Q : Presheaf S} {U R : Over S} (a : (schemeYoneda S).obj U ⟶ Q)
  [Presheaf.IsLocallySurjective (fppfTopology S) a] {t s : R ⟶ U}

set_option backward.isDefEq.respectTransparency.types false in
/-- A locally surjective map from a scheme to a presheaf with representable diagonal is étale
when one projection of its represented kernel pair is étale. -/
theorem isEtale_of_isPullback (hdiag : HasRepresentableDiagonal Q)
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (hs : Etale s.left) : IsEtale a := by
  have hr : IsRepresentableMorphism a := Functor.relativelyRepresentable.of_diag hdiag a
  let : MorphismProperty.RespectsIso (@Etale.{u}) :=
    Etale.etale_isStableUnderBaseChange.respectsIso
  let := MorphismProperty.RespectsIso.inverseImage (@Etale.{u}) (Over.forget S)
  refine MorphismProperty.relative_of_snd hr fun T g ↦ ?_
  change Etale (hr.snd g).left
  have hsq := hr.isPullback g
  have hJ : Presheaf.imageSieve a (uliftYonedaEquiv g) ∈ fppfTopology S T :=
    Presheaf.imageSieve_mem (fppfTopology S) a _
  rw [GrothendieckTopology.mem_over_iff] at hJ
  have : IsZariskiLocalAtTarget @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  refine FppfLocal.of_fppfTopology_sieve @Etale (hr.snd g).left _ hJ fun Y f hf ↦ ?_
  rw [Sieve.overEquiv_iff] at hf
  obtain ⟨⟨τ⟩, hτ⟩ := hf
  let T' : Over S := Over.mk (f ≫ T.hom)
  let f' : T' ⟶ T := Over.homMk f
  have hτg : (schemeYoneda S).map τ ≫ a = (schemeYoneda S).map f' ≫ g :=
    map_comp_eq_map_comp_of_app_eq a g (hτ.trans (schemeYoneda_app_up g f').symm)
  have hW := IsPullback.of_hasPullback s τ
  have big := (hW.map (schemeYoneda S)).paste_horiz h
  rw [hτg] at big
  let k := hsq.lift ((schemeYoneda S).map (pullback.fst s τ) ≫ (schemeYoneda S).map t)
    ((schemeYoneda S).map (pullback.snd s τ) ≫ (schemeYoneda S).map f')
    (by simpa only [Category.assoc] using big.w)
  have hk : IsPullback k ((schemeYoneda S).map (pullback.snd s τ))
      ((schemeYoneda S).map (hr.snd g)) ((schemeYoneda S).map f') :=
    IsPullback.of_right (by rw [hsq.lift_fst]; exact big) (hsq.lift_snd _ _ _) hsq
  obtain ⟨κ, hκ⟩ := (schemeYoneda S).map_surjective k
  rw [← hκ] at hk
  have hk' := isPullback_of_map hk
  exact ⟨_, κ.left, (pullback.snd s τ).left, hk'.map (Over.forget S),
    MorphismProperty.of_isPullback (hW.map (Over.forget S)) hs⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPair
