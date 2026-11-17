import Langlands.GroupScheme.IsomorphismSheafQuotientLocalModel
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationEtale
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedAtlasEffectivityDescent

/-! # A full Isom scheme from one local affine outer quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace LocalGroupIso.ActionQuotient

variable {S : Scheme.{u}}

/-- One represented separated locally quasi-finite pullback along an fppf cover suffices. -/
theorem exists_representation_of_single_pullback {F : FppfSheaf S} {Z W T : Over S}
    {c : (schemeYoneda S).obj Z ⟶ F.obj} {j : Z ⟶ W}
    {φ : F.obj ⟶ (schemeYoneda S).obj T} {p : W ⟶ T}
    (hpb : IsPullback c ((schemeYoneda S).map j) φ ((schemeYoneda S).map p))
    [Flat p.left] [LocallyOfFinitePresentation p.left] [Surjective p.left]
    [IsSeparated j.left] [LocallyQuasiFinite j.left] [LocallyOfFiniteType j.left] :
    ∃ M : Over S, Nonempty ((schemeYoneda S).obj M ≅ F.obj) := by
  obtain ⟨M, _, e, _⟩ :=
    Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent.fppfSeparatedLocallyQuasiFiniteDescent
      S F T φ (Sieve.generate (Presieve.singleton p))
        (generate_singleton_mem_fppfTopology p) (by
          intro V g hg
          obtain ⟨V', r, p', hp', hcomp⟩ := hg
          cases hp'
          subst g
          let P := Limits.pullback j r
          let h := IsPullback.of_hasPullback j r
          have hs : IsSeparated (pullback.snd j r).left :=
            MorphismProperty.of_isPullback (P := @IsSeparated) (h.map (Over.forget S))
              (inferInstanceAs (IsSeparated j.left))
          have hq : LocallyQuasiFinite (pullback.snd j r).left :=
            MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (h.map (Over.forget S))
              (inferInstanceAs (LocallyQuasiFinite j.left))
          have hf : LocallyOfFiniteType (pullback.snd j r).left :=
            MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (h.map (Over.forget S))
              (inferInstanceAs (LocallyOfFiniteType j.left))
          have hlocal := (h.map (schemeYoneda S)).paste_horiz hpb
          rw [← Functor.map_comp] at hlocal
          exact ⟨P, pullback.snd j r, (schemeYoneda S).map (pullback.fst j r) ≫ c,
            hlocal, hs, hq, hf⟩)
  exact ⟨M, ⟨e⟩⟩

/-- One local quotient model over an fppf surjective base gives the global quotient scheme. -/
def representationOfSingleLocalPresentation
    {G H A : GroupScheme S} (a : AutomorphicAction A G) (ha : a.IsFaithful)
    {U : Scheme.{u}} (b : U ⟶ S) [Flat b] [LocallyOfFinitePresentation b] [Surjective b]
    (P : LocalPresentation (H := H) a (Over.mk b)) : Representation (H := H) a := by
  apply Classical.choice
  obtain ⟨e, he⟩ := P.exists_iso ha
  let p : Over.mk b ⟶ Over.mk (𝟙 S) := Over.homMk b (by simp)
  let : Flat p.left := inferInstanceAs (Flat b)
  let : LocallyOfFinitePresentation p.left := inferInstanceAs (LocallyOfFinitePresentation b)
  let : Surjective p.left := inferInstanceAs (Surjective b)
  let := P.separated
  let := P.locallyQuasiFinite
  let := P.locallyOfFiniteType
  obtain ⟨Q, ⟨eQ⟩⟩ := exists_representation_of_single_pullback (P.isPullback e he p)
  exact ⟨⟨Q, eQ⟩⟩

end LocalGroupIso.ActionQuotient

namespace GroupIsomorphismScheme

variable {S U : Scheme.{u}} {G H A : GroupScheme S}
    (b : U ⟶ S) [Etale b] [Surjective b]
    (a : AutomorphicAction A G) (ha : a.IsFaithful)
    (I : GroupIsomorphismScheme
      ((GroupScheme.baseChange b).obj G) ((GroupScheme.baseChange b).obj H))
    [Smooth I.parameter.hom]
    (O : OuterIsomorphismScheme I (a.baseChange b))
    [Etale O.parameter.hom] [IsSeparated O.parameter.hom] [IsAffineHom O.classMap.left]

open LocalGroupIso.ActionQuotient

/-- A local full Isom scheme with an affine separated étale outer quotient descends to a scheme. -/
def ofSingleLocalOuterQuotient : GroupIsomorphismScheme G H := by
  apply Classical.choice
  let P := I.localQuotientPresentationOfSmooth b a O
  let R := representationOfSingleLocalPresentation a ha b P
  obtain ⟨e, he⟩ := P.exists_iso ha
  let m : P.parameter ⟶ R.parameter :=
    (schemeYoneda S).preimage (e.hom ≫ extProd.fst ≫ R.iso.inv)
  have hm : (schemeYoneda S).map m = e.hom ≫ extProd.fst ≫ R.iso.inv :=
    (schemeYoneda S).map_preimage _
  let φ := R.mapToParameter a
  have hsq :
      IsPullback (P.isomIso.hom ≫ extProd.fst) ((schemeYoneda S).map P.classMap)
        φ ((schemeYoneda S).map m) := by
    apply (extProd.isPullback_mapLeft (classMap (H := H) a).hom).flip.of_iso'
      P.isomIso (Iso.refl _) e R.iso
    · simp
    · exact he.symm
    · simpa only [Iso.refl_hom, Category.id_comp] using
        (R.mapToParameter_iso_hom a).symm
    · rw [hm]
      simp
  have hme : IsEtale ((schemeYoneda S).map m) := by
    rw [hm]
    exact (IsEtale.iso_comp e
      (extProd.relative_fst (@Etale.{u}) (F := (sheaf (H := H) a).obj)
        (Λ := Over.mk b) (inferInstanceAs (Etale b)))).comp_iso R.iso.symm
  have hms : IsSurjective ((schemeYoneda S).map m) := by
    rw [hm]
    exact (MorphismProperty.cancel_left_of_respectsIso
      ((MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
        (schemeYoneda S)) _ _).mpr
          (IsSurjective.comp_iso
            (extProd.relative_fst (@Surjective.{u}) (F := (sheaf (H := H) a).obj)
              (Λ := Over.mk b) (inferInstanceAs (Surjective b))) R.iso.symm)
  let X : Langlands.AlgebraicGeometry.AlgebraicSpace S :=
    ⟨LocalGroupIso.sheaf G H (fppfTopology S),
      LocalRepresentation.isAlgebraicSpace_of_single_representation b I.parameter
        (I.localRepresentationIso b) inferInstance inferInstance⟩
  let Y := (schemeToSpace S).obj R.parameter
  let f : X ⟶ Y := homMk φ
  let : IsAffineHom P.classMap.left := inferInstanceAs (IsAffineHom O.classMap.left)
  obtain ⟨M, ⟨eM⟩⟩ := AtlasEffectivity.exists_iso_of_isAffineHom
    (f := f) hsq hme hms
      (F := LocalGroupIso.sheaf G H (fppfTopology S))
      (IsPullback.of_id_fst (f := φ))
  exact ⟨GroupIsomorphismScheme.ofRepresentableBy
    ((Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _).symm eM)⟩

end GroupIsomorphismScheme

end Langlands.GroupScheme
