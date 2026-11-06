import Langlands.GroupScheme.Rational.TorusQuotientKernelSplitDomination
import Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat
import Langlands.GroupScheme.Rational.SplitTorusFppfImage

/-! # Faithful flatness from injective pullback of actual torus characters -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Diagonalizable

variable {k : Type u} [Field k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)

/-- The canonical diagonalizable model is evaluation on actual characters. -/
theorem splitTorusDiagonalizableIso_points (U : Over (Spec (CommRingCat.of k)))
    (x : U ⟶ T.X) :
    characterPointsEquiv (CommRingCat.of k) (characterLattice T) U
      (x ≫ (splitTorusDiagonalizableIso T hT).hom.hom.hom) =
      characterLattice.pointCharacters T U x := by
  exact isoOfPointModels_hom
    (fun U : Over (Spec (CommRingCat.of k)) =>
      Multiplicative (characterLattice T) →* (Γ(U.left, ⊤))ˣ)
    (fun a => MonoidHom.compHom (Units.map a.left.appTop.hom.toMonoidHom))
    (characterLattice.pointCharactersEquiv T hT)
    (characterPointsEquiv (CommRingCat.of k) (characterLattice T))
    (by
      intro U U' a x
      apply MonoidHom.ext
      intro b
      exact characterLattice.pointCharacters_naturality T a x b.toAdd)
    (characterPointsEquiv_natural (CommRingCat.of k) (characterLattice T)) U x

variable {T} {Q : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Every map of actual split tori is restriction along its full character pullback
in the canonical diagonalizable models. -/
theorem splitTorusDiagonalizableIso_naturality
    (hQ : IsSplitTorus Q.toGrp) (f : T.toGrp ⟶ Q.toGrp) :
    f ≫ (splitTorusDiagonalizableIso Q hQ).hom =
      (splitTorusDiagonalizableIso T hT).hom ≫
        restrictMap (CommRingCat.of k) (characterLattice.comapHom f) := by
  apply hom_ext_points
  intro U x
  apply (characterPointsEquiv (CommRingCat.of k) (characterLattice Q) U).injective
  apply MonoidHom.ext
  intro b
  change characterPointsEquiv _ _ U
      ((x ≫ f.hom.hom) ≫ (splitTorusDiagonalizableIso Q hQ).hom.hom.hom) b = _
  rw [splitTorusDiagonalizableIso_points]
  change characterLattice.pointCharacters Q U (x ≫ f.hom.hom) (.ofAdd b.toAdd) =
    characterPointsEquiv _ _ U
      ((x ≫ (splitTorusDiagonalizableIso T hT).hom.hom.hom) ≫
        (restrictMap (CommRingCat.of k) (characterLattice.comapHom f)).hom.hom) (.ofAdd b.toAdd)
  have hr := pointsEquiv_restrictMap (CommRingCat.of k) (characterLattice.comapHom f)
    (x ≫ (splitTorusDiagonalizableIso T hT).hom.hom.hom) b.toAdd
  change characterPointsEquiv _ _ U
      ((x ≫ (splitTorusDiagonalizableIso T hT).hom.hom.hom) ≫
        (restrictMap (CommRingCat.of k) (characterLattice.comapHom f)).hom.hom)
      (.ofAdd b.toAdd) =
    characterPointsEquiv _ _ U
      (x ≫ (splitTorusDiagonalizableIso T hT).hom.hom.hom)
      (.ofAdd (characterLattice.comapHom f b.toAdd)) at hr
  rw [hr]
  rw [splitTorusDiagonalizableIso_points]
  exact characterLattice.pointCharacters_comp_hom f U x b.toAdd

end Diagonalizable

variable {k : Type u} [Field k]
    {T Q : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Injective pullback of full actual characters makes a homomorphism of split tori
faithfully flat over any field. -/
theorem IsSplitTorus.flat_and_surjective_of_injective_characterPullback
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp)
    (f : T.toGrp ⟶ Q.toGrp)
    (hf : Function.Injective (characterLattice.comapHom f)) :
    Flat f.hom.hom.left ∧ Surjective f.hom.hom.left := by
  let eT := Diagonalizable.splitTorusDiagonalizableIso T hT
  let eQ := Diagonalizable.splitTorusDiagonalizableIso Q hQ
  let r := Diagonalizable.restrictMap (CommRingCat.of k) (characterLattice.comapHom f)
  have hflat := Diagonalizable.flat_and_surjective_restrictMap
    (CommRingCat.of k) (characterLattice.comapHom f) hf
  have : Flat r.hom.hom.left := hflat.1
  have : Surjective r.hom.hom.left := hflat.2
  have : IsIso eT.hom.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso eT.hom
  have : IsIso eQ.inv.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso eQ.inv
  have hfac : f = eT.hom ≫ r ≫ eQ.inv := by
    apply (cancel_mono eQ.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      Diagonalizable.splitTorusDiagonalizableIso_naturality hT hQ f
  rw [hfac]
  change Flat (eT.hom.hom.hom.left ≫ r.hom.hom.left ≫ eQ.inv.hom.hom.left) ∧
    Surjective (eT.hom.hom.hom.left ≫ r.hom.hom.left ≫ eQ.inv.hom.hom.left)
  exact ⟨inferInstance, inferInstance⟩

end Langlands.GroupScheme
