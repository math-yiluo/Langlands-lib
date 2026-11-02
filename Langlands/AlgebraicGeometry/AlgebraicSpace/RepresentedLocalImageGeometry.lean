import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorImages
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeSourceDescentProof
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Scheme geometry of a represented local image -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {G : Presheaf S} {D B W : Over S}

/-- The local image representation has its induced map to the base and its
canonical surjective etale chart, with all projection compatibilities. -/
def RepresentedLocalImageGeometry
    (c : (schemeYoneda S).obj D ⟶ G)
    (p : G ⟶ (schemeYoneda S).obj B) (w : D ⟶ B)
    (e : (schemeYoneda S).obj W ≅
      ((Subfunctor.range c).sheafify (fppfTopology S)).toFunctor) : Prop :=
  ∃ (q : W ⟶ B) (d : D ⟶ W),
    (schemeYoneda S).map q =
      e.hom ≫ ((Subfunctor.range c).sheafify (fppfTopology S)).ι ≫ p ∧
    (schemeYoneda S).map d ≫ e.hom =
      Subfunctor.toRangeSheafify (fppfTopology S) c ∧
    d ≫ q = w ∧ Mono q.left ∧ Etale d.left ∧ Surjective d.left ∧
      LocallyOfFiniteType q.left ∧ LocallyQuasiFinite q.left

/-- A represented local image of an etale chart over a monomorphism
inherits local finite type from the original chart composite. -/
theorem representedLocalImageGeometry
    (c : (schemeYoneda S).obj D ⟶ G) (hc : IsEtale c)
    (p : G ⟶ (schemeYoneda S).obj B) [Mono p]
    (w : D ⟶ B) (hw : c ≫ p = (schemeYoneda S).map w)
    [LocallyOfFiniteType w.left]
    (e : (schemeYoneda S).obj W ≅
      ((Subfunctor.range c).sheafify (fppfTopology S)).toFunctor) :
    RepresentedLocalImageGeometry c p w e := by
  let A := (Subfunctor.range c).sheafify (fppfTopology S)
  let a := Subfunctor.toRangeSheafify (fppfTopology S) c
  let q : W ⟶ B := (schemeYoneda S).preimage (e.hom ≫ A.ι ≫ p)
  let d : D ⟶ W := (schemeYoneda S).preimage (a ≫ e.inv)
  have hq : (schemeYoneda S).map q = e.hom ≫ A.ι ≫ p :=
    (schemeYoneda S).map_preimage _
  have hd : (schemeYoneda S).map d ≫ e.hom = a := by
    dsimp [d]
    rw [Functor.map_preimage]
    simp
  have hsq : IsPullback (𝟙 ((schemeYoneda S).obj D))
      ((schemeYoneda S).map d) a e.hom :=
    IsPullback.of_horiz_isIso ⟨by simpa using hd.symm⟩
  have hde : Etale d.left :=
    (OpenSubfunctorImages.toRangeSheafify_isEtale c hc).projection
      e.hom (𝟙 _) d hsq
  have hds : Surjective d.left :=
    (OpenSubfunctorImages.toRangeSheafify_isSurjective c hc).projection
      e.hom (𝟙 _) d hsq
  have hdq : d ≫ q = w := by
    apply (schemeYoneda S).map_injective
    rw [Functor.map_comp, hq, ← Category.assoc, hd, ← Category.assoc]
    have ha : a ≫ A.ι = c := by
      ext T x
      rfl
    rw [ha, hw]
  have hqm : Mono q := (schemeYoneda S).mono_of_mono_map (by
    rw [hq]
    infer_instance)
  have hqft : LocallyOfFiniteType q.left := by
    have : Etale d.left := hde
    have : LocallyOfFiniteType (d.left ≫ q.left) := by
      change LocallyOfFiniteType (d ≫ q).left
      rw [hdq]
      infer_instance
    exact locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp
      D.left W.left B.left d.left q.left hds inferInstance inferInstance inferInstance
  have : Mono q.left := inferInstance
  have : LocallyQuasiFinite q.left := inferInstance
  exact ⟨q, d, hq, hd, hdq, inferInstance, hde, hds, hqft, inferInstance⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
