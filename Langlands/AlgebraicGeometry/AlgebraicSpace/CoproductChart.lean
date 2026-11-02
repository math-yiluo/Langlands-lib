import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Scheme coproduct charts over a fixed base -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart

variable {S : Scheme.{u}} {ι : Type u} (V : ι → Over S)

/-- The scheme coproduct, with the structure map induced by its components. -/
def sigmaOver : Over S :=
  Over.mk (Sigma.desc (fun i => (V i).hom))

/-- A component inclusion into the coproduct over the fixed base. -/
def sigmaOverι (i : ι) : V i ⟶ sigmaOver V :=
  Over.homMk (Sigma.ι (fun i => (V i).left) i) (Sigma.ι_comp_desc _ i)

/-- Descent from a family of morphisms over the fixed base. -/
def sigmaOverDesc {T : Over S} (f : ∀ i, V i ⟶ T) : sigmaOver V ⟶ T :=
  Over.homMk (Sigma.desc (fun i => (f i).left)) (by
    change Sigma.desc (fun i => (f i).left) ≫ T.hom =
      Sigma.desc (fun i => (V i).hom)
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Over.w])

@[reassoc (attr := simp)]
theorem ι_desc {T : Over S} (f : ∀ i, V i ⟶ T) (i : ι) :
    sigmaOverι V i ≫ sigmaOverDesc V f = f i :=
  Over.OverMorphism.ext (Sigma.ι_comp_desc _ i)

instance isOpenImmersion_ι (i : ι) :
    _root_.AlgebraicGeometry.IsOpenImmersion (sigmaOverι V i).left := by
  change _root_.AlgebraicGeometry.IsOpenImmersion (Sigma.ι (fun i => (V i).left) i)
  infer_instance

instance isAffine [Finite ι] [∀ i, IsAffine (V i).left] :
    IsAffine (sigmaOver V).left := by
  change IsAffine (∐ fun i => (V i).left)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance locallyOfFiniteType [∀ i, LocallyOfFiniteType (V i).hom] :
    LocallyOfFiniteType (sigmaOver V).hom :=
  IsZariskiLocalAtSource.sigmaDesc (P := @_root_.AlgebraicGeometry.LocallyOfFiniteType.{u})
    (fun _ => inferInstance)

set_option backward.isDefEq.respectTransparency false in
/-- The pullbacks of the coproduct components form an open cover, with
the fiber products taken in the category over the fixed base. -/
def pullbackOpenCover {W : Over S} (r : W ⟶ sigmaOver V) : W.left.OpenCover := by
  let R i := Limits.pullback r (sigmaOverι V i)
  let p i : R i ⟶ W := pullback.fst r (sigmaOverι V i)
  let : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (p i).left := fun i =>
    MorphismProperty.of_isPullback
      (((IsPullback.of_hasPullback r (sigmaOverι V i)).map (Over.forget S)).flip)
      (show _root_.AlgebraicGeometry.IsOpenImmersion (sigmaOverι V i).left from
        inferInstance)
  apply Scheme.Cover.mkOfCovers
    (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u}) ι
    (fun i => (R i).left) (fun i => (p i).left)
  intro x
  let 𝒰 := (_root_.AlgebraicGeometry.sigmaOpenCover (fun i => (V i).left)).pullback₁ r.left
  obtain ⟨i, y, hy⟩ := Scheme.Cover.exists_eq 𝒰 x
  let e := PreservesPullback.iso (Over.forget S) r (sigmaOverι V i)
  refine ⟨i, e.inv y, ?_⟩
  exact (congrArg (fun f : Limits.pullback r.left (sigmaOverι V i).left ⟶ W.left => f y)
    (PreservesPullback.iso_inv_fst (Over.forget S) r (sigmaOverι V i))).trans hy

set_option backward.isDefEq.respectTransparency false in
/-- Etaleness of a scheme chart can be checked on the components of its
scheme coproduct source, when the target has representable diagonal. -/
theorem isEtale_of_forall_ι {F : Presheaf S}
    (hF : HasRepresentableDiagonal F)
    (b : (schemeYoneda S).obj (sigmaOver V) ⟶ F)
    (hb : ∀ i, IsEtale ((schemeYoneda S).map (sigmaOverι V i) ≫ b)) :
    IsEtale b := by
  refine ⟨Functor.relativelyRepresentable.of_diag hF b, ?_⟩
  intro T W g a q h
  obtain ⟨r, rfl⟩ := (schemeYoneda S).map_surjective a
  apply IsZariskiLocalAtSource.of_openCover (P := @_root_.AlgebraicGeometry.Etale.{u})
    (pullbackOpenCover V r)
  intro i
  change ι at i
  have hp := ((IsPullback.of_hasPullback r (sigmaOverι V i)).flip).map (schemeYoneda S)
  have hi := hp.paste_vert h
  have he := (hb i).projection g
    ((schemeYoneda S).map (pullback.snd r (sigmaOverι V i)))
    (pullback.fst r (sigmaOverι V i) ≫ q) (by
      simpa only [Functor.map_comp] using hi)
  exact he

end Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart
