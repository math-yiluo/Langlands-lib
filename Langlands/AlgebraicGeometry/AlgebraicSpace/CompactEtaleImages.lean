import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubspaceGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeHelpers

/-! # Compact etale images inside representable open subfunctors -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.CompactEtaleImages

variable {S : Scheme.{u}} {Y : AlgebraicSpace S} {U : Over S}

/-- The sheafified image of a scheme chart. -/
def imageSubfunctor (a : (schemeYoneda S).obj U ⟶ Y.presheaf) :
    Subfunctor Y.presheaf :=
  (Subfunctor.range a).sheafify (fppfTopology S)

/-- The actual open algebraic space given by the image of an etale scheme chart. -/
def etaleImage (Y : AlgebraicSpace S)
    (a : (schemeYoneda S).obj U ⟶ Y.presheaf) (ha : IsEtale a) :
    AlgebraicSpace S :=
  OpenSubspaceGeometry.openSubspace Y (imageSubfunctor a)
    (OpenSubfunctorImages.sheafify_range_open a ha)

/-- The canonical scheme atlas of the image. -/
def imageAtlas (a : (schemeYoneda S).obj U ⟶ Y.presheaf) (ha : IsEtale a) :
    (schemeYoneda S).obj U ⟶ (etaleImage Y a ha).presheaf :=
  Subfunctor.toRangeSheafify (fppfTopology S) a

theorem imageAtlas_isEtale
    (a : (schemeYoneda S).obj U ⟶ Y.presheaf) (ha : IsEtale a) :
    IsEtale (imageAtlas a ha) :=
  OpenSubfunctorImages.toRangeSheafify_isEtale a ha

theorem imageAtlas_isSurjective
    (a : (schemeYoneda S).obj U ⟶ Y.presheaf) (ha : IsEtale a) :
    IsSurjective (imageAtlas a ha) :=
  OpenSubfunctorImages.toRangeSheafify_isSurjective a ha

/-- The etale image has a compact atlas whenever its source scheme is compact. -/
theorem etaleImage_isQuasiCompact [CompactSpace U.left]
    (a : (schemeYoneda S).obj U ⟶ Y.presheaf) (ha : IsEtale a) :
    IsQuasiCompact (etaleImage Y a ha) :=
  ⟨U, imageAtlas a ha, imageAtlas_isEtale a ha, imageAtlas_isSurjective a ha,
    inferInstance⟩

/-- The etale image inherits relative quasi-separatedness from its ambient space. -/
theorem etaleImage_isQuasiSeparated
    (hY : IsQuasiSeparated Y)
    (a : (schemeYoneda S).obj U ⟶ Y.presheaf) (ha : IsEtale a) :
    IsQuasiSeparated (etaleImage Y a ha) :=
  OpenSubspaceGeometry.isQuasiSeparated_openSubspace hY (imageSubfunctor a)
    (OpenSubfunctorImages.sheafify_range_open a ha)

/-- A chart factoring through an open has its entire sheafified image in that open. -/
theorem imageSubfunctor_le_open
    (a : (schemeYoneda S).obj U ⟶ Y.presheaf)
    {A : Subfunctor Y.presheaf} (hA : IsOpenImmersion A.ι)
    (h : Subfunctor.range a ≤ A) :
    imageSubfunctor a ≤ A := by
  intro T x hx
  apply OpenSubfunctorImages.mem_of_coveringSieve hA x
  apply (fppfTopology S).superset_covering ?_ hx
  intro V f hf
  exact h _ hf

/-- An open containing a chart's residue-field value also contains the
sheafified image of an affine open restriction through that chart point. -/
theorem exists_affine_restriction_inside_open
    (a : (schemeYoneda S).obj U ⟶ Y.presheaf)
    (A : Subfunctor Y.presheaf) (hA : IsOpenImmersion A.ι)
    (x : U.left)
    (hx : Y.presheaf.map (OpenSubfunctorPoints.residueFieldPoint U x).op
      (uliftYonedaEquiv a) ∈
        A.obj (op (OpenSubfunctorPoints.residueFieldTest U x))) :
    ∃ (V : Over S) (j : V ⟶ U) (d : V.left),
      IsAffine V.left ∧
        _root_.AlgebraicGeometry.IsOpenImmersion j.left ∧
          j.left d = x ∧
            imageSubfunctor ((schemeYoneda S).map j ≫ a) ≤ A := by
  let R := hA.rep.pullback a
  let q : R ⟶ U := hA.rep.snd a
  let : _root_.AlgebraicGeometry.IsOpenImmersion q.left := hA.property_snd a
  have hxrange : x ∈ Set.range q.left := by
    have h := (OpenSubfunctorPoints.mem_map_iff_range_subset hA
      (uliftYonedaEquiv a) (OpenSubfunctorPoints.residueFieldPoint U x)).mp hx
    rw [Equiv.symm_apply_apply] at h
    exact h ⟨(default : Spec (U.left.residueField x)),
      U.left.fromSpecResidueField_apply x _⟩
  obtain ⟨z, hz⟩ := hxrange
  obtain ⟨i, d, hd⟩ := R.left.affineCover.exists_eq z
  let V : Over S := Over.mk (R.left.affineCover.f i ≫ R.hom)
  let r : V ⟶ R := Over.homMk (R.left.affineCover.f i)
  let j := r ≫ q
  have hj : _root_.AlgebraicGeometry.IsOpenImmersion j.left := by
    change _root_.AlgebraicGeometry.IsOpenImmersion
      (R.left.affineCover.f i ≫ q.left)
    infer_instance
  have heq : (schemeYoneda S).map j ≫ a =
      ((schemeYoneda S).map r ≫ hA.rep.fst a) ≫ A.ι := by
    dsimp [j]
    rw [Functor.map_comp, Category.assoc, ← (hA.rep.isPullback a).w,
      Category.assoc]
  have hrange : Subfunctor.range ((schemeYoneda S).map j ≫ a) ≤ A := by
    rintro T y ⟨w, rfl⟩
    rw [heq]
    exact (((schemeYoneda S).map r ≫ hA.rep.fst a).app T w).property
  refine ⟨V, j, d, inferInstanceAs (IsAffine (R.left.affineCover.X i)),
    hj, ?_, imageSubfunctor_le_open _ hA hrange⟩
  change q.left ((R.left.affineCover.f i) d) = x
  rw [hd]
  exact hz

end Langlands.AlgebraicGeometry.AlgebraicSpace.CompactEtaleImages
