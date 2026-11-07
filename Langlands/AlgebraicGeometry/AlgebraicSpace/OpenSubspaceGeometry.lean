import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorImages
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralCompactness

/-! # Open subspaces and compactness of finite scheme sources -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubspaceGeometry

variable {S : Scheme.{u}}

/-- The algebraic space defined by a representable open subfunctor. -/
def openSubspace (Y : AlgebraicSpace S) (A : Subfunctor Y.presheaf)
    (hA : IsOpenImmersion A.ι) : AlgebraicSpace S :=
  let hsh := OpenSubfunctorImages.isSheaf_of_open Y.toSheaf.property hA
  ⟨⟨A.toFunctor, hsh⟩,
    OpenSubfunctorLifting.open_subsheaf_isAlgebraicSpace Y A hA hsh⟩

/-- The actual inclusion of the open subspace into its ambient algebraic space. -/
def inclusion (Y : AlgebraicSpace S) (A : Subfunctor Y.presheaf)
    (hA : IsOpenImmersion A.ι) : openSubspace Y A hA ⟶ Y :=
  homMk A.ι

theorem inclusion_isOpenImmersion (Y : AlgebraicSpace S)
    (A : Subfunctor Y.presheaf) (hA : IsOpenImmersion A.ι) :
    IsOpenImmersion (hom (inclusion Y A hA)) :=
  hA

/-- Quasi-separatedness of an algebraic space passes to every open subspace. -/
theorem isQuasiSeparated_openSubspace {Y : AlgebraicSpace S}
    (hY : IsQuasiSeparated Y) (A : Subfunctor Y.presheaf)
    (hA : IsOpenImmersion A.ι) :
    IsQuasiSeparated (openSubspace Y A hA) := by
  let := MorphismProperty.relative_isStableUnderBaseChange (F := schemeYoneda S)
    (MorphismProperty.inverseImage (@QuasiCompact.{u}) (Over.forget S))
  exact MorphismProperty.of_isPullback
    (P := (MorphismProperty.inverseImage (@QuasiCompact.{u})
      (Over.forget S)).relative (schemeYoneda S))
    (OpenSubfunctorImages.diag_isPullback_of_mono A.ι) hY

/-- A scheme finite over an algebraic space with a compact atlas is compact. -/
theorem compactSpace_of_finite_source {Y : AlgebraicSpace S}
    (hY : IsQuasiCompact Y) {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ Y.presheaf) (ha : IsFinite a) :
    CompactSpace U.left := by
  obtain ⟨V, b, _, hbs, hV⟩ := hY
  let hr := ha.representable
  let W := hr.pullback b
  let p : W ⟶ V := hr.snd b
  obtain ⟨r, hrmap⟩ := (schemeYoneda S).map_surjective (hr.fst b)
  have sq : IsPullback ((schemeYoneda S).map r)
      ((schemeYoneda S).map p) a b := by
    rw [hrmap]
    exact hr.isPullback b
  let : _root_.AlgebraicGeometry.IsFinite p.left :=
    ha.projection b ((schemeYoneda S).map r) p sq
  let : Surjective r.left :=
    hbs.projection a ((schemeYoneda S).map p) r sq.flip
  let : CompactSpace V.left := hV
  let : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace p.left
  exact Function.Surjective.compactSpace r.left.continuous r.left.surjective

end Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubspaceGeometry
