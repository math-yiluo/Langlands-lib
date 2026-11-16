import Langlands.GroupScheme.RelativeLevi.ParabolicModelZariskiGluing
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # A single affine etale cover carrying a smooth proper parabolic model -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {hG : IsReductive G}

namespace SmoothProperModel

/-- A model for direct base change also represents the iterated base change,
via the canonical parabolic-presheaf comparisons. -/
def forComposite {U V : Scheme.{u}} (p : U ⟶ S) (q : V ⟶ U)
    (r : V ⟶ S) (h : q ≫ p = r)
    (d : SmoothProperModel ((GroupScheme.baseChange r).obj G) (hG.baseChange r)) :
    SmoothProperModel ((GroupScheme.baseChange q).obj
      ((GroupScheme.baseChange p).obj G)) ((hG.baseChange p).baseChange q) where
  scheme := d.scheme
  represents := d.represents.ofIso
    ((parabolicPresheafBaseChangeIso q (hG.baseChange p) ≪≫
      Functor.isoWhiskerLeft (Over.map q).op (parabolicPresheafBaseChangeIso p hG) ≪≫
      (Functor.associator (Over.map q).op (Over.map p).op
        (parabolicPresheaf G hG)).symm ≪≫
      Functor.isoWhiskerRight (NatIso.op (Over.mapComp q p))
        (parabolicPresheaf G hG) ≪≫
      Functor.isoWhiskerRight (NatIso.op (Over.mapCongr (q ≫ p) r h)).symm
        (parabolicPresheaf G hG) ≪≫
      (parabolicPresheafBaseChangeIso r hG).symm).symm)
  smooth := d.smooth
  proper := d.proper

/-- Models of the pulled-back group on arbitrary coproduct components assemble
into a model over the coproduct base. -/
def coproduct {I : Type u} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)
    (d : ∀ i, SmoothProperModel ((GroupScheme.baseChange (f i)).obj G)
      (hG.baseChange (f i))) :
    SmoothProperModel ((GroupScheme.baseChange (Sigma.desc f)).obj G)
      (hG.baseChange (Sigma.desc f)) :=
  zariskiGlue (sigmaOpenCover X) fun i =>
    forComposite (hG := hG) (Sigma.desc f) (Sigma.ι X i) (f i) (by simp) (d i)

end SmoothProperModel

/-- A single affine etale surjection carrying an actual smooth proper model
for parabolic subgroups of the pulled-back group. -/
structure AffineEtaleCoverModel (hG : IsReductive G) where
  scheme : Scheme.{u}
  affine : IsAffine scheme
  baseMap : scheme ⟶ S
  etale : Etale baseMap
  surjective : Surjective baseMap
  model : SmoothProperModel ((GroupScheme.baseChange baseMap).obj G)
    (hG.baseChange baseMap)

/-- Compactness extracts finitely many affine etale neighbourhoods. Their
finite coproduct is affine and carries the assembled smooth proper model. -/
theorem nonempty_affineEtaleCoverModel [CompactSpace S]
    (hfin : RelativeParabolicEtaleLocalFiniteTypesStatement.{u})
    (hG : IsReductive G) : Nonempty (AffineEtaleCoverModel hG) := by
  classical
  let a : ∀ s : S, AffineEtaleModel hG s := affineEtaleModel hfin hG
  have hopen (s : S) : IsOpen (Set.range (a s).baseMap) := by
    let : Etale (a s).baseMap := (a s).etale
    exact (a s).baseMap.isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover
    (fun s : S => Set.range (a s).baseMap)
    (fun s => (hopen s).mem_nhds ⟨(a s).point, (a s).point_over⟩)
  let X : t → Scheme.{u} := fun s => Spec (CommRingCat.of (a s.val).ring)
  let f : ∀ s : t, X s ⟶ S := fun s => (a s.val).baseMap
  have hcover (s : S) : ∃ i : t, s ∈ Set.range (f i) := by
    have hs : s ∈ (⊤ : Set S) := trivial
    rw [← ht, Set.mem_iUnion] at hs
    rcases hs with ⟨y, _, ⟨hy, rfl⟩, hs⟩
    exact ⟨⟨y, hy⟩, hs⟩
  have hf (s : t) : Etale (f s) := (a s.val).etale
  have ha (s : t) : IsAffine (X s) := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (a s.val).ring)))
  let : ∀ s : t, IsAffine (X s) := ha
  have hsurj : Surjective (Sigma.desc f) := by
    constructor
    intro s
    obtain ⟨i, y, hy⟩ := hcover s
    exact ⟨Sigma.ι X i y, by simpa [← Scheme.Hom.comp_apply] using hy⟩
  exact ⟨⟨∐ X, inferInstance, Sigma.desc f,
    IsZariskiLocalAtSource.sigmaDesc hf, hsurj,
    SmoothProperModel.coproduct (hG := hG) X f (fun s => (a s.val).model)⟩⟩

/-- Choose the actual affine etale cover and its smooth proper parabolic model. -/
def affineEtaleCoverModel [CompactSpace S]
    (hfin : RelativeParabolicEtaleLocalFiniteTypesStatement.{u})
    (hG : IsReductive G) : AffineEtaleCoverModel hG :=
  Classical.choice (nonempty_affineEtaleCoverModel hfin hG)

end Langlands.GroupScheme.ParabolicSubgroupModuli
