import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionClosedEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.SectionEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineWeilRestrictionEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionGeometricInputsStatement

/-! # Diagonals under finite locally free Weil restriction -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace
namespace WeilRestrictionDiagonalGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Affine-test equality-locus representatives glue on every scheme test. -/
theorem exists_sectionEqualizer_representation_of_affine
    {S : Scheme.{u}} {F : Presheaf S}
    (hF : Presheaf.IsSheaf (fppfTopology S) F)
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (h : ∀ (U : Over S) [IsAffine U.left] (x y : F.obj (op U)),
      ∃ W : Over U.left,
        Nonempty ((schemeYoneda U.left).obj W ≅ sectionEqualizer x y) ∧ P W.hom)
    (T : Over S) (x y : F.obj (op T)) :
    ∃ W : Over T.left,
      Nonempty ((schemeYoneda T.left).obj W ≅ sectionEqualizer x y) ∧ P W.hom := by
  let 𝒰 := T.left.affineCover
  let U (i : 𝒰.I₀) : Over S := Over.mk (𝒰.f i ≫ T.hom)
  let k (i : 𝒰.I₀) : U i ⟶ T := Over.homMk (𝒰.f i)
  have hlocal (i : 𝒰.I₀) : ∃ W : Over (𝒰.X i),
      Nonempty ((schemeYoneda (𝒰.X i)).obj W ≅
        sectionEqualizer (F.map (k i).op x) (F.map (k i).op y)) ∧ P W.hom := by
    have : IsAffine (U i).left := inferInstanceAs (IsAffine (T.left.affineCover.X i))
    exact h (U i) _ _
  choose W he hW using hlocal
  let e (i : 𝒰.I₀) := Classical.choice (he i)
  let e' (i : 𝒰.I₀) : (schemeYoneda (𝒰.X i)).obj (W i) ≅
      (Over.map (𝒰.f i)).op ⋙ sectionEqualizer x y :=
    e i ≪≫ (sectionEqualizerRestrictIso x y (𝒰.f i)).symm
  obtain ⟨V, ⟨eV⟩⟩ := LocalRepresentation.exists_representation
    (isSheaf_sectionEqualizer hF x y) 𝒰 W e'
  exact ⟨V, ⟨eV⟩,
    LocalRepresentation.property_of_local_representations P V eV 𝒰 W e' hW⟩

/-- The diagonal criterion can be checked by full equality-locus representations
on affine test schemes. -/
theorem relative_diagonal_of_affine_sectionEqualizer
    {S : Scheme.{u}} {F : Presheaf S}
    (hF : Presheaf.IsSheaf (fppfTopology S) F)
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (h : ∀ (U : Over S) [IsAffine U.left] (x y : F.obj (op U)),
      ∃ W : Over U.left,
        Nonempty ((schemeYoneda U.left).obj W ≅ sectionEqualizer x y) ∧ P W.hom) :
    (P.inverseImage (Over.forget S)).relative (schemeYoneda S) (diag F) := by
  apply relative_diag_of_representsEqualizer P
  intro T x y
  obtain ⟨W, ⟨e⟩, hW⟩ := exists_sectionEqualizer_representation_of_affine hF P h T x y
  obtain ⟨hm, hE⟩ := representsEqualizer_of_sectionEqualizerIso x y W e
  exact ⟨_, sectionTestMap W, hm, hE, hW⟩

end WeilRestrictionDiagonalGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Finite locally free restriction of scalars preserves representable
quasi-compact diagonals and representable closed diagonals. -/
theorem weilRestrictionDiagonal_proof : WeilRestrictionDiagonalStatement.{u} := by
  intro R R' _ _ _ _ _ X' hX
  let F := ((ringWeilRestriction R R').obj X'.toSheaf).obj
  have hF : Presheaf.IsSheaf (fppfTopology (Spec (CommRingCat.of R))) F :=
    ((ringWeilRestriction R R').obj X'.toSheaf).property
  constructor
  · apply WeilRestrictionDiagonalGeometry.relative_diagonal_of_affine_sectionEqualizer
      hF (@QuasiCompact.{u})
    intro T _ x y
    obtain ⟨W, he, hqc, _⟩ :=
      exists_affineTest_sectionEqualizer_weil R R' X' hX T x y
    exact ⟨W, he, hqc⟩
  · intro hsep
    apply WeilRestrictionDiagonalGeometry.relative_diagonal_of_affine_sectionEqualizer
      hF (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
    intro T _ x y
    obtain ⟨W, he, _, hclosed⟩ :=
      exists_affineTest_sectionEqualizer_weil R R' X' hX T x y
    exact ⟨W, he, hclosed hsep⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
