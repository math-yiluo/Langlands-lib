import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionDiagonalGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.Morphisms.GenericFiniteness

/-! # Quasi-affine equalizer loci for algebraic spaces -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace
namespace WeilRestrictionDiagonalGeometry

set_option backward.isDefEq.respectTransparency false

/-- Every represented projection of a diagonal is a scheme monomorphism. -/
theorem relative_diagonal_with_mono {S : Scheme.{u}} {F : Presheaf S}
    {P : MorphismProperty Scheme.{u}}
    (hF : (P.inverseImage (Over.forget S)).relative (schemeYoneda S) (diag F)) :
    ((P ⊓ MorphismProperty.monomorphisms Scheme.{u}).inverseImage (Over.forget S)).relative
      (schemeYoneda S) (diag F) := by
  refine ⟨hF.rep, ?_⟩
  intro U V g a p h
  refine ⟨hF.property g a p h, ?_⟩
  have hm : Mono ((schemeYoneda S).map p) := h.mono_snd_of_mono
  have : Mono p := (schemeYoneda S).mono_of_mono_map hm
  exact inferInstanceAs (Mono p.left)

/-- Over an affine test, a quasi-separated algebraic space has quasi-affine equalizer loci. -/
theorem exists_quasiAffine_representsEqualizer {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hX : IsQuasiSeparated X) {U : Over S} [IsAffine U.left]
    (x y : X.presheaf.obj (op U)) :
    ∃ (Z : Over S) (ι : Z ⟶ U), Mono ι.left ∧ RepresentsEqualizer ι x y ∧
      LocallyOfFiniteType ι.left ∧ QuasiCompact ι.left ∧ Z.left.IsQuasiAffine := by
  have hL := locallyOfFiniteType_diagonal X
  let P : MorphismProperty Scheme.{u} := @QuasiCompact.{u} ⊓ @LocallyOfFiniteType.{u}
  have hQ : (MorphismProperty.inverseImage P
      (Over.forget S)).relative (schemeYoneda S) (diag X.presheaf) :=
    ⟨hX.rep, fun _ _ g a p h => ⟨hX.property g a p h, hL.property g a p h⟩⟩
  obtain ⟨Z, ι, hE, ⟨hqc, hlft⟩, hm⟩ :=
    exists_representsEqualizer_of_relative_diag (relative_diagonal_with_mono hQ) x y
  have : Mono ι.left := hm
  have : LocallyOfFiniteType ι.left := hlft
  have : QuasiCompact ι.left := hqc
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace ι.left
  have : LocallyQuasiFinite ι.left :=
    GenericFiniteness.locallyQuasiFinite_of_formallyUnramified ι.left
  exact ⟨Z, ι, hm, hE, hlft, hqc,
    LocallyQuasiFiniteDescent.isQuasiAffine_of_locallyQuasiFinite ι.left⟩

end WeilRestrictionDiagonalGeometry
end Langlands.AlgebraicGeometry.AlgebraicSpace
