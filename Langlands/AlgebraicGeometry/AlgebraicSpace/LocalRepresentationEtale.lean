import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationGluing
import Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPairDiagonal
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Proof
import Mathlib.AlgebraicGeometry.Cover.Sigma

/-! # Algebraic spaces from étale-local scheme representations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {B U : Scheme.{u}} {F : Presheaf B} (j : U ⟶ B) (H : Over U)
    (e : (schemeYoneda U).obj H ≅ (Over.map j).op ⋙ F)

/-- A representation over an étale base scheme gives a representable étale chart. -/
theorem chart_isEtale (hj : Etale j) : IsEtale (chart j H e) := by
  rw [← chartProductIso_hom_fst]
  exact (MorphismProperty.cancel_left_of_respectsIso
    ((MorphismProperty.inverseImage (@Etale.{u}) (Over.forget B)).relative
      (schemeYoneda B)) _ _).mpr
    (extProd.relative_fst (@Etale.{u}) (Λ := Over.mk j) hj)

/-- A representation over a surjective base scheme gives a representable surjective chart. -/
theorem chart_isSurjective (hj : Surjective j) : IsSurjective (chart j H e) := by
  rw [← chartProductIso_hom_fst]
  exact (MorphismProperty.cancel_left_of_respectsIso
    ((MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget B)).relative
      (schemeYoneda B)) _ _).mpr
    (extProd.relative_fst (@Surjective.{u}) (Λ := Over.mk j) hj)

/-- An fppf sheaf represented after one étale surjective base change is an algebraic space. -/
theorem isAlgebraicSpace_of_single_representation {Q : FppfSheaf B}
    (e : (schemeYoneda U).obj H ≅ (Over.map j).op ⋙ Q.obj)
    (hj : Etale j) (hs : Surjective j) : IsAlgebraicSpace B Q := by
  let a := chart j H e
  have ha : IsEtale a := chart_isEtale j H e hj
  have hsa : IsSurjective a := chart_isSurjective j H e hs
  let : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology B) a :=
    isLocallySurjective_of_isEtale a ha hsa
  obtain ⟨R, t, s, h, ht, _⟩ := exists_kernelPair ha
  have : Etale t.left := ht
  exact ⟨KernelPair.hasRepresentableDiagonal_of_isPullback
    LocallyQuasiFiniteDescent.fppfSeparatedLocallyQuasiFiniteDescent a h
      (inferInstanceAs (LocallyOfFiniteType t.left)),
    ⟨(Over.map j).obj H, a, ha, hsa⟩⟩

/-- Representations over the members of an arbitrary étale cover give an algebraic space.
The cover is collapsed to its scheme coproduct; no finiteness assumption is needed. -/
theorem isAlgebraicSpace_of_cover {Q : FppfSheaf B}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) B)
    (H : ∀ i, Over (𝒰.X i))
    (e : ∀ i, (schemeYoneda (𝒰.X i)).obj (H i) ≅
      (Over.map (𝒰.f i)).op ⋙ Q.obj) : IsAlgebraicSpace B Q := by
  let j : (∐ 𝒰.X) ⟶ B := Sigma.desc 𝒰.f
  let F' := (Over.map j).op ⋙ Q.obj
  have hF' : CategoryTheory.Presheaf.IsSheaf (fppfTopology (∐ 𝒰.X)) F' :=
    (Over.map j).op_comp_isSheaf (fppfTopology (∐ 𝒰.X)) (fppfTopology B) Q
  have e' : ∀ i, (schemeYoneda (𝒰.X i)).obj (H i) ≅
      (Over.map (Sigma.ι 𝒰.X i)).op ⋙ F' := by
    intro i
    change (schemeYoneda (𝒰.X i)).obj (H i) ≅
      ((Over.map (Sigma.ι 𝒰.X i) ⋙ Over.map j).op ⋙ Q.obj)
    rw [← Over.mapComp_eq, Sigma.ι_comp_desc]
    exact e i
  obtain ⟨V, ⟨eV⟩⟩ := exists_representation hF' (sigmaOpenCover 𝒰.X) H e'
  have hj : Etale j := 𝒰.sigma.map_prop PUnit.unit
  have hs : Surjective j := ⟨fun x => by
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    exact ⟨Sigma.ι 𝒰.X i y, by simp [j, ← Scheme.Hom.comp_apply]⟩⟩
  exact isAlgebraicSpace_of_single_representation j V eV hj hs

/-- The original sheaf as an algebraic space, using supplied étale-local representations. -/
def ofCover (Q : FppfSheaf B)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) B)
    (H : ∀ i, Over (𝒰.X i))
    (e : ∀ i, (schemeYoneda (𝒰.X i)).obj (H i) ≅
      (Over.map (𝒰.f i)).op ⋙ Q.obj) : Langlands.AlgebraicGeometry.AlgebraicSpace B :=
  ⟨Q, isAlgebraicSpace_of_cover 𝒰 H e⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentation
