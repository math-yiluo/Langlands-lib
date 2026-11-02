import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAlgebraicSpaceQuotientProof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleAtlasFppfSheafStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleKernelPairComparison

/-! # Fppf descent for an etale sheaf with an etale scheme atlas -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Transport the absolute quotient interface back to the original represented
kernel pair in the scheme slice. -/
theorem quotient_of_represented_etale_kernelPair
    (hQ : EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement.{u})
    {S : Scheme.{u}} {F : Presheaf S} {U R : Over S} (t s : R ⟶ U)
    (a : (schemeYoneda S).obj U ⟶ F)
    (ha : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (ht : Etale t.left) (hs : Etale s.left) :
    ∃ (Q : AlgebraicSpace S) (b : (schemeYoneda S).obj U ⟶ Q.presheaf),
      IsEtale b ∧ IsSurjective b ∧
        IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) b b := by
  let E := EtaleEquivalenceRelation.ofKernelPair t s a ha ht hs
  have hb : E.t ≫ U.hom = E.s ≫ U.hom := (Over.w t).trans (Over.w s).symm
  obtain ⟨Q, b, hbe, hbs, hpb⟩ := hQ S E U.hom hb
  refine ⟨Q, b, hbe, hbs, ?_⟩
  let R₀ : Over S := Over.mk (E.t ≫ U.hom)
  let e : R₀ ≅ R := Over.isoMk (Iso.refl _) (by
    change 𝟙 R.left ≫ R.hom = t.left ≫ U.hom
    simpa only [Category.id_comp] using (Over.w t).symm)
  apply hpb.of_iso ((schemeYoneda S).mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom]
    congr 1
  · simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom]
    congr 1
  · simp
  · simp

/-- An etale sheaf with representable diagonal and an etale surjective scheme
atlas is a sheaf for the full fppf topology. -/
theorem etaleAtlasFppfSheaf : EtaleAtlasFppfSheafStatement.{u} := by
  intro S F hF _ hAtlas
  obtain ⟨U, a, ha, hs⟩ := hAtlas
  obtain ⟨R, t, s, hA, ht, hst⟩ := exists_kernelPair ha
  obtain ⟨Q, b, hb, hbs, hB⟩ :=
    quotient_of_represented_etale_kernelPair
      etaleEquivalenceRelationAlgebraicSpaceQuotient t s a hA ht hst
  exact isSheaf_fppf_of_common_etale_kernelPair (G := Q.toSheaf) hF t s a b
    (isLocallySurjective_etale_of_isEtale_isSurjective a ha hs)
    (isLocallySurjective_etale_of_isEtale_isSurjective b hb hbs) hA hB

end Langlands.AlgebraicGeometry.AlgebraicSpace
