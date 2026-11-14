import Langlands.GroupScheme.Rational.ParabolicSplitComponentStatements
import Langlands.GroupScheme.Rational.OriginalLeviCocharacter
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction
import Langlands.GroupScheme.Rational.ParabolicFunctorCocharacter
import Langlands.GroupScheme.Rational.AffineGeometricUnipotentRadical
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Rational Levi subgroups and centralizers of their split components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A subgroup of a connected reductive field group is a rational Levi factor
of a rational parabolic exactly when it is the centralizer of a split torus
that is its split component (Renard V.3.1). -/
theorem leviCentralizerCharacterization :
    LeviCentralizerCharacterizationStatement.{u} := by
  intro k _ G hG M m
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsSeparated G.X.hom := hG.isSeparated
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  constructor
  · rintro ⟨P, p, l, hp, hl, rfl⟩
    obtain ⟨⟨A, a, ha⟩, -⟩ := splitComponentStatement k M hl.isConnectedReductive
    obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG P p hp.isClosedSubgroup).1 hp
    have hP : (Dynamic.parabolic χ).IsRepresentedBy p :=
      ⟨hp.isClosedSubgroup.mono_overHom, hχ⟩
    obtain ⟨ν, -, -, hZ⟩ :=
      hl.exists_splitComponentCocharacter_of_dynamicParabolic hG χ hP ha
    have hclosed : IsClosedSubgroup (l ≫ p) :=
      hl.isClosedSubgroup.comp hp.isClosedSubgroup
    exact ⟨A, a ≫ l ≫ p, a,
      ⟨ha.1.1.1, ha.1.1.2.comp hclosed⟩,
      ⟨hclosed.mono_overHom, hZ.symm⟩, rfl, ha⟩
  · rintro ⟨A, a, aM, ha, hm, -, -⟩
    obtain ⟨ν, hν⟩ := ha.1.exists_cocharacter_centralizer_eq a
    let χ := CommGroupScheme.groupHom ν ≫ a
    have hZ : (Dynamic.centralizer χ).IsRepresentedBy m := by
      change (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ a)).IsRepresentedBy m
      rwa [hν]
    let P := Dynamic.Affine.parabolicScheme χ
    let p : P ⟶ G := Dynamic.Affine.parabolicHom χ
    have hP : (Dynamic.parabolic χ).IsRepresentedBy p :=
      Dynamic.Affine.isRepresentedBy_parabolicHom χ
    have hU := Dynamic.Affine.isRepresentedBy_unipotentHom χ
    let l := hP.factorHom m (by rw [hZ.2]; exact Dynamic.centralizer_le_parabolic χ)
    let r := hP.factorHom (Dynamic.Affine.unipotentHom χ)
      (by rw [hU.2]; exact Dynamic.unipotent_le_parabolic χ)
    have hl : l ≫ p = m := hP.factorHom_comp _ _
    have hr : r ≫ p = Dynamic.Affine.unipotentHom χ := hP.factorHom_comp _ _
    have hM := dynamicCentralizerReductive k G hG χ M m
      (Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer χ hZ) hZ
    have hrad := dynamicGeometricUnipotentRadical k G hG χ P _ p r hP
      (by rw [hr]; exact hU)
    exact ⟨P, p, l,
      Dynamic.Affine.isParabolicSubgroup_parabolicHom_of_parabolicDynamic parabolicDynamic hG χ,
      Dynamic.isRationalLeviSubgroup_of_geometricUnipotentRadical hP hZ hU l r hl hr hM hrad,
      hl⟩

end Langlands.GroupScheme
