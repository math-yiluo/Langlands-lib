import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Aubert.General.RationalOppositeParabolic
import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Rational.ParabolicFunctorCocharacter
import Langlands.GroupScheme.Rational.LeviMultiplication
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.GeometricUnipotentRadicalComparison
import Langlands.GroupScheme.Reductive.UnipotentFieldExtensionProof
import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof

/-! # An actual opposite parabolic for a represented parabolic

From the proved dynamic description of actual parabolics, every rational parabolic
`P = MU` with rational Levi `M` has an actual opposite parabolic `P̄ = M Ū`: the
dynamic parabolic of the inverse of a cocharacter realizing both `P` and `M`.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily.InducedTwistsDetection

open Langlands.GroupScheme Langlands.Aubert.General.RepresentedParabolic

variable {k : Type u} [Field k]

/-- Every actual rational parabolic with a rational Levi has an actual opposite
parabolic with the same Levi map, given by the inverse of a cocharacter realizing
both; its radical is the corresponding dynamic contraction subgroup. -/
theorem exists_opposite_parabolic
    {G P M : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {p : P ⟶ G} {l : M ⟶ P} (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) :
    ∃ (Pbar Nbar : GroupScheme (Spec (CommRingCat.of k))) (pbar : Pbar ⟶ G)
      (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G),
      IsParabolicSubgroup pbar ∧ IsRationalLeviSubgroup mbar ∧
      LeviSubgroup.IsGeometricUnipotentRadical nbar ∧
      IsIso (subgroupMultiplication mbar nbar) ∧
      mbar ≫ pbar = l ≫ p ∧
      pointImage p ⊓ pointImage pbar = pointImage (l ≫ p) ∧
      SubgroupFunctor.range pbar = Dynamic.parabolic χ ∧
      SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer χ ∧
      SubgroupFunctor.range (nbar ≫ pbar) = Dynamic.unipotent χ := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.isSeparated
  obtain ⟨χ, hPχ, hMχ⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
      dynamicGeometricUnipotentRadical hG hp hl
  let χ' := Dynamic.inverseCocharacter χ
  have hZ' : Dynamic.centralizer χ' = Dynamic.centralizer χ :=
    Dynamic.centralizer_inverseCocharacter χ
  let pbar := Dynamic.Affine.parabolicHom χ'
  have hpP : (Dynamic.parabolic χ').IsRepresentedBy pbar :=
    Dynamic.Affine.isRepresentedBy_parabolicHom χ'
  have hpbarc : IsClosedSubgroup pbar := Dynamic.Affine.isClosedSubgroup_parabolicHom χ'
  have : IsAffineHom (Dynamic.Affine.parabolicScheme χ').X.hom := hpbarc.isAffineHom
  have hleM : SubgroupFunctor.range (l ≫ p) ≤ Dynamic.parabolic χ' := by
    rw [hMχ, ← hZ']
    exact Dynamic.centralizer_le_parabolic χ'
  let mbar := hpP.factorHom (l ≫ p) hleM
  have hmbar_comp : mbar ≫ pbar = l ≫ p := hpP.factorHom_comp (l ≫ p) hleM
  have hu := Dynamic.Affine.isRepresentedBy_unipotentHom χ'
  have hleU : SubgroupFunctor.range (Dynamic.Affine.unipotentHom χ') ≤ Dynamic.parabolic χ' := by
    rw [hu.2]
    exact Dynamic.unipotent_le_parabolic χ'
  let nbar := hpP.factorHom (Dynamic.Affine.unipotentHom χ') hleU
  have hnbar_comp : nbar ≫ pbar = Dynamic.Affine.unipotentHom χ' :=
    hpP.factorHom_comp (Dynamic.Affine.unipotentHom χ') hleU
  have hlpc : IsClosedSubgroup (l ≫ p) := hl.isClosedSubgroup.comp hp.isClosedSubgroup
  have hlpmono : Mono (l ≫ p).hom.hom := by
    have := hlpc.mono
    exact Over.mono_of_mono_left _
  have hZrep : (Dynamic.centralizer χ').IsRepresentedBy (l ≫ p) := ⟨hlpmono, by rw [hZ', hMχ]⟩
  have hnrep : (Dynamic.unipotent χ').IsRepresentedBy (nbar ≫ pbar) := by
    rw [hnbar_comp]
    exact hu
  have hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar :=
    (dynamicGeometricUnipotentRadical k G hG χ' _ _ pbar nbar hpP hnrep).leviSubgroup_of_unipotentFieldExtension
      unipotentFieldExtensionStatement
  have hmulbar : IsIso (subgroupMultiplication mbar nbar) :=
    Dynamic.isIso_subgroupMultiplication hpP hZrep hu mbar nbar hmbar_comp hnbar_comp
  have hmbarc : IsClosedSubgroup mbar := IsClosedSubgroup.of_comp hpbarc (by rw [hmbar_comp]; exact hlpc)
  have hmbar : IsRationalLeviSubgroup mbar :=
    ⟨hpbarc.isAffineHom, hmbarc, hl.isConnectedReductive, ⟨_, nbar, hnbar, hmulbar⟩⟩
  have hpbar : IsParabolicSubgroup pbar :=
    Dynamic.Affine.isParabolicSubgroup_parabolicHom_of_parabolicDynamic parabolicDynamic hG χ'
  have hinf : pointImage p ⊓ pointImage pbar = pointImage (l ≫ p) := by
    have h := Dynamic.parabolic_inf_opposite_eq_centralizer χ
    rw [pointImage_eq_range_carrier, pointImage_eq_range_carrier, pointImage_eq_range_carrier,
      hPχ, hpP.2, hMχ]
    have h' := congrArg (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 _))) h
    simp only [SubgroupFunctor.inf_carrier] at h'
    exact h'
  refine ⟨_, _, pbar, mbar, nbar, χ', hpbar, hmbar, hnbar, hmulbar, hmbar_comp, hinf, hpP.2,
    ?_, hnrep.2⟩
  rw [hZ', hMχ]

end Langlands.Renard.AlgebraicFamily.InducedTwistsDetection
