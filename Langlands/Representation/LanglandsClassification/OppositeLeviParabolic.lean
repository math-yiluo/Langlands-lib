import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Rational.AffineGeometricUnipotentRadical
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Rational.DynamicSemistandardIntersectionModels
import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry

/-! # An actual opposite parabolic with the specified rational Levi

This internal assembly chooses the inverse dynamic parabolic, retains the
original Levi scheme and its ambient embedding, and supplies all radical
and multiplication certificates required by the representation functors.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k]
  {G P M : GroupScheme (Spec (CommRingCat.of k))}

/-- Actual opposite data with the same Levi scheme and exactly the same
ambient Levi homomorphism. No topology or representation is part of the data. -/
structure OppositeLeviParabolicData (p : P ⟶ G) (l : M ⟶ P) where
  parabolic : GroupScheme (Spec (CommRingCat.of k))
  radical : GroupScheme (Spec (CommRingCat.of k))
  inclusion : parabolic ⟶ G
  levi : M ⟶ parabolic
  unipotent : radical ⟶ parabolic
  isParabolic : IsParabolicSubgroup inclusion
  isLevi : IsRationalLeviSubgroup levi
  isRadical : LeviSubgroup.IsGeometricUnipotentRadical unipotent
  multiplication : IsIso (subgroupMultiplication levi unipotent)
  levi_comp : levi ≫ inclusion = l ≫ p
  intersection : pointImage p ⊓ pointImage inclusion = pointImage (l ≫ p)

/-- A connected reductive group and an actual rational parabolic with a
specified rational Levi supply all actual opposite data unconditionally. -/
def oppositeLeviParabolic (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) :
    OppositeLeviParabolicData p l := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsSeparated G.X.hom := hG.isSeparated
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := DynamicLeviConjugacy.parabolicLeviRealizingCocharacter
    parabolicDynamic dynamicGeometricUnipotentRadical hG hp hl
  have hP := (DynamicLeviConjugacy.parabolicLeviRealizingCocharacter_spec
    parabolicDynamic dynamicGeometricUnipotentRadical hG hp hl).1
  have hM := (DynamicLeviConjugacy.parabolicLeviRealizingCocharacter_spec
    parabolicDynamic dynamicGeometricUnipotentRadical hG hp hl).2
  let ψ := Dynamic.oppositeCocharacter χ
  let Q := Dynamic.Affine.parabolicScheme ψ
  let U := Dynamic.Affine.unipotentScheme ψ
  let q : Q ⟶ G := Dynamic.Affine.parabolicHom ψ
  let u : U ⟶ G := Dynamic.Affine.unipotentHom ψ
  have hQ : (Dynamic.parabolic ψ).IsRepresentedBy q :=
    Dynamic.Affine.isRepresentedBy_parabolicHom ψ
  have hU : (Dynamic.unipotent ψ).IsRepresentedBy u :=
    Dynamic.Affine.isRepresentedBy_unipotentHom ψ
  have hZ : (Dynamic.centralizer ψ).IsRepresentedBy (l ≫ p) := by
    rw [Dynamic.centralizer_oppositeCocharacter, ← hM]
    exact (hl.isClosedSubgroup.comp hp.isClosedSubgroup).isRepresentedBy_range
  let lQ : M ⟶ Q := Dynamic.centralizerToParabolic hQ hZ
  let rQ : U ⟶ Q := Dynamic.unipotentToParabolic hQ hU
  have hlQ : lQ ≫ q = l ≫ p := Dynamic.centralizerToParabolic_comp hQ hZ
  have hrQ : rQ ≫ q = u := Dynamic.unipotentToParabolic_comp hQ hU
  have hqc : IsClosedSubgroup q := Dynamic.Affine.isClosedSubgroup_parabolicHom ψ
  let : IsClosedImmersion q.hom.hom.left := hqc
  let : IsAffineHom Q.X.hom := by
    rw [← Over.w q.hom.hom]
    infer_instance
  have hrad : IsGeometricUnipotentRadical rQ :=
    dynamicGeometricUnipotentRadical k G hG ψ Q U q rQ hQ (by rw [hrQ]; exact hU)
  have hmul : IsIso (subgroupMultiplication lQ rQ) :=
    Dynamic.isIso_subgroupMultiplication hQ hZ hU lQ rQ hlQ hrQ
  have hlevi : IsRationalLeviSubgroup lQ :=
    Dynamic.isRationalLeviSubgroup_of_geometricUnipotentRadical
      hQ hZ hU lQ rQ hlQ hrQ hl.isConnectedReductive hrad
  refine {
    parabolic := Q
    radical := U
    inclusion := q
    levi := lQ
    unipotent := rQ
    isParabolic := isParabolicSubgroup_of_range_eq_dynamicParabolic hG q hqc ψ hQ.2
    isLevi := hlevi
    isRadical := hrad.leviSubgroup
    multiplication := hmul
    levi_comp := hlQ
    intersection := ?_ }
  have hfun : SubgroupFunctor.range p ⊓ SubgroupFunctor.range q =
      SubgroupFunctor.range (l ≫ p) := by
    rw [hP, hQ.2, hM]
    exact Dynamic.parabolic_inf_opposite_eq_centralizer χ
  exact congrArg
    (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) hfun

end Langlands.Aubert.General.RepresentedParabolic
