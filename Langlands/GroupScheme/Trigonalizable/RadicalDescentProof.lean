import Langlands.GroupScheme.Trigonalizable.RadicalDescentStatement
import Langlands.GroupScheme.Trigonalizable.SeparableCriterionProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Rational.AffineGeometricUnipotentRadical
import Langlands.GroupScheme.Rational.GeometricRadicalTorusQuotient
import Langlands.GroupScheme.Reductive.SmoothQuotientRadicalExtension

/-! # Separable trigonalizability and descent of the geometric unipotent radical -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Corollary 16.31. A smooth connected affine solvable group is trigonalizable
 over a separable algebraic extension exactly when its geometric unipotent radical
 descends as a closed subgroup. -/
theorem separablyTrigonalizableRadicalDescent :
    SeparablyTrigonalizableRadicalDescentStatement.{u} := by
  intro k _ G _ _ _ hG
  have hcriterion := (separablyTrigonalizableCriterion k G).1
  constructor
  · intro h
    obtain ⟨U, M, i, q, hi, hU, _, hq, hM⟩ := hcriterion.mp h
    let b := toAlgebraicClosure k
    let B := GroupScheme.baseChange b
    have : Smooth (B.obj G).X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
    have : IsAffineHom (B.obj G).X.hom := inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
    have : ConnectedSpace (B.obj G).X.left := G.connectedSpace_baseChange_of_smooth_affine b
    have hGB : IsSolvableGroupScheme (B.obj G) :=
      solvableFieldExtensionStatement k (AlgebraicClosure k) b G inferInstance hG
    obtain ⟨V, D, j, r, hj, hs, hc, hV, hn, hr, hD⟩ :=
      solvableTorusQuotient (AlgebraicClosure k) (B.obj G) hGB
    have : IsAffineHom U.X.hom := hi.isAffineHom
    have hiB : IsClosedSubgroup (B.map i) := hi.baseChange b
    have hqB : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (B.map i)) (B.map q) := by
      rw [SubgroupFunctor.range_baseChangeHom]
      exact hq.baseChange b
    have hMB : IsMultiplicativeType (B.obj M) :=
      MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic
        k (AlgebraicClosure k) M hM
    have hiGreat := IsUnipotent.isGreatestUnipotentSubgroup hiB
      (hU.baseChange (K := AlgebraicClosure k)) hqB hMB
    have hjGreat := IsUnipotent.isGreatestUnipotentSubgroup hj hV hr
      hD.isTorus.isMultiplicativeType
    have hjRadical : IsUnipotentRadical j :=
      ⟨hj, hs, hc, hV, hn, fun W a ha _ _ hW _ => hjGreat.greatest W a ha hW⟩
    have hiRadical : IsUnipotentRadical (B.map i) :=
      hjRadical.of_range_eq hiB (hjGreat.range_eq hiGreat)
    have hiGeometric : LeviSubgroup.IsGeometricUnipotentRadical i :=
      ⟨hiRadical.of_baseChange (K := AlgebraicClosure k) hi, hiRadical⟩
    exact ⟨U, i, hiGeometric.isGeometricUnipotentRadical⟩
  · rintro ⟨U, i, hi⟩
    have hi' := hi.leviSubgroup
    let D := hi'.torusQuotient solvableTorusQuotient hG
    exact hcriterion.mpr ⟨U, D.quotient, i, D.projection, hi'.1.isClosedSubgroup,
      hi'.1.isUnipotent, hi'.1.isNormal, D.isFppfQuotient, D.isTorus.isMultiplicativeType⟩

end Langlands.GroupScheme
