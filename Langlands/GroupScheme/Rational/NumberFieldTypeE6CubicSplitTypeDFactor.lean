import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexNonTypeAQuadraticIsotropy
import Langlands.GroupScheme.Rational.TypeE6CubicSplitNonTypeAFactor
import Langlands.GroupScheme.Reductive.AbsoluteCartanClassificationProof

/-! # Orthogonal factors in the cubic splitting argument for E6 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

private theorem TitsIndexData.exists_typeD_of_small_anisotropic_factor
    {F : Type u} [Field F] [NumberField F]
    {Q : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom]
    (d : TitsIndexData Q) (hF : IsTotallyComplex F)
    (hsc : IsSimplyConnected Q) (habs : IsAbsolutelyAlmostSimple Q) (hAni : IsAnisotropic Q)
    (hrank : Nat.card d.Vertex ≤ 5) (hA : ¬ ∃ n : ℕ, d.HasCartanMatrix (CartanMatrix.A n))
    (hF4 : ¬ d.HasCartanMatrix CartanMatrix.F₄) :
    ∃ n : ℕ, 4 ≤ n ∧ n ≤ 5 ∧ d.HasCartanMatrix (CartanMatrix.D n) := by
  have hle {n : ℕ} (e : d.Vertex ≃ Fin n) : n ≤ 5 := by
    rwa [Nat.card_congr e, Nat.card_fin] at hrank
  rcases absolutelyAlmostSimpleCartanClassification F Q d habs with
    ⟨n, _, h⟩ | ⟨n, hn, e, h⟩ | ⟨n, hn, e, h⟩ | ⟨n, hn, e, h⟩ |
    ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | h | ⟨e, h⟩
  · exact (hA ⟨n, h⟩).elim
  · exact (d.not_isAnisotropic_of_typeB_totallyComplex hF hsc habs hn e h hAni).elim
  · exact (d.not_isAnisotropic_of_typeC_totallyComplex hF hsc habs hn e h hAni).elim
  · exact ⟨n, hn, hle e, e, h⟩
  · exact ((by decide : ¬ 6 ≤ 5) (hle e)).elim
  · exact ((by decide : ¬ 7 ≤ 5) (hle e)).elim
  · exact ((by decide : ¬ 8 ≤ 5) (hle e)).elim
  · exact (hF4 h).elim
  · have he := d.splitRank_eq_two_of_typeG2_totallyComplex hF hsc habs e h
    rw [show splitRank Q = 0 from hAni] at he
    exact ((by decide : (0 : ℕ∞) ≠ 2) he).elim

/-- Cubic splitting of anisotropic E6 over a totally complex number field
forces an actual anisotropic simply connected group of type D4 or D5 over
a finite extension of the ground field. -/
def NumberFieldTotallyComplexTypeE6CubicSplitTypeDFactorStatement : Prop :=
  ∀ (F K : Type u) [Field F] [NumberField F], IsTotallyComplex F →
    ∀ [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K],
      Module.finrank F K = 3 →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom], IsAnisotropic G → IsSimplyConnected G →
    ∀ (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap F K)).obj G))
      (e : p.base.support ≃ Fin 6),
      (∀ a b, p.rootDatum.pairing a.val b.val = CartanMatrix.E 6 (e a) (e b)) →
      ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L)
        (_ : Algebra.IsSeparable F L)
        (Q : GroupScheme (Spec (CommRingCat.of L))) (_ : IsAffineHom Q.X.hom)
        (_ : LocallyOfFiniteType Q.X.hom) (d : TitsIndexData Q),
          IsSimplyConnected Q ∧ IsAbsolutelyAlmostSimple Q ∧ IsAnisotropic Q ∧
          ∃ n : ℕ, 4 ≤ n ∧ n ≤ 5 ∧ d.HasCartanMatrix (CartanMatrix.D n)

theorem numberFieldTotallyComplexTypeE6CubicSplitTypeDFactor :
    NumberFieldTotallyComplexTypeE6CubicSplitTypeDFactorStatement.{u} := by
  intro F K _ _ hF _ _ _ _ hK G _ _ hAni hsc p e hE
  obtain ⟨L, hL, hAlg, hFinite, hSep, Q, hAff, hFT, d, hscQ, habs, hAniQ, hrank, hA, hF4⟩ :=
    hAni.exists_nonTypeA_nonTypeF4_factor_of_typeE6_cubicSplit hsc hK p e hE
  have : NumberField L := NumberField.of_module_finite F L
  have : IsTotallyComplex F := hF
  exact ⟨L, hL, hAlg, hFinite, hSep, Q, hAff, hFT, d, hscQ, habs, hAniQ,
    d.exists_typeD_of_small_anisotropic_factor (isTotallyComplex_of_algebra F L)
      hscQ habs hAniQ hrank hA hF4⟩

end Langlands.GroupScheme
