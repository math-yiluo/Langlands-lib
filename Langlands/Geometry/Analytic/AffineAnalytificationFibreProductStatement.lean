import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap

/-! # Statement: affine analytification carries pushouts of algebras to fibre products -/

universe u v w x

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory TensorProduct

/-- Statement (affine case of the compatibility of analytification with fibre products,
Berkovich 1993, Proposition 2.6.1, as used in Conrad 2011, printed p.19, for the
Library's polynomial-locus model in its localized category of analytic spaces): for a
complete nonarchimedean nontrivially normed field `K`, a commutative `K`-algebra `C`,
commutative `C`-algebras `A` and `B` whose `K`-algebra structures factor through `C`, and
finite polynomial presentations of `C`, `A`, `B` and `A ⊗[C] B`, the square of
analytifications induced by the four algebra maps `C → A`, `C → B`, `A → A ⊗[C] B`
(`a ↦ a ⊗ 1`) and `B → A ⊗[C] B` (`b ↦ 1 ⊗ b`) is a pullback square in the localized
category: `Spec(A ⊗[C] B)ᵃⁿ` is the fibre product of `Spec(A)ᵃⁿ` and `Spec(B)ᵃⁿ` over
`Spec(C)ᵃⁿ`. -/
def AffineAnalytificationFibreProductStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (C : Type v) [CommRing C] [Algebra K C]
    (A : Type w) [CommRing A] [Algebra K A] [Algebra C A] [IsScalarTower K C A]
    (B : Type x) [CommRing B] [Algebra K B] [Algebra C B] [IsScalarTower K C B]
    (PC : FinitePolynomialPresentation K C) (PA : FinitePolynomialPresentation K A)
    (PB : FinitePolynomialPresentation K B)
    (PT : FinitePolynomialPresentation K (A ⊗[C] B)),
    IsPullback
      (localizedHom K PA PT (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[C] B))
      (localizedHom K PB PT
        ((Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).restrictScalars K))
      (localizedHom K PC PA (IsScalarTower.toAlgHom K C A))
      (localizedHom K PC PB (IsScalarTower.toAlgHom K C B))

end Langlands.Analytic.AffineAnalytification
