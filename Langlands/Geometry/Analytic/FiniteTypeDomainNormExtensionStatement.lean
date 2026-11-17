import Langlands.Geometry.Analytic.AffineAnalytificationSeminorm

/-! # Statement: the norm of a complete ultrametric field extends to every finitely generated domain -/

universe u v

namespace Langlands.Analytic.AffineAnalytification

/-- Statement (Berkovich 1990, Theorem 3.4.1(i) with Remark 3.4.2, applied at the generic
point of `Spec D`; Temkin, *Valued Fields*, Exercise 1.2.13 and Theorem 1.7.7): for a
complete nonarchimedean nontrivially normed field `K` and a finitely generated
commutative `K`-algebra `D` that is a domain, some multiplicative seminorm `ν` on `D`
extends the norm of `K` and vanishes only at `0`; that is, `ν` is a multiplicative norm
on `D` extending the norm of `K`. -/
def FiniteTypeDomainNormExtensionStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (D : Type v) [CommRing D] [IsDomain D] [Algebra K D] [Algebra.FiniteType K D],
    ∃ ν : MulRingSeminorm D, ExtendsNorm K ν ∧ ∀ a : D, ν a = 0 → a = 0

end Langlands.Analytic.AffineAnalytification
