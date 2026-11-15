import Langlands.Geometry.Analytic.AffineAnalytificationMap
import Langlands.Geometry.Analytic.DirectedAtlasComposition

/-! # Statement: functoriality of the polynomial-locus affine analytification -/

universe u v w x

namespace Langlands.Analytic.AffineAnalytification

open AffinoidAtlasPresentation

/-- Statement (affine case of the functoriality of analytification, Berkovich 1990, §3.4,
and Conrad–Temkin 2009, Theorem 2.2.3, as used in Conrad 2011, printed p.19): for a
complete nonarchimedean nontrivially normed field `K`, finite polynomial presentations
`P`, `P'` of `A`, `Q` of `B` and `R` of `C`, and `K`-algebra maps `f : A → B` and
`g : B → C`,
1. the strong atlas map induced by the identity of `A` is the identity strong map;
2. the strong atlas map induced by `g ∘ f` is the directed composite of the maps
   induced by `g` and by `f`;
3. the strong atlas maps induced by the identity of `A` between the atlases of the
   presentations `P` and `P'` compose to the identity of the atlas of `P`. -/
def AffineAnalytificationFunctorialityStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A] (B : Type w) [CommRing B] [Algebra K B]
    (C : Type x) [CommRing C] [Algebra K C]
    (P P' : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (R : FinitePolynomialPresentation K C) (f : A →ₐ[K] B) (g : B →ₐ[K] C),
    strongHom K P P (AlgHom.id K A) = StrongHom.id (presentation K P) ∧
    strongHom K P R (g.comp f) =
      StrongHom.compOfDirected (strongHom K Q R g) (strongHom K P Q f)
        (atlas_hasDirectedCharts K Q) (atlas_hasDirectedCharts K P) ∧
    StrongHom.compOfDirected (strongHom K P' P (AlgHom.id K A))
        (strongHom K P P' (AlgHom.id K A))
        (atlas_hasDirectedCharts K P') (atlas_hasDirectedCharts K P) =
      StrongHom.id (presentation K P)

end Langlands.Analytic.AffineAnalytification
