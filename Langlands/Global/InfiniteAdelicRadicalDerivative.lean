import Langlands.Global.InfiniteAdelicAdjointDerivative
import Langlands.Global.InfiniteAdelicRealTrace
import Langlands.GroupScheme.Rational.LeviRadicalTrace

/-! # The derivative of the normalizing factor of a parabolic as a trace on its unipotent radical

For a parabolic `Q = M ⋉ V` of a connected reductive group over a number field and a morphism
`c : H ⟶ M`, the derivative at the identity of `m ↦ δ_Q(c(m))^{-1/2}` along a tangent vector
`X` of `H(F_∞)` is `-1/2 · Σ_v mult(v) · Re (tr_{F_∞} ad(c X) | Lie V ⊗ F_∞)_v`. The trace on
`Lie M` drops out because `M` is reductive. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology AdelicGroupPoints

attribute [local instance] Lie.kernelLieRingOfField Lie.kernelLieAlgebraOfField

/-- The Lie map of a composite is the composite of the Lie maps. -/
theorem targetMapLinear_comp_apply {k : Type u} [Field k] {H M Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom M.X.hom] [IsAffineHom Q.X.hom]
    (A : Type u) [CommRing A] [Algebra k A] (f : H ⟶ M) (g : M ⟶ Q)
    (x : Additive (lieKernel H A)) :
    Lie.targetMapLinear (f ≫ g) A x = Lie.targetMapLinear g A (Lie.targetMapLinear f A x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change x.toMul.val ≫ (f ≫ g).hom.hom = (x.toMul.val ≫ f.hom.hom) ≫ g.hom.hom
  rw [Grp.comp_hom_hom, Category.assoc]

variable (F : Type u) [Field F] [NumberField F] {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] {e : ℕ} (hsmoothH : SmoothOfRelativeDimension e H.X.hom)

/-- The derivative at the identity of the normalizing factor `m ↦ δ_Q(c(m))^{-1/2}` along `X` is
`-1/2 · Σ_v mult(v) · Re (tr_{F_∞} ad(Lie (c ≫ l) (B X)) | Lie V ⊗ F_∞)_v`, where `B X` is
`tangentKernel X` and `ad` on `Lie V` is `Lie.normalAdjoint`. -/
theorem mfderiv_halfModulus_one_eq_radicalTrace {G Q M V : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
    [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
    [IsAffine V.X.left] [LocallyOfFiniteType V.X.hom]
    {q : Q ⟶ G} {iV : V ⟶ Q} {l : M ⟶ Q}
    (hG : IsConnectedReductive G) (hq : IsParabolicSubgroup q)
    (hV : LeviSubgroup.IsGeometricUnipotentRadical iV) (hl : IsRationalLeviSubgroup l)
    [Mono iV.hom.hom] (c : H ⟶ M)
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F H hsmoothH
      GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F H hsmoothH
    mfderiv 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, ℂ)
        (fun m => parameterPower F Q (-halfModulusParameter F Q)
          (map F H Q (c ≫ l) (ofInfinite F H m))) 1 X =
      (-1 / 2 : ℂ) * ((∑ v : InfinitePlace F, (v.mult : ℝ) *
        RCLike.re (LinearMap.trace (InfiniteAdeleRing F) (Additive (lieKernel V (InfiniteAdeleRing F)))
          (Lie.normalAdjoint iV hV.1.isNormal (InfiniteAdeleRing F)
            (Lie.targetMapLinear l (InfiniteAdeleRing F)
              (Lie.targetMapLinear c (InfiniteAdeleRing F)
                (Additive.ofMul (tangentKernel F hsmoothH X))))) v) : ℝ) : ℂ) := by
  rw [mfderiv_halfModulus_one_eq_trace_ad, targetMapLinear_comp_apply,
    Lie.trace_toEnd_levi hG hq hV hl,
    Lie.trace_toEnd_eq_zero_of_isConnectedReductive _ hl.isConnectedReductive, add_zero]

end Langlands.Global.InfiniteAdelicGroupPoints
