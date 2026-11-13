import Langlands.Representation.LanglandsClassification.OppositeStandardExponentParameters

/-! # Restriction of opposite standard exponents to a larger standard Levi

A closed proposition (Renard VII.1.1 with transitivity of parabolic restriction,
as used in the proof of VII.4.2 (iii)), phrased with the full real parameters of
the actual opposite standard Jacquet exponents. No proof is given here.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace

/-- Restriction of actual opposite standard exponents to a larger standard
Levi, in full real parameters (Renard VII.1.1 with transitivity of parabolic
restriction, as used in VII.4.2 (iii)). Let `z` be an exponent on the label
`J ⊆ K`. If `w` annihilates the coroots of `K` and differs from the full real
parameter of `z` by an element of the real span of the roots in `K`, then some
exponent on the label `K` has full real parameter `w`. -/
def OppositeStandardExponentRestrictionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      [Mono i.hom.hom.left] (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)
      (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν),
      IsMinimalParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)) →
      ∀ π : SmoothRep.{0, u, v} ℂ (rationalPoints G), π.IsAdmissible → π.HasFiniteLength →
      ∀ (z : OppositeStandardJacquetFamily.exponents i ν hG hi hν π)
        (K : StandardJacquetFamily.Index i ν) (w : Vstar T),
        z.1.val ⊆ K.val →
        (∀ α : relativeRoots i, α.1 ∈ K.val → pair T w ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0) →
        OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D z - w ∈
          Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K.val) →
        ∃ x : OppositeStandardJacquetFamily.exponents i ν hG hi hν π,
          x.1 = K ∧ OppositeStandardJacquetFamily.fullRealPart i ν hG hi hν π D x = w

end Langlands.Aubert.General.RepresentedParabolic
