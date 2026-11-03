import Langlands.GroupScheme.Rational.CoordinateCotangent

/-! # Actual cotangent and Lie-kernel comparison targets -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

/-- The original actual Lie kernel is dual to the original augmentation quotient,
with its value fixed by the existing actual coordinate derivation comparison. -/
def KernelCotangentDualityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hAff : IsAffineHom G.X.hom),
    letI := hAff
    ∀ (A : Type u) [CommRing A] [Algebra k A],
      ∃ e : Additive (lieKernel G A) ≃ₗ[A] (Cotangent G →ₗ[k] A),
        ∀ (X : Additive (lieKernel G A)) (f : augmentation G),
          e X (cotangentMk G f) = Lie.kernelDerivationEquiv G X.toMul f.val

/-- The actual action on Lie kernels is transpose to coordinate pullback on the
base-changed augmentation quotient, without an inverse character. -/
def CotangentActionPairingStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hAff : IsAffineHom G.X.hom),
    letI := hAff
    ∀ (A : Type u) [CommRing A] [Algebra k A],
      ∃ e : Additive (lieKernel G A) ≃ₗ[A] Module.Dual A (BaseCotangent G A),
        (∀ (X : Additive (lieKernel G A)) (f : augmentation G),
          e X (cotangentBaseChange (cotangentMk G f)) =
            Lie.kernelDerivationEquiv G X.toMul f.val) ∧
        (∀ (S : CommGroupScheme (Spec (CommRingCat.of k)))
          (b : AutomorphicAction S.toGrp G) (s : Lie.AffinePoints S.toGrp A)
          (X : Additive (lieKernel G A)),
          ∃ Y : Additive (lieKernel G A),
            Y.toMul.val = b.act (Lie.constant S.toGrp s) X.toMul.val ∧
            ∀ q : BaseCotangent G A, e Y q = e X (cotangentAction b s q))

/-- Under splitness, the actual cotangent support has exactly the labels of the
existing intrinsic actionWeightSupport on the actual Lie kernel. -/
def CotangentLieSupportStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hAff : IsAffineHom G.X.hom) (_hft : LocallyOfFiniteType G.X.hom)
    (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ b : AutomorphicAction S.toGrp G,
    letI := hAff
    cotangentSupport b = RelativeRoot.actionWeightSupport b ⊤

/-- Exact remaining kernel duality, actual-action pairing and support comparison. -/
def CoordinateLieComparisonStatement : Prop :=
  KernelCotangentDualityStatement.{u} ∧ CotangentActionPairingStatement.{u} ∧
    CotangentLieSupportStatement.{u}

end Langlands.GroupScheme.CoordinateWeights
