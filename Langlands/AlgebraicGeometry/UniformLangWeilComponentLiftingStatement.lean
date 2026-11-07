import Langlands.AlgebraicGeometry.UniformLangWeilStatement
import Langlands.AlgebraicGeometry.PointTopology.HenselianSmoothPointLifting

/-! # Uniform lifting without a prescribed common fibre dimension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- One bound works for every finite-field point of a smooth geometrically
connected finite-type family, allowing different dimensions on its components. -/
def UniformLangWeilComponentFiniteFieldLiftingStatement : Prop :=
  UniformLangWeilStatement.{u} →
    ∀ (B Y : Scheme.{u}) (f : Y ⟶ B),
      LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B) → CompactSpace B →
      Smooth f → IsSeparated f → QuasiCompact f → GeometricallyConnected f →
      ∃ C : ℝ, 0 < C ∧
        ∀ (K : Type u) [Field K] [Finite K]
          (p : Spec (CommRingCat.of K) ⟶ B),
          C ^ 2 < (Nat.card K : ℝ) →
          ∃ q : Spec (CommRingCat.of K) ⟶ Y, q ≫ f = p

/-- The bound also controls lifts of points over Henselian local rings with a
large finite-field quotient, independently of any common fibre dimension. -/
def UniformLangWeilComponentHenselianLiftingStatement : Prop :=
  UniformLangWeilStatement.{u} →
    ∀ (B Y : Scheme.{u}) (f : Y ⟶ B),
      LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B) → CompactSpace B →
      Smooth f → IsSeparated f → QuasiCompact f → GeometricallyConnected f →
      ∃ C : ℝ, 0 < C ∧
        ∀ (R : Type u) [CommRing R] [HenselianLocalRing R]
          (K : Type u) [Field K] [Finite K] [Algebra R K],
          Function.Surjective (algebraMap R K) → C ^ 2 < (Nat.card K : ℝ) →
          ∀ p : Spec (CommRingCat.of R) ⟶ B,
            ∃ q : Spec (CommRingCat.of R) ⟶ Y, q ≫ f = p

/-- The Henselian conclusion retains points over an arbitrary original
coefficient ring, with the lift an actual morphism in its over-category. -/
def UniformLangWeilComponentRingPointLiftingStatement : Prop :=
  UniformLangWeilStatement.{u} →
    ∀ (A : Type u) [CommRing A] (B Y : Over (Spec (CommRingCat.of A)))
      (f : Y ⟶ B),
      LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B.left) →
      CompactSpace B.left → Smooth f.left → IsSeparated f.left →
      QuasiCompact f.left → GeometricallyConnected f.left →
      ∃ C : ℝ, 0 < C ∧
        ∀ (R : Type u) [CommRing R] [HenselianLocalRing R] [Algebra A R]
          (K : Type u) [Field K] [Finite K] [Algebra A K]
          (φ : R →ₐ[A] K),
          Function.Surjective φ → C ^ 2 < (Nat.card K : ℝ) →
          ∀ p : PointTopology.RingPoint A B R,
            ∃ q : PointTopology.RingPoint A Y R, q ≫ f = p

/-- The finite-field, Henselian and original-coefficient lifting consequences
of uniform Lang-Weil, with no supplied common fibre dimension. -/
def UniformLangWeilComponentLiftingStatement : Prop :=
  UniformLangWeilComponentFiniteFieldLiftingStatement.{u} ∧
    UniformLangWeilComponentHenselianLiftingStatement.{u} ∧
    UniformLangWeilComponentRingPointLiftingStatement.{u}

end Langlands.AlgebraicGeometry
