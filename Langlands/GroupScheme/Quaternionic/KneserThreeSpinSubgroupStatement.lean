import Langlands.GroupScheme.Quaternionic.SpinKernelAssembly
import Langlands.GroupScheme.Quaternionic.BinaryQuaternionSpinLift

/-!
# A simply connected subgroup through the binary quaternionic group (Kneser's `A₃ = D₃`)

For a hyperbolic pair `h` of a quaternionic quadratic form `q`, the binary group
`SL₂ × SL₁(D)` acts on the hyperbolic plane of `h` and trivially on its orthogonal
complement (`AmbientBinaryScheme.isometryHom`). `KneserThreeSpinSubgroupStatement` asserts, in
the setting of `LocalSpinKneserTitsStatement`, that this action factors through a simply
connected group `C` in whose rational points the image of `(-1, -1)` is elementary. The
statement assumes that the characteristic of `K` is not `2`; in characteristic `2` the point
`(-1, -1)` is the identity.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

/-- **Kneser's `A₃ = D₃` subgroup.** Let `K` be a nonarchimedean local field of characteristic
different from `2`, `D` a quaternion division algebra over `K` with orthogonal involution `σ`,
and `q` a nondegenerate quadratic form of rank `m ∈ {4, 5}` and Witt index one. For every hyperbolic pair `h = (e, f)` of `q` there are
a simply connected group `C` over `K`, a homomorphism `c : C ⟶ O(q)` and a homomorphism
`j : SL₂ × SL₁(D) ⟶ C` such that `j ≫ c` is the action of the binary group on the hyperbolic
plane of `h` (`AmbientBinaryScheme.isometryHom`), and the rational point
`j(diag(-1, -1), 1) · j(1, -1) = j(-1, -1)` of `C` lies in `C(K)⁺`.

The rational point is written as `kernelPoint` of the pair
`(upperCocharacter ≫ firstFactor ≫ j, secondFactor ≫ j)` at `-1 ∈ μ₂(K)`. The instance
argument `[Infinite K]`, needed by `AmbientBinaryScheme.isometryHom`, holds for every
nonarchimedean local field. -/
def KneserThreeSpinSubgroupStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Infinite K], (2 : K) ≠ 0 →
    ∀ (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] (hD : Module.finrank K D = 4),
    ∀ (σ : FirstKindInvolution K D) (hsym : Module.finrank K σ.symmetricSubspace = 3),
    ∀ m : ℕ, (m = 4 ∨ m = 5) →
    ∀ q : σ.QuadraticForms (Fin m), σ.IsNondegenerateQuadratic q →
      σ.quadraticWittIndex q = 1 →
      ∀ (e f : Fin m → D) (h : σ.IsHyperbolicPair q e f),
        ∃ (C : GroupScheme (Spec (CommRingCat.of K))) (c : C ⟶ σ.isometryGroup q)
          (j : BinaryScheme.groupScheme (K := K) (D := D) ⟶ C),
          IsSimplyConnected C ∧
          j ≫ c = AmbientBinaryScheme.isometryHom σ hD hsym h ∧
          (GaloisPointComparison.rationalCoeffEquiv K C).symm
              (kernelPoint (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hD)
                (SpecialLinear.BinaryRoot.upperCocharacter (CommRingCat.of K) ≫
                  BinarySpinLift.firstFactor ≫ j)
                (BinarySpinLift.secondFactor ≫ j) _ negOneRoot) ∈
            parabolicElementarySubgroup C

end Langlands.GroupScheme.Quaternionic.SpinKernel
