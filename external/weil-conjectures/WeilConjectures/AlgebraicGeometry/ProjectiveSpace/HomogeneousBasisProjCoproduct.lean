/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

import WeilConjectures.AlgebraicGeometry.ProjFiniteTwistCoproductFractions
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.HomogeneousBasisCoordinates
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.GradedChartComparison

/-!
# Associated sheaves of homogeneous bases on polynomial Proj

## References

* Stacks Project, Constructions, Definitions 01M6, 01MN and Lemma 01M7
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous basis identifies its associated sheaf with the coproduct of Proj twists. -/
theorem homogeneous_basis_proj_coproduct (k : Type u) [Field k]
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (F : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f M)
    (halpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (alpha f d hd hf) ∧
        Set.range (alpha f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f))
    (hscalar : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        alpha f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
          algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (Localization.Away f) r • alpha f d hd hf s)
    (hres : ∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
        (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
          basicOpen (homogeneousSubmodule (Fin 2) k) f)
        (e c : ℕ) (a : MvPolynomial (Fin 2) k),
        0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
        ∀ (m : ℕ) (y : M)
          (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
          alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha g b hb hg (F.val.map (homOfLE inc).op s) =
            mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (r : ℕ) (d : Fin r → ℤ)
    (b : Module.Basis (Fin r) (MvPolynomial (Fin 2) k) M)
    (hb : ∀ a : Fin r, b a ∈ 𝓜 (-(d a))) :
    Nonempty (F ≅ ∐ (fun a ↦ twist (homogeneousSubmodule (Fin 2) k) (d a))) := by
  classical
  obtain ⟨beta, hbeta, hbetaScalar, hbetaRes⟩ :=
    finite_twist_coproduct_fractions (homogeneousSubmodule (Fin 2) k) r d
  have hdegree (n : ℕ) (y : M) : y ∈ 𝓜 n ↔
      ∀ a, if 0 ≤ d a + n then
        b.equivFun y a ∈ homogeneousSubmodule (Fin 2) k (d a + n).toNat
      else b.equivFun y a = 0 := by
    constructor
    · exact homogeneous_basis_coordinates k M 𝓜 h𝓜 hsmul r d b hb n y
    · intro hy
      rw [← b.sum_equivFun y]
      apply (𝓜 n).sum_mem
      intro a _
      by_cases ha : 0 ≤ d a + n
      · have hc := hsmul (d a + n).toNat (-(d a)) (b.equivFun y a) (b a)
          (by simpa [ha] using hy a) (hb a)
        have hn : ((d a + n).toNat : ℤ) + -(d a) = n := by
          rw [Int.toNat_of_nonneg ha]
          omega
        simpa only [hn] using hc
      · have hzero : b.equivFun y a = 0 := by simpa [ha] using hy a
        rw [hzero, zero_smul]
        exact (𝓜 n).zero_mem
  exact graded_chart_comparison k M
    (ModuleCat.of (MvPolynomial (Fin 2) k) (Fin r → MvPolynomial (Fin 2) k))
    (fun n ↦ (𝓜 n : Set M))
    (fun n ↦ {y | ∀ a, if 0 ≤ d a + n then
      y a ∈ homogeneousSubmodule (Fin 2) k (d a + n).toNat else y a = 0})
    b.equivFun hdegree F _ alpha halpha hscalar hres beta hbeta hbetaScalar hbetaRes

end AlgebraicGeometry.Proj
