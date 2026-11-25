/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.ProjPolynomialTwistChart
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
import WeilConjectures.AlgebraicGeometry.ProjHomogeneousSectionTensorPowersData
import WeilConjectures.AlgebraicGeometry.ProjHomogeneousSectionTensorPowersLocus

/-! # Tensor powers of a homogeneous section of a polynomial Proj twist

Source: Stacks Project, Constructions, Tags 01MS, 01MU, 01MV and 01NG.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Tensor-power identifications for `O(d)` respect multiplication by any homogeneous
polynomial, and its nonvanishing locus is its standard open.

Source: Stacks Project, Constructions, Tags 01MS, 01MU, 01MV and 01NG.
(blueprint: lem-sc-p1-homogeneous-section-tensor-powers).

Proof: On each coordinate chart D_+(x_i), O(m) is free on x_i^m for every integer m.
Multiplication of fractions gives O(m) tensor O(n) -> O(m+n), carrying the tensor
of these bases to the corresponding basis. These maps agree on intersections and
are isomorphisms. Iterate them to construct the displayed identifications, starting
with O = O(0). The homogeneous section f is (f/x_i^d) x_i^d on that chart. Its tensor
power therefore has coefficient (f/x_i^d)^n, which gives exactly f^n under both
identifications. This proves the two morphism identities, including n=0. The fibre
value of f is nonzero exactly where f/x_i^d is outside the prime ideal; this is
D_+(f) intersected with the chart. Since the charts cover, the locus equality follows.
Invertibility follows from the same local bases. For f=0 the locus is empty and the
positive powers are zero; the zeroth identities are still the unit identities.
-/
theorem proj_homogeneous_section_tensor_powers (k : Type u) [Field k]
    {d : ℕ} (hd : 0 < d) {f : MvPolynomial (Fin 2) k}
    (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k d) :
    let L := Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (0 + (d : ℤ))
    L.IsInvertible ∧
      ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) f :
        (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Opens) : Set _) =
        nonvanishingLocus L ((Proj.unitToTwist hf).app ⊤
          (unitSectionsEquiv ⊤ 1)) ∧
      ∃ (a : ∀ n : ℕ, L.tensorPow n ≅
          Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
            (0 + ((n • d : ℕ) : ℤ)))
        (b : ∀ (m : ℤ) (n : ℕ),
          Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ⊗ L.tensorPow n ≅
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
              (m + ((n • d : ℕ) : ℤ))),
        (∀ n : ℕ, tensorPowSection
            (homOfGlobalSection L ((Proj.unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)))
            n ≫ (a n).hom =
          Proj.unitToTwist (SetLike.pow_mem_graded n hf)) ∧
        (∀ (m : ℤ) (n : ℕ),
          (ρ_ (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m)).inv ≫
            Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) m ◁
              tensorPowSection
                (homOfGlobalSection L ((Proj.unitToTwist hf).app ⊤ (unitSectionsEquiv ⊤ 1)))
                n ≫ (b m n).hom =
            Proj.twistMul m (SetLike.pow_mem_graded n hf)) := by
  dsimp
  have hL := Proj.isInvertible_twist
    (MvPolynomial.homogeneousSubmodule (Fin 2) k) (0 + (d : ℤ)) (by
      intro x
      have hx : x ∈ ⨆ i : Fin 2,
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k) (MvPolynomial.X i) := by
        rw [(proj_polynomial_twist_chart k 1).1]
        trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨_, MvPolynomial.isHomogeneous_X k i, hi⟩)
  obtain ⟨ha, hb, h₁, h₂⟩ := proj_homogeneous_section_tensor_powers_data k hd hf
  have hl := proj_homogeneous_section_tensor_powers_locus k hd hf
  exact ⟨hL, hl, ⟨ha, hb, h₁, h₂⟩⟩

end AlgebraicGeometry
