/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

import WeilConjectures.AlgebraicGeometry.ProjLineSerreVanishing
import WeilConjectures.AlgebraicGeometry.ProjLineCoordinateShortExact
import WeilConjectures.AlgebraicGeometry.Cohomology.Exact
import WeilConjectures.AlgebraicGeometry.Cohomology.PushforwardZero

/-! # Eventual surjectivity of coordinate multiplication on twisted sections

Source: Stacks Project, Tag 01YS (4), applied to the locally split coordinate sequence.
(blueprint: lem-sc-p1-section-coordinate-surjective).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- In sufficiently high degrees, every section is a sum of coordinate multiples of
sections in the preceding degree. This asserts no finite generation of a section module.

Source: Stacks Project, Lemma 01YS (4), and the standard two-coordinate sequence on P¹;
https://stacks.math.columbia.edu/tag/01YS.
(blueprint: lem-sc-p1-section-coordinate-surjective).

Proof: the coordinate maps give the sequence
0 → O(-1) → O² → O(1) → 0, with maps t ↦ (-x₁t, x₀t) and
(a,b) ↦ x₀a + x₁b. On D₊(x₀), respectively D₊(x₁), the indicated coordinate
is a unit after trivializing the twists, so this sequence is split exact locally.
Tensoring with G ⊗ O(z) therefore remains exact even when G is not locally free.
The kernel is G ⊗ O(z-1), by the twist tensor addition isomorphisms; the last
map is exactly the sum of the two maps G ◁ Proj.twistMul z, as can be checked
on local homogeneous fractions. Identify these Proj twists with projective-line
and projective-space twists using proj_shifted_free_is_twist and uniqueness of
TwistData. Coherence on this noetherian scheme gives quasi-coherence and finite
presentation. Serre vanishing (01YS (4)) applied to G gives a bound b such that
H¹(G ⊗ O(d)) vanishes for d ≥ b. Choose a natural N ≥ max(0,b+1).
For z ≥ N, the long exact sequence identifies the cokernel of coordinate
multiplication on global sections with a subgroup of H¹(G ⊗ O(z-1)) = 0.
Global sections of the two-fold direct sum are pairs of global sections, giving
the two required preimages. For G = 0 both preimages are zero. The bound excludes
the failure at z = -1 for G = O, where constants do not come from O(-1). -/
theorem serreSectionCoordinateSurjective
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toRingedSpace G) :
    ∃ N : ℕ, ∀ (z : ℤ), (N : ℤ) ≤ z →
      ∀ s : Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (z + (1 : ℕ)), ⊤),
      ∃ s₀ s₁ : Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z, ⊤),
        s = Scheme.Modules.Hom.app
            (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (0 : Fin 2)))
            ⊤ s₀ +
          Scheme.Modules.Hom.app
            (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (1 : Fin 2)))
            ⊤ s₁ := by
  obtain ⟨b, hb⟩ := exists_subsingleton_H_one_tensor_proj_twist k G hG
  refine ⟨(b + 1).toNat, ?_⟩
  intro z hz s
  have hvan := hb (z - 1) (by omega)
  obtain ⟨f, h, hseq⟩ := exists_proj_coordinate_shortExact k G z
  let S := ShortComplex.mk f (Limits.biprod.desc
    (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (0 : Fin 2)))
    (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (1 : Fin 2)))) h
  let x := (Scheme.Modules.H.zeroLinearEquiv S.X₃).symm s
  obtain ⟨w, hw⟩ := Abelian.Ext.covariant_sequence_exact₃ _
    (hseq.map_of_exact (Scheme.Modules.toAb _)) x (n₁ := 1) rfl
    (Subsingleton.elim (α := S.X₁.H 1) _ _)
  let t := Scheme.Modules.H.zeroLinearEquiv S.X₂ w
  refine ⟨Scheme.Modules.Hom.app Limits.biprod.fst ⊤ t,
    Scheme.Modules.Hom.app Limits.biprod.snd ⊤ t, ?_⟩
  have hs : Scheme.Modules.Hom.app S.g ⊤ t = s := by
    rw [← Scheme.Modules.H.zeroLinearEquiv_map]
    change Scheme.Modules.H.zeroLinearEquiv S.X₃
      (Scheme.Modules.H.map S.g 0 w) = s
    rw [show Scheme.Modules.H.map S.g 0 w = x from hw]
    exact (Scheme.Modules.H.zeroLinearEquiv S.X₃).apply_symm_apply s
  rw [← hs]
  change Scheme.Modules.Hom.app (Limits.biprod.desc _ _) ⊤ t = _
  rw [Limits.biprod.desc_eq]
  simp
  rfl

end AlgebraicGeometry
