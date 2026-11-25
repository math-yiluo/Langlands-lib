/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.DirectSum.Module
import WeilConjectures.AlgebraicGeometry.SerreSectionModuleAction

/-! # SerreSectionModuleConstruction

Intermediate step for finite generation of graded sections. -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The nonnegative twisted sections carry their canonical internally graded polynomial action.
No coherence or finiteness is asserted.

Source: Stacks Project, Section 30.14, the graded module in Lemma 01YS(5), and Lemma
0AG6(4); https://stacks.math.columbia.edu/tag/01YS.
(blueprint: lem-sc-p1-section-module-construction).
Proof: take the additive direct sum of the groups Γ(G ⊗ O(n), P), indexed by n ≥ 0.
A homogeneous polynomial a of degree e sends the n-th summand to the (n+e)-th by
G ◁ Proj.twistMul n a. Define the action of an arbitrary polynomial by adding the actions
of its finitely many homogeneous components. Locally, twistMul is multiplication of
fractions, so it is additive in a, sends 1 to the identity, and its composites are
multiplication by the product, after the degree equalities are transported. These facts
prove the module laws. The summand images give the internal integer grading; put zero
in negative degrees. The inverse of each summand inclusion gives φ. Its definition and
the homogeneous action give the asserted compatibility, including degree zero. -/
theorem serreSectionModuleConstruction
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
 :
    ∃ (M : ModuleCat.{u} (MvPolynomial (Fin 2) k)),
    ∃ (𝓜 : ℤ → AddSubgroup M), DirectSum.IsInternal 𝓜 ∧
      (∀ (e : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
        a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k e → y ∈ 𝓜 z → a • y ∈ 𝓜 (e + z)) ∧
      (∀ z : ℤ, z < 0 → 𝓜 z = ⊥) ∧
    ∃ (φ : ∀ z : ℤ, 0 ≤ z →
        (𝓜 z ≃+ Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z, ⊤))),
      ∀ (z : ℤ) (hz : 0 ≤ z) (e : ℕ) (hze : 0 ≤ z + e) (a : MvPolynomial (Fin 2) k)
        (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k e)
        (y : 𝓜 z) (hay : a • (y : M) ∈ 𝓜 (z + e)),
        φ (z + e) hze ⟨a • (y : M), hay⟩ =
          Scheme.Modules.Hom.app (G ◁ Proj.twistMul z ha) ⊤ (φ z hz y) := by
  classical
  let B := serreSectionPiece k G
  let M := ModuleCat.of (MvPolynomial (Fin 2) k)
    (serreSectionSum k G)
  let 𝓜 : ℤ → AddSubgroup M := fun z ↦ (DirectSum.of B z).range
  let E (z : ℤ) : B z ≃+ 𝓜 z :=
    AddMonoidHom.ofLeftInverse (f := DirectSum.of B z)
      (g := { toFun := fun x ↦ x z, map_zero' := rfl, map_add' := fun _ _ ↦ rfl })
      (fun _ ↦ DirectSum.of_eq_same _ _)
  have h𝓜 : DirectSum.IsInternal 𝓜 := by
    let F := DFinsupp.mapRange.addEquiv (fun z ↦ (E z).symm)
    have hF : DirectSum.coeAddMonoidHom 𝓜 = F.toAddMonoidHom := by
      apply DirectSum.addHom_ext
      intro z y
      simp only [DirectSum.coeAddMonoidHom_of]
      change (y : M) = DFinsupp.mapRange (fun i x ↦ (E i).symm x)
        (fun i ↦ map_zero ((E i).symm)) (DirectSum.of (fun i ↦ 𝓜 i) z y)
      change (y : M) = DFinsupp.mapRange (fun i x ↦ (E i).symm x)
        (fun i ↦ map_zero ((E i).symm)) (DFinsupp.single z y)
      rw [DFinsupp.mapRange_single]
      exact (congrArg Subtype.val ((E z).apply_symm_apply y)).symm
    rw [DirectSum.IsInternal, hF]
    exact F.bijective
  have hneg : ∀ z : ℤ, z < 0 → 𝓜 z = ⊥ := by
    intro z hz
    apply le_antisymm ?_ bot_le
    rintro y ⟨s, rfl⟩
    have hs : s = 0 := by
      funext h
      have hh := h.down
      exact False.elim (by omega : False)
    simp [hs]
  have hsmul : ∀ (e : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k e → y ∈ 𝓜 z →
        a • y ∈ 𝓜 (e + z) := by
    intro e z a y ha hy
    obtain ⟨s, rfl⟩ := hy
    rw [(serreSectionActionLaws k G).2.2.2.2 e z a ha s]
    simpa only [add_comm] using
      (show DirectSum.of B (z + e) (serreSectionHomogeneous k G e z ⟨a, ha⟩ s) ∈
        𝓜 (z + e) from ⟨_, rfl⟩)
  let φ (z : ℤ) (hz : 0 ≤ z) :
      𝓜 z ≃+ Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z, ⊤) :=
    (E z).symm.trans
      { toFun := fun s ↦ s ⟨hz⟩
        invFun := fun s _ ↦ s
        left_inv := fun s ↦ by funext h; congr
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl }
  refine ⟨M, 𝓜, h𝓜, hsmul, hneg, φ, ?_⟩
  intro z hz e hze a ha y hay
  have hy : (y : M) = DirectSum.of B z ((E z).symm y) :=
    (congrArg Subtype.val ((E z).apply_symm_apply y)).symm
  have hmul : a • (y : M) = DirectSum.of B (z + e)
      (serreSectionHomogeneous k G e z ⟨a, ha⟩ ((E z).symm y)) := by
    rw [hy]
    exact (serreSectionActionLaws k G).2.2.2.2 e z a ha _
  have heq : (⟨a • (y : M), hay⟩ : 𝓜 (z + e)) =
      E (z + e) (serreSectionHomogeneous k G e z ⟨a, ha⟩ ((E z).symm y)) := by
    apply Subtype.ext
    exact hmul
  rw [heq]
  simp [φ, serreSectionHomogeneous, hz]

end AlgebraicGeometry
