/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.ClosedLift
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale

/-!
# Lifting a covering of a closed fibre

Let `W = Spec B` be affine and `Z_W = V(J) ⊆ W` a closed subscheme whose complement is
quasi-compact. A finite covering of `Z_W` by affine ind-étale `V_a = Spec C̄_a` extends to a finite
pro-étale covering of `W`: its members over the closed fibre are the lifts
`v_W(V_a) = Spec H_B(C̄_a)` of `Algebra.ClosedLift`, which reduce to `V_a`, and its other members
are basic opens `D(f_b)`, `f_b ∈ J`, of `W ∖ Z_W`, which reduce to the empty scheme
(`AlgebraicGeometry.exists_ofArrows_closedLiftCover_mem_proetalePrecoverage`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {B : Type u} [CommRing B] (J : Ideal B) {ι κ : Type u}
  (C : ι → Type u) [∀ a, CommRing (C a)] [∀ a, Algebra B (C a)] (f : κ → B)

/-- The members of the extended covering of `Spec B`: the lifts `Spec H_B(C̄_a)` of the members
`Spec C̄_a` of a covering of the closed fibre, and the basic opens `Spec B_{f_b}`. -/
noncomputable def closedLiftCoverObj : ι ⊕ κ → Scheme.{u} :=
  Sum.elim (fun a ↦ Spec (.of (Algebra.ClosedLift B (C a))))
    (fun b ↦ Spec (.of (Localization.Away (f b))))

/-- The structure morphisms of the members of the extended covering of `Spec B`. -/
noncomputable def closedLiftCoverHom :
    ∀ k, closedLiftCoverObj C f k ⟶ Spec (.of B)
  | .inl a => Spec.map (CommRingCat.ofHom (algebraMap B (Algebra.ClosedLift B (C a))))
  | .inr b => Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (f b))))

variable [∀ a, Algebra (B ⧸ J) (C a)] [∀ a, IsScalarTower B (B ⧸ J) (C a)]

/-- Let `W = Spec B` be affine and `Z_W = V(J)` closed with quasi-compact complement. A finite
covering of `Z_W` by affine ind-étale `Spec C̄_a` extends to a finite pro-étale covering of `W`
whose members over the closed fibre are the lifts `v_W(Spec C̄_a) = Spec H_B(C̄_a)`
(`Algebra.ClosedLift`), and whose other members are basic opens `D(f_b)`, `f_b ∈ J`, covering
`W ∖ Z_W`. Their reductions to `Z_W` are respectively `Spec C̄_a`
(`Algebra.ClosedLift.bijective_reduction`) and empty. -/
theorem exists_ofArrows_closedLiftCover_mem_proetalePrecoverage
    (hJ : IsCompact (PrimeSpectrum.zeroLocus (J : Set B))ᶜ) [Finite ι]
    [∀ a, Algebra.IndEtale (B ⧸ J) (C a)]
    (hC : ∀ p : PrimeSpectrum (B ⧸ J), ∃ a,
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap (B ⧸ J) (C a)))) :
    ∃ (κ : Type u) (_ : Finite κ) (f : κ → B), (∀ b, f b ∈ J) ∧
      (⋃ b, (PrimeSpectrum.basicOpen (f b) : Set (PrimeSpectrum B))) =
        (PrimeSpectrum.zeroLocus (J : Set B))ᶜ ∧
      Presieve.ofArrows _ (closedLiftCoverHom C f) ∈ Scheme.proetalePrecoverage (Spec (.of B)) ∧
      (∀ a, Function.Bijective (Algebra.ClosedLift.reduction B (C a) J)) ∧
      ∀ b, Subsingleton
        (Localization.Away (f b) ⧸ J.map (algebraMap B (Localization.Away (f b)))) := by
  classical
  -- finitely many `f_b ∈ J` cover the complement of `V(J)`
  have hcov : (PrimeSpectrum.zeroLocus (J : Set B))ᶜ ⊆
      ⋃ x : J, (PrimeSpectrum.basicOpen (x : B) : Set (PrimeSpectrum B)) := by
    intro p hp
    simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Set.not_subset] at hp
    obtain ⟨x, hxJ, hxp⟩ := hp
    exact Set.mem_iUnion.2 ⟨⟨x, hxJ⟩, hxp⟩
  obtain ⟨t, ht⟩ := hJ.elim_finite_subcover
    (fun x : J ↦ (PrimeSpectrum.basicOpen (x : B) : Set (PrimeSpectrum B)))
    (fun x ↦ (PrimeSpectrum.basicOpen _).isOpen) hcov
  let f : t → B := fun b ↦ b.1.1
  have hU : (⋃ b, (PrimeSpectrum.basicOpen (f b) : Set (PrimeSpectrum B))) =
      (PrimeSpectrum.zeroLocus (J : Set B))ᶜ := by
    refine subset_antisymm (Set.iUnion_subset fun b p hp hJp ↦ hp (hJp b.1.2)) fun p hp ↦ ?_
    obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.1 (ht hp)
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hpx⟩
  have hsurj : ∀ x : PrimeSpectrum B, ∃ k, x ∈ Set.range (closedLiftCoverHom C f k).base := by
    intro x
    by_cases hx : x ∈ PrimeSpectrum.zeroLocus (J : Set B)
    · have hx' : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
        rw [range_comap_of_surjective (B ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective,
          Ideal.mk_ker]
        exact hx
      obtain ⟨p, rfl⟩ := hx'
      obtain ⟨a, q, rfl⟩ := hC p
      refine ⟨.inl a,
        PrimeSpectrum.comap (Algebra.ClosedLift.toAlgHom B (C a) : _ →+* C a) q, ?_⟩
      change PrimeSpectrum.comap (algebraMap B (Algebra.ClosedLift B (C a)))
        (PrimeSpectrum.comap (Algebra.ClosedLift.toAlgHom B (C a) : _ →+* C a) q) = _
      rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
      congr 1
      ext b
      simp [IsScalarTower.algebraMap_apply B (B ⧸ J) (C a), Ideal.Quotient.algebraMap_eq]
    · replace hx : x ∈ (PrimeSpectrum.zeroLocus (J : Set B))ᶜ := hx
      rw [← hU] at hx
      obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hx
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (f b))] at hb
      obtain ⟨y, rfl⟩ := hb
      exact ⟨.inr b, y, rfl⟩
  let D : PreZeroHypercover (Spec (.of B)) :=
    ⟨ι ⊕ t, closedLiftCoverObj C f, closedLiftCoverHom C f⟩
  have : ∀ k, QuasiCompact (D.f k) := by
    rintro (a | b) <;> dsimp [D, closedLiftCoverHom, closedLiftCoverObj] <;> infer_instance
  have hD : QuasiCompactCover D :=
    ⟨fun {U} hU ↦ IsCompactOpenCovered.of_finite_of_isSpectralMap
      (fun k ↦ (D.f k).isSpectralMap) (fun x _ ↦ hsurj x) U.2 hU.isCompact⟩
  refine ⟨t, inferInstance, f, fun b ↦ b.1.2, hU, ?_,
    fun a ↦ Algebra.ClosedLift.bijective_reduction B (C a) J, fun b ↦ ?_⟩
  · refine ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hD,
      (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).2 ⟨hsurj, ?_⟩⟩
    rintro (a | b) <;> dsimp [closedLiftCoverHom, closedLiftCoverObj] <;> infer_instance
  · rw [Ideal.Quotient.subsingleton_iff]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ b.1.2)
      (IsLocalization.Away.algebraMap_isUnit _)


end AlgebraicGeometry
