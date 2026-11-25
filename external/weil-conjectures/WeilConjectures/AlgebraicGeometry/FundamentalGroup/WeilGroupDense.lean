/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusElement
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.HomotopyExactSequence

/-!
# The Weil group is dense in the fundamental group

Let `p : C₀ ⟶ Spec K` be a geometrically connected quasi-compact quasi-separated scheme over a
finite field and `G = π₁(C₀, s)`. The geometric Frobenius acts transitively on the geometric fibre
of the constant cover of a finite subfield `L` of `K̄`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_geometricFrobenius_inv_pow_eq`). Consequently a closed
subgroup of `G` containing the projection of the Weil group `W(C₀, s) ⊆ G × ℤ` is everything
(`AlgebraicGeometry.Scheme.FiniteEtale.eq_top_of_forall_mem_weilGroup`): a point of a geometric
fibre fixed by the geometric part comes from a constant cover, on which every element acts as a
power of a Frobenius lift.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of K))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X₀)

/-- **Frobenius is transitive on the constant covers of finite fields.** -/
lemma exists_geometricFrobenius_inv_pow_eq (L : FiniteSubfield K)
    (v w : (fiber s).obj (constantCover p L.toFiniteEtaleAlgebra)) :
    ∃ n : ℕ, ((geometricFrobenius p s L.toFiniteEtaleAlgebra)⁻¹ ^ n) v = w := by
  let A := L.toFiniteEtaleAlgebra
  have : FiniteDimensional K L.1 := L.2
  have : Finite L.1 := Module.finite_of_finite K
  have : Fintype K := Fintype.ofFinite K
  let _ : Algebra K Ω := (baseRingHom p s).toAlgebra
  let e := fiberConstantCoverEquiv p s A
  let toAlg (y : (fiber s).obj (constantCover p A)) : L.1 →ₐ[K] Ω :=
    { (e y).1 with commutes' := fun k ↦ RingHom.congr_fun (e y).2 k }
  have htoAlg : Function.Injective toAlg := fun y y' h ↦
    e.injective (Subtype.ext (RingHom.ext fun a ↦ DFunLike.congr_fun h a))
  let d := Module.finrank K L.1
  let f : Fin d → (fiber s).obj (constantCover p A) :=
    fun n ↦ ((geometricFrobenius p s A)⁻¹ ^ n.1) v
  have hpow (n : ℕ) (a : L.1) :
      toAlg (((geometricFrobenius p s A)⁻¹ ^ n) v) a = toAlg v a ^ (Nat.card K ^ n) :=
    fiberConstantCoverEquiv_geometricFrobenius_inv_pow p s A n v a
  have hf : Function.Injective f := by
    intro n m h
    apply (FiniteField.bijective_frobeniusAlgHom_pow K L.1).1
    refine DFunLike.ext _ _ fun a ↦ (toAlg v).toRingHom.injective ?_
    have h1 := hpow n.1 a
    have h2 := hpow m.1 a
    change toAlg (f n) a = _ at h1
    change toAlg (f m) a = _ at h2
    rw [h] at h1
    change (toAlg v) ((FiniteField.frobeniusAlgHom K L.1 ^ n.1) a) =
      (toAlg v) ((FiniteField.frobeniusAlgHom K L.1 ^ m.1) a)
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, map_pow]
    rw [← Nat.card_eq_fintype_card, ← h1.symm.trans h2]
  have hcard : Nat.card ((fiber s).obj (constantCover p A)) ≤ Nat.card (Fin d) := by
    rw [Nat.card_fin]
    calc Nat.card ((fiber s).obj (constantCover p A)) ≤ Nat.card (L.1 →ₐ[K] Ω) :=
          Nat.card_le_card_of_injective _ htoAlg
      _ ≤ d := card_algHom_le_finrank K L.1 Ω
  obtain ⟨n, hn⟩ := (hf.bijective_of_nat_card_le hcard).2 w
  exact ⟨n.1, hn⟩

section Dense

variable {C : Scheme.{u}} (q : C ⟶ Spec (.of K)) [GeometricallyConnected q] [LocallyOfFiniteType q]
  [QuasiCompact q] [CompactSpace C]
  [QuasiSeparatedSpace C] [ConnectedSpace C] {t : Spec (.of (AlgebraicClosure K)) ⟶ C}
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber t).obj P)] [IsFundamentalGroup (fiber t) G]

/-- **The Weil group is dense in the fundamental group.** A closed subgroup of `π₁(C₀, t)`
containing the projection of the Weil group `W(C₀, t)` is everything. -/
theorem eq_top_of_forall_mem_weilGroup (H : Subgroup G) (hH : IsClosed (H : Set G))
    (hW : ∀ w ∈ weilGroup q t G, w.1 ∈ H) : H = ⊤ := by
  have : ConnectedSpace q.geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := q)
      (Scheme.specAlgebraicClosure K).hom q.geometricFiberProj
      q.geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)
  have : Nonempty q.geometricFiber := inferInstance
  obtain ⟨t', ht'⟩ := q.geometricFiberToAlgebraicClosure.exists_comp_eq_id_of_isAlgClosed
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup t'
  let τ : pullback q.geometricFiberProj ⋙ fiber t' ≅ fiber t :=
    pullbackFiberIso q.geometricFiberProj t' ≪≫
      (nonempty_iso_of_fiberFunctor (fiber (t' ≫ q.geometricFiberProj)) (fiber t)).some
  obtain ⟨γ, hγ⟩ := exists_mem_weilGroup_snd_eq_one q t G
  have hγH : γ ∈ H := hW _ hγ
  refine eq_top_iff.2 fun g _ ↦ mem_of_forall_smul_eq_self t G H hH g fun U u hu ↦ ?_
  have hu' : ∀ k ∈ (fundamentalGroupMap τ G' G).range, k • u = u := by
    rintro _ ⟨k, rfl⟩
    exact hu _ (hW _ (mem_weilGroup_fundamentalGroupMap q ht' τ G G' k))
  obtain ⟨L, ψ, v, rfl⟩ := exists_constantCover_fiber_map_eq q τ G' G U u hu'
  obtain ⟨n, hn⟩ := exists_geometricFrobenius_inv_pow_eq q t L v (g • v)
  -- the Frobenius lift `γ` acts on the constant covers as the geometric Frobenius
  have hγinv (y : (fiber t).obj (constantCover q L.toFiniteEtaleAlgebra)) :
      γ⁻¹ • y = (geometricFrobenius q t _)⁻¹ y := by
    rw [inv_smul_eq_iff, (mem_weilGroup_iff q t G).1 hγ, toAdd_ofAdd, zpow_one]
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  have hpow (m : ℕ) (y : (fiber t).obj (constantCover q L.toFiniteEtaleAlgebra)) :
      γ⁻¹ ^ m • y = ((geometricFrobenius q t _)⁻¹ ^ m) y := by
    induction m generalizing y with
    | zero => rw [pow_zero, one_smul, pow_zero, Equiv.Perm.one_apply]
    | succ m ih => rw [pow_succ, mul_smul, hγinv, ih, pow_succ, Equiv.Perm.mul_apply]
  rw [← IsNaturalSMul.naturality, ← hn, ← hpow, IsNaturalSMul.naturality]
  exact hu _ (H.pow_mem (H.inv_mem hγH) n)

end Dense

end AlgebraicGeometry.Scheme.FiniteEtale
