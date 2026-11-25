/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.Infinite
import WeilConjectures.FieldTheory.OpenSubgroupFixedField

/-!
# Finite separable extensions and finite continuous Galois sets

Source: Stacks Project, Tags 03SF and 03QR (blueprint: lem-exc-etale-field-galois-classification).
-/

@[expose] public section

universe u v w w' z

open scoped IntermediateField

namespace FieldTheory

/-!
The affine description of `Hom_K(Spec K^sep, Spec L)` is the type of `K`-algebra
maps `L →ₐ[K] K^sep`.  The action below is postcomposition by `Gal(K^sep/K)`.
-/

private theorem embeddings_transitive
    (K : Type u) (Ks : Type v) [Field K] [Field Ks] [Algebra K Ks]
    [IsSepClosure K Ks] (L : Type w) [Field L] [Algebra K L]
    (σ τ : L →ₐ[K] Ks) : ∃ g : Gal(Ks / K), g.toAlgHom.comp σ = τ := by
  let e := σ.equivFieldRange.symm.trans τ.equivFieldRange
  refine ⟨e.liftNormal Ks, ?_⟩
  ext x
  have h := e.liftNormal_commutes Ks (σ.equivFieldRange x)
  simpa [e] using h

private theorem embedding_stabilizer
    (K : Type u) (Ks : Type v) [Field K] [Field Ks] [Algebra K Ks]
    (L : Type w) [Field L] [Algebra K L] (σ : L →ₐ[K] Ks) :
    {g : Gal(Ks / K) | g.toAlgHom.comp σ = σ} =
      (IntermediateField.map σ ⊤).fixingSubgroup := by
  ext g
  constructor
  · intro h x
    obtain ⟨y, _, hy⟩ := (IntermediateField.mem_map _).mp x.property
    change g x.val = x.val
    rw [← hy]
    exact DFunLike.congr_fun h y
  · intro h
    apply AlgHom.ext
    intro x
    exact h ⟨σ x, (IntermediateField.mem_map _).mpr ⟨x, trivial, rfl⟩⟩

private theorem transitive_actions_equiv
    (G : Type u) [Group G] (A : Type v) (B : Type w)
    [MulAction G A] [MulAction G B]
    [MulAction.IsPretransitive G A] [MulAction.IsPretransitive G B]
    (a : A) (b : B) (h : ∀ g : G, g • a = a ↔ g • b = b) :
    ∃ e : A ≃ B, ∀ (g : G) (x : A), e (g • x) = g • e x := by
  classical
  let H := MulAction.stabilizer G a
  let f : G ⧸ H → A := MulAction.ofQuotientStabilizer G a
  have hf : Function.Bijective f := by
    refine ⟨MulAction.injective_ofQuotientStabilizer G a, ?_⟩
    intro x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a x
    exact ⟨QuotientGroup.mk g, hg⟩
  let f' : G ⧸ H → B := fun q ↦ Quotient.liftOn' q (fun g : G ↦ g • b)
    (by
      intro g₁ g₂ hg
      have ha : (g₁⁻¹ * g₂) • a = a := QuotientGroup.leftRel_apply.mp hg
      have hb := (h (g₁⁻¹ * g₂)).mp ha
      calc
        g₁ • b = g₁ • ((g₁⁻¹ * g₂) • b) := congrArg (g₁ • ·) hb.symm
        _ = g₂ • b := by rw [smul_smul, mul_inv_cancel_left])
  have hf' : Function.Bijective f' := by
    constructor
    · intro q₁ q₂
      refine Quotient.inductionOn₂' q₁ q₂ ?_
      intro g₁ g₂ hg
      apply Quotient.sound'
      apply QuotientGroup.leftRel_apply.mpr
      change (g₁⁻¹ * g₂) • a = a
      apply (h _).mpr
      change g₁ • b = g₂ • b at hg
      rw [mul_smul, ← hg, inv_smul_smul]
    · intro x
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G b x
      exact ⟨QuotientGroup.mk g, hg⟩
  let ea := Equiv.ofBijective f hf
  let eb := Equiv.ofBijective f' hf'
  refine ⟨ea.symm.trans eb, ?_⟩
  have he : ∀ (g : G) (q : G ⧸ H), f' (g • q) = g • f' q := by
    intro g q
    refine Quotient.inductionOn' q ?_
    intro k
    exact mul_smul g k b
  intro g x
  have ha : ea.symm (g • x) = g • ea.symm x := by
    apply ea.injective
    change f (ea.symm (g • x)) = f (g • ea.symm x)
    dsimp [f]
    rw [MulAction.ofQuotientStabilizer_smul]
    exact (ea.apply_symm_apply (g • x)).trans
      (congrArg (g • ·) (ea.apply_symm_apply x)).symm
  change eb (ea.symm (g • x)) = g • eb (ea.symm x)
  rw [ha]
  exact he g (ea.symm x)

/-- Finite separable extensions of a field are classified by finite continuous Galois sets.

Source: Stacks Project, Tags 03SF and 03QR (blueprint: lem-exc-etale-field-galois-classification).
The proof first identifies geometric points with algebra embeddings. Embeddings exist by
extension to the separable closure and are finite because their values on a finite basis
are roots of minimal polynomials. Extend an isomorphism between two images to an
endomorphism of the separable closure; algebraicity makes it invertible, proving
transitivity. Stabilizers are fixing subgroups, which are open for finite subextensions.
For a nonempty transitive continuous discrete action, the stabilizer of a point is open;
its fixed field is finite separable and its embedding action has the same homogeneous
G-set. Finally, an equivariant map is determined by one embedding. The fixed-field
identity factors its image through that embedding and gives the unique field map.
-/
theorem finite_separable_extension_galois_classification
    (K : Type u) (Ksep : Type v) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep]
    (L : Type w) (L' : Type w') [Field L] [Field L'] [Algebra K L] [Algebra K L']
    [FiniteDimensional K L] [FiniteDimensional K L']
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K L'] :
    (Nonempty (L →ₐ[K] Ksep) ∧ Finite (L →ₐ[K] Ksep) ∧
      (∀ σ τ : L →ₐ[K] Ksep, ∃ g : Gal(Ksep / K),
        g.toAlgHom.comp σ = τ) ∧
      (∀ σ : L →ₐ[K] Ksep,
        {g : Gal(Ksep / K) | g.toAlgHom.comp σ = σ} =
          (IntermediateField.map σ ⊤).fixingSubgroup) ∧
      (∀ σ : L →ₐ[K] Ksep,
        IsOpen {g : Gal(Ksep / K) | g.toAlgHom.comp σ = σ})) ∧
    (∀ (Y : Type z) [Finite Y] [MulAction (Gal(Ksep / K)) Y],
      Nonempty Y →
      MulAction.IsPretransitive (Gal(Ksep / K)) Y →
      (∀ y : Y, IsOpen {g : Gal(Ksep / K) | g • y = y}) →
        ∃ E : IntermediateField K Ksep,
          FiniteDimensional K E ∧ Algebra.IsSeparable K E ∧
            ∃ e : Y ≃ (E →ₐ[K] Ksep),
              ∀ (g : Gal(Ksep / K)) (y : Y),
                e (g • y) = g.toAlgHom.comp (e y)) ∧
    Function.Bijective
      (fun (f : L' →ₐ[K] L) =>
        (⟨fun (σ : L →ₐ[K] Ksep) => σ.comp f,
          by
            intro g σ
            rfl⟩ :
          {φ : (L →ₐ[K] Ksep) → (L' →ₐ[K] Ksep) //
            ∀ (g : Gal(Ksep / K)) (σ : L →ₐ[K] Ksep),
              φ (g.toAlgHom.comp σ) = g.toAlgHom.comp (φ σ)}))
  := by
  classical
  let : IsSepClosed Ksep := IsSepClosure.sep_closed K
  have hn : Nonempty (L →ₐ[K] Ksep) := ⟨IsSepClosed.lift⟩
  have ht := embeddings_transitive K Ksep L
  have hs := embedding_stabilizer K Ksep L
  have ho : ∀ σ : L →ₐ[K] Ksep,
      IsOpen {g : Gal(Ksep / K) | g.toAlgHom.comp σ = σ} := by
    intro σ
    rw [hs σ]
    let : FiniteDimensional K σ.fieldRange :=
      σ.equivFieldRange.toLinearEquiv.finiteDimensional
    have hm : IntermediateField.map σ ⊤ = σ.fieldRange := by
      ext x
      simp [IntermediateField.mem_map, AlgHom.mem_fieldRange]
    rw [hm]
    exact IntermediateField.fixingSubgroup_isOpen _
  refine ⟨⟨hn, inferInstance, ht, hs, ho⟩, ?_, ?_⟩
  · intro (Y : Type z) _ _ hY htrans hopen
    let := hY
    let := htrans
    let y := Classical.choice hY
    let H := MulAction.stabilizer (Gal(Ksep / K)) y
    have hH : IsOpen (H : Set (Gal(Ksep / K))) := hopen y
    obtain ⟨hfin, hsep, hfix, _⟩ :=
      (openSubgroup_fixedField_finite_separable.{u, v, z} K Ksep).1 H hH
    let E := IntermediateField.fixedField H
    let : FiniteDimensional K E := hfin
    let : Algebra.IsSeparable K E := hsep
    let : MulAction (Gal(Ksep / K)) (E →ₐ[K] Ksep) := {
      smul g σ := g.toAlgHom.comp σ
      one_smul σ := by ext x; rfl
      mul_smul g h σ := by ext x; rfl }
    let : MulAction.IsPretransitive (Gal(Ksep / K)) (E →ₐ[K] Ksep) :=
      ⟨embeddings_transitive K Ksep E⟩
    have hstab : ∀ g : Gal(Ksep / K), g • y = y ↔ g • E.val = E.val := by
      intro g
      change g ∈ H ↔ g.toAlgHom.comp E.val = E.val
      rw [← hfix]
      constructor
      · intro hg
        ext x
        exact hg x
      · intro hg x
        exact DFunLike.congr_fun hg x
    obtain ⟨e, he⟩ := transitive_actions_equiv (Gal(Ksep / K)) Y
      (E →ₐ[K] Ksep) y E.val hstab
    exact ⟨E, hfin, hsep, e, he⟩
  · constructor
    · intro f f' h
      obtain ⟨σ⟩ := hn
      have hh := congrArg (fun φ ↦ φ.val σ) h
      ext x
      exact σ.injective (DFunLike.congr_fun hh x)
    · intro φ
      obtain ⟨σ⟩ := hn
      let τ := φ.val σ
      have hr : ∀ x : L', τ x ∈ σ.fieldRange := by
        intro x
        rw [← InfiniteGalois.fixedField_fixingSubgroup σ.fieldRange]
        rw [IntermediateField.mem_fixedField_iff]
        intro g hg
        have hσ : g.toAlgHom.comp σ = σ := by
          ext t
          exact hg (σ.equivFieldRange t)
        have hτ : g.toAlgHom.comp τ = τ := by
          exact (φ.property g σ).symm.trans (congrArg φ.val hσ)
        exact DFunLike.congr_fun hτ x
      let τ' : L' →ₐ[K] σ.fieldRange := τ.codRestrict σ.fieldRange.toSubalgebra hr
      let f : L' →ₐ[K] L := σ.equivFieldRange.symm.toAlgHom.comp τ'
      have hf : σ.comp f = τ := by
        ext x
        have he := σ.equivFieldRange.apply_symm_apply (τ' x)
        exact congrArg Subtype.val he
      refine ⟨f, ?_⟩
      apply Subtype.ext
      funext ρ
      obtain ⟨g, hg⟩ := ht σ ρ
      change ρ.comp f = φ.val ρ
      rw [← hg, AlgHom.comp_assoc, hf]
      exact (φ.property g σ).symm

end FieldTheory
