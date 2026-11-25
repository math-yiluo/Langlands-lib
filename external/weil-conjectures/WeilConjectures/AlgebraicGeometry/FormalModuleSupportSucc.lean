/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

/-! Consecutive levels of a coherent formal module have equal support.

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 30.26.11 (Tag 0CYV).
(blueprint: lem-weil-pbc-formal-system-support-succ)
-/

@[expose] public section

universe u

open Opposite

namespace AlgebraicGeometry

/-- Consecutive support equality, reducing the constant-support theorem to induction.

The proof identifies the stalk at level `n` with the quotient of the stalk at level
`n + 1` by the `(n + 1)`st ideal power, and uses the annihilation condition to show that
this quotient vanishes exactly when the original stalk vanishes. This is the
consecutive-level step in the proof of the constant-support theorem.
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 30.26.11 (Tag 0CYV),
first sentence of the proof of (1).
(blueprint: lem-weil-pbc-formal-system-support-succ). -/
theorem formalModule_support_succ {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (n : ℕ) :
    {x : X | ¬ Subsingleton ((F.obj.obj (op (n + 1))).presheaf.stalk x)} =
      {x : X | ¬ Subsingleton ((F.obj.obj (op n)).presheaf.stalk x)} := by
  ext x
  apply not_congr
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let M := F.obj.obj (op (n + 1))
  obtain ⟨e, _, _, _, _, _, hpow⟩ :=
    Scheme.ideal_module_product_stalk I.toModulesι M x
  let J : Ideal (X.presheaf.stalk x) :=
    LinearMap.range (CategoryTheory.CategoryStruct.comp (S.map I.toModulesι) e.hom).hom
  obtain ⟨_, _, φ, _⟩ := hpow (n + 1) (by omega)
  obtain ⟨_, hrz, _⟩ := hpow (n + 2) (by omega)
  obtain ⟨q, _⟩ := F.property.2.2 n
  let ψ := (S.mapIso q).toLinearEquiv
  have hz : J ^ (n + 2) • (⊤ : Submodule (X.presheaf.stalk x) (S.obj M)) = ⊥ := by
    rw [← hrz]
    have hzero := S.map_isZero (F.property.2.1 (n + 1))
    have hf : S.map (Scheme.idealModuleProductι
        (Scheme.idealSheafPower I.toModulesι (n + 2)).2 M) = 0 :=
      hzero.eq_zero_of_src _
    rw [hf]
    exact LinearMap.range_zero
  change Subsingleton (S.obj M) ↔ Subsingleton (S.obj (F.obj.obj (op n)))
  constructor
  · intro hm
    have : Subsingleton (S.obj M) := hm
    have : Subsingleton (S.obj M ⧸ J ^ (n + 1) •
        (⊤ : Submodule (X.presheaf.stalk x) (S.obj M))) := inferInstance
    exact (φ.toEquiv.trans ψ.toEquiv).surjective.subsingleton
  · intro hn
    have : Subsingleton (S.obj (F.obj.obj (op n))) := hn
    have hquot : Subsingleton (S.obj M ⧸ J ^ (n + 1) •
        (⊤ : Submodule (X.presheaf.stalk x) (S.obj M))) :=
      (φ.toEquiv.trans ψ.toEquiv).injective.subsingleton
    have ht := Submodule.Quotient.subsingleton_iff.mp hquot
    have ht₂ : J ^ ((n + 1) + (n + 1)) •
        (⊤ : Submodule (X.presheaf.stalk x) (S.obj M)) = ⊤ := by
      rw [pow_add, Submodule.mul_smul, ht, ht]
    have hle : J ^ ((n + 1) + (n + 1)) •
        (⊤ : Submodule (X.presheaf.stalk x) (S.obj M)) ≤
        J ^ (n + 2) • (⊤ : Submodule (X.presheaf.stalk x) (S.obj M)) :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
    rw [ht₂, hz] at hle
    refine ⟨fun a b ↦ ?_⟩
    have ha : a = 0 := by
      simpa using hle (show a ∈ (⊤ : Submodule _ (S.obj M)) from trivial)
    have hb : b = 0 := by
      simpa using hle (show b ∈ (⊤ : Submodule _ (S.obj M)) from trivial)
    exact ha.trans hb.symm


end AlgebraicGeometry
