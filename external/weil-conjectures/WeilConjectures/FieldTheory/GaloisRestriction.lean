/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.GaloisClosure
public import WeilConjectures.FieldTheory.Galois.NormalFixedField

/-!
# Restriction of automorphisms along a map of field extensions

Consider a commutative square of fields
```
Ω₁ --ω--> Ω₂
 ^         ^
 |         |
L₁ --l--> L₂
```
with `Ω₁ / L₁` normal. Every `σ ∈ Aut(Ω₂/L₂)` maps `ω(Ω₁)` onto itself, hence restricts to an
automorphism of `Ω₁ / L₁`. This gives a group homomorphism
`AlgEquiv.restrictNormalHomAlong : Aut(Ω₂/L₂) →* Aut(Ω₁/L₁)` characterised by
`ω (restrictNormalHomAlong hω σ x) = σ (ω x)`.

If moreover `Ω₂ / L₂` is normal and `L₁` is relatively closed in `L₂` inside `Ω₂` (an element of
`Ω₁` whose image lies in `L₂` already lies in `L₁`), the image of this homomorphism is dense:
it surjects onto `Gal(L'/L₁)` for every finite Galois subextension `L'` of `Ω₁ / L₁`
(`AlgEquiv.exists_restrictNormalHomAlong_eq`, `AlgEquiv.exists_eq_of_forall_mem_range`).

The group-theoretic form of "the wild kernels map onto each other" (for a commutative square
`q₁ ∘ r = ψ ∘ q₂` of groups with `r` surjective and `ψ` injective, `r` maps `ker q₂` onto
`ker q₁`) is `MonoidHom.map_ker_eq_ker_of_comp_eq`.
-/

@[expose] public section

open IntermediateField

namespace AlgEquiv

variable {L₁ Ω₁ L₂ Ω₂ : Type*} [Field L₁] [Field Ω₁] [Field L₂] [Field Ω₂]
  [Algebra L₁ Ω₁] [Algebra L₂ Ω₂] {l : L₁ →+* L₂} {ω : Ω₁ →+* Ω₂}

/-- Given a commutative square `ω ∘ algebraMap L₁ Ω₁ = algebraMap L₂ Ω₂ ∘ l` with `Ω₁ / L₁`
normal, the restriction of automorphisms of `Ω₂ / L₂` to (the image under `ω` of) `Ω₁`. -/
noncomputable def restrictNormalHomAlong [Normal L₁ Ω₁]
    (hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l) :
    Gal(Ω₂/L₂) →* Gal(Ω₁/L₁) :=
  letI : Algebra L₁ L₂ := l.toAlgebra
  letI : Algebra L₁ Ω₂ := ((algebraMap L₂ Ω₂).comp l).toAlgebra
  letI : Algebra Ω₁ Ω₂ := ω.toAlgebra
  haveI : IsScalarTower L₁ L₂ Ω₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower L₁ Ω₁ Ω₂ :=
    IsScalarTower.of_algebraMap_eq fun x => (congrArg (· x) hω).symm
  (restrictNormalHom Ω₁).comp
    { toFun σ := σ.restrictScalars L₁
      map_one' := rfl
      map_mul' _ _ := rfl }

/-- The characterising property of `AlgEquiv.restrictNormalHomAlong`. -/
@[simp]
theorem restrictNormalHomAlong_commutes [Normal L₁ Ω₁]
    (hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l) (σ : Gal(Ω₂/L₂)) (x : Ω₁) :
    ω (restrictNormalHomAlong hω σ x) = σ (ω x) :=
  letI : Algebra L₁ L₂ := l.toAlgebra
  letI : Algebra L₁ Ω₂ := ((algebraMap L₂ Ω₂).comp l).toAlgebra
  letI : Algebra Ω₁ Ω₂ := ω.toAlgebra
  haveI : IsScalarTower L₁ L₂ Ω₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower L₁ Ω₁ Ω₂ :=
    IsScalarTower.of_algebraMap_eq fun x => (congrArg (· x) hω).symm
  restrictNormal_commutes (σ.restrictScalars L₁) Ω₁ x

/-- If `Ω₂ / L₂` is normal and `L₁` is relatively closed in `L₂` inside `Ω₂`, then every
automorphism of a finite Galois subextension `L'` of `Ω₁ / L₁` is the restriction of an
automorphism of `Ω₂ / L₂`. -/
theorem exists_restrictNormalHomAlong_eq [Normal L₁ Ω₁] [Normal L₂ Ω₂]
    (hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l)
    (hclosed : ∀ x : Ω₁, ω x ∈ Set.range (algebraMap L₂ Ω₂) →
      x ∈ Set.range (algebraMap L₁ Ω₁))
    (L' : FiniteGaloisIntermediateField L₁ Ω₁) (a : Gal(L'/L₁)) :
    ∃ σ : Gal(Ω₂/L₂), ∀ x : L', restrictNormalHomAlong hω σ x = a x := by
  set f := (restrictNormalHom (L' : IntermediateField L₁ Ω₁)).comp (restrictNormalHomAlong hω)
  have hbot : fixedField f.range = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hfix : ∀ σ : Gal(Ω₂/L₂), σ (ω x) = ω x := by
      intro σ
      rw [← restrictNormalHomAlong_commutes hω,
        ← restrictNormalHom_apply (L' : IntermediateField L₁ Ω₁) _ x]
      exact congrArg (fun y : L' => ω y) ((mem_fixedField_iff _ _).mp hx (f σ) ⟨σ, rfl⟩)
    have hsep : IsSeparable L₂ (ω x) := by
      have hx : IsSeparable L₁ (x : Ω₁) := by
        unfold IsSeparable
        rw [← minpoly_eq]
        exact Algebra.IsSeparable.isSeparable L₁ x
      refine (Polynomial.Separable.map (f := l) hx).of_dvd (minpoly.dvd L₂ _ ?_)
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hω, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    let z : fixedField (⊤ : Subgroup Gal(Ω₂/L₂)) := ⟨ω x, fun σ => hfix σ⟩
    have hz : IsSeparable L₂ z := by
      unfold IsSeparable
      rwa [minpoly_eq]
    obtain ⟨c, hc⟩ := (Normal.isPurelyInseparable_fixedField (F := L₂) (E := Ω₂)).inseparable
      L₂ z hz
    obtain ⟨d, hd⟩ := hclosed x ⟨c, congrArg Subtype.val hc⟩
    exact (mem_bot (F := L₁)).mpr ⟨d, Subtype.ext hd⟩
  have htop : f.range = ⊤ := by
    rw [← fixingSubgroup_fixedField f.range, hbot, fixingSubgroup_bot]
  obtain ⟨σ, hσ⟩ := f.mem_range.mp (htop ▸ Subgroup.mem_top a)
  refine ⟨σ, fun x => ?_⟩
  rw [← hσ]
  exact (restrictNormalHom_apply (L' : IntermediateField L₁ Ω₁) _ x).symm

/-- If `Ω₂ / L₂` is normal and `L₁` is relatively closed in `L₂` inside `Ω₂`, then every
automorphism `a` of a finite Galois subextension `L'` of `Ω₁ / L₁` extends to an automorphism
`σ₁` of `Ω₁ / L₁` which is compatible along `ω` with an automorphism `σ₂` of `Ω₂ / L₂`. -/
theorem exists_eq_of_forall_mem_range [Normal L₁ Ω₁] [Normal L₂ Ω₂]
    (hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l)
    (hclosed : ∀ x : Ω₁, ω x ∈ Set.range (algebraMap L₂ Ω₂) →
      x ∈ Set.range (algebraMap L₁ Ω₁))
    (L' : FiniteGaloisIntermediateField L₁ Ω₁) (a : Gal(L'/L₁)) :
    ∃ σ₂ : Gal(Ω₂/L₂), ∃ σ₁ : Gal(Ω₁/L₁),
      (∀ x : L', σ₁ x = a x) ∧ ∀ x, ω (σ₁ x) = σ₂ (ω x) := by
  obtain ⟨σ, hσ⟩ := exists_restrictNormalHomAlong_eq hω hclosed L' a
  exact ⟨σ, restrictNormalHomAlong hω σ, hσ, restrictNormalHomAlong_commutes hω σ⟩


section Inertia

variable {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra K₁ L₁] [Algebra K₁ Ω₁]
  [IsScalarTower K₁ L₁ Ω₁] [Algebra K₂ Ω₂]

/-- **The wild kernels map onto each other.** Let `K₁ ⊆ L₁ ⊆ Ω₁` and `K₂ ⊆ L₂ ⊆ Ω₂` be towers of
fields and `ω : Ω₁ ⟶ Ω₂`. Assume that every `σ₁ ∈ Aut(Ω₁/K₁)` is the restriction of some
`σ₂ ∈ Aut(Ω₂/K₂)` along `ω` (the map of inertia groups `I₂ ⟶ I₁` is surjective), and that an
element of `Aut(Ω₂/K₂)` fixing `ω(L₁)` fixes `L₂` (the map of the quotients `I₂/P₂ ⟶ I₁/P₁` is
injective, e.g. the tame inertia quotients are identified). Then every `σ₁ ∈ Aut(Ω₁/L₁)` is the
restriction of some `σ₂ ∈ Aut(Ω₂/L₂)`: the kernels `Pᵢ = Aut(Ωᵢ/Lᵢ)` map onto each other (the
Galois form of `MonoidHom.map_ker_eq_ker_of_comp_eq`). -/
theorem exists_comp_eq_of_exists_comp_eq_of_fixes
    (hI : ∀ σ₁ : Ω₁ ≃ₐ[K₁] Ω₁, ∃ σ₂ : Ω₂ ≃ₐ[K₂] Ω₂, ∀ x, ω (σ₁ x) = σ₂ (ω x))
    (htame : ∀ σ₂ : Ω₂ ≃ₐ[K₂] Ω₂,
      (∀ x : L₁, σ₂ (ω (algebraMap L₁ Ω₁ x)) = ω (algebraMap L₁ Ω₁ x)) →
        ∀ y : L₂, σ₂ (algebraMap L₂ Ω₂ y) = algebraMap L₂ Ω₂ y)
    (σ₁ : Ω₁ ≃ₐ[L₁] Ω₁) : ∃ σ₂ : Ω₂ ≃ₐ[L₂] Ω₂, ∀ x, ω (σ₁ x) = σ₂ (ω x) := by
  obtain ⟨σ₂, hσ₂⟩ := hI (σ₁.restrictScalars K₁)
  have hfix := htame σ₂ fun x ↦ by
    rw [← hσ₂]
    exact congrArg ω (σ₁.commutes x)
  exact ⟨AlgEquiv.ofRingEquiv (f := σ₂.toRingEquiv) hfix, hσ₂⟩

/-- The finite-quotient form of `AlgEquiv.exists_comp_eq_of_exists_comp_eq_of_fixes`: under the
same hypotheses, with `Ω₁ / L₁` normal, every automorphism `a` of a finite Galois subextension
`L'` of `Ω₁ / L₁` extends to some `σ₁ ∈ Aut(Ω₁/L₁)` which is the restriction of some
`σ₂ ∈ Aut(Ω₂/L₂)` along `ω`. -/
theorem exists_eq_of_exists_comp_eq_of_fixes [Normal L₁ Ω₁]
    (hI : ∀ σ₁ : Ω₁ ≃ₐ[K₁] Ω₁, ∃ σ₂ : Ω₂ ≃ₐ[K₂] Ω₂, ∀ x, ω (σ₁ x) = σ₂ (ω x))
    (htame : ∀ σ₂ : Ω₂ ≃ₐ[K₂] Ω₂,
      (∀ x : L₁, σ₂ (ω (algebraMap L₁ Ω₁ x)) = ω (algebraMap L₁ Ω₁ x)) →
        ∀ y : L₂, σ₂ (algebraMap L₂ Ω₂ y) = algebraMap L₂ Ω₂ y)
    (L' : FiniteGaloisIntermediateField L₁ Ω₁) (a : Gal(L'/L₁)) :
    ∃ σ₂ : Gal(Ω₂/L₂), ∃ σ₁ : Gal(Ω₁/L₁),
      (∀ x : L', σ₁ x = a x) ∧ ∀ x, ω (σ₁ x) = σ₂ (ω x) := by
  obtain ⟨σ₁, hσ₁⟩ := AlgEquiv.restrictNormalHom_surjective (F := L₁)
    (K₁ := (L' : IntermediateField L₁ Ω₁)) Ω₁ a
  obtain ⟨σ₂, hσ₂⟩ := exists_comp_eq_of_exists_comp_eq_of_fixes hI htame σ₁
  refine ⟨σ₂, σ₁, fun x ↦ ?_, hσ₂⟩
  rw [← hσ₁]
  exact (restrictNormalHom_apply (L' : IntermediateField L₁ Ω₁) σ₁ x).symm

end Inertia

end AlgEquiv
