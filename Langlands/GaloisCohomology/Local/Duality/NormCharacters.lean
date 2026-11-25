import Mathlib.FieldTheory.Galois.Abelian
import Langlands.ClassFieldTheory.Local.Artin.NormSubgroup
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNorm

/-!
# Norm groups of abelian extensions of a local field

Two theorems of local class field theory for a finite abelian extension `L` of a nonarchimedean
local field `K` (in any universe), from the local Artin homomorphism `abelianArtinHom` of
`Langlands.ClassFieldTheory.Local.Artin.NormSubgroup` (surjective with kernel the norm group):

- the reciprocity isomorphism `Gal(L/K) ≃* Kˣ / N(Lˣ)` (`reciprocityEquiv`);
- the norm index `[Kˣ : N(Lˣ)] = [L : K]` (`index_fieldNormSubgroup_of_isAbelianGalois`).

Consequence used by local duality: an open normal subgroup `H` of `Gal(Ω/F)` with abelian quotient
such that every element of `F` is a norm from the fixed field of `H` is the whole group
(`eq_top_of_forall_exists_norm`).
-/

noncomputable section

namespace Langlands.GaloisCohomology.Local

universe u

open IntermediateField LocalFieldTheory

section Reciprocity

variable (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The Galois group of a finite abelian extension of `K`, as a commutative group. -/
abbrev galCommGroup : CommGroup Gal(L/K) :=
  { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }

/-- **Reciprocity isomorphism** of a finite abelian extension `L/K` of local fields:
`Gal(L/K) ≃* Kˣ / N(Lˣ)` (the inverse of the isomorphism induced by the local Artin homomorphism
`Artin.abelianArtinHom`, which is surjective with kernel the norm group). -/
def reciprocityEquiv : Gal(L/K) ≃* Kˣ ⧸ DiscreteValuationField.fieldNormSubgroup K L :=
  (QuotientGroup.quotientKerEquivOfSurjective
      (ClassFieldTheory.Local.Artin.abelianArtinHom K L)
      (ClassFieldTheory.Local.Artin.abelianArtinHom_surjective K L)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (ClassFieldTheory.Local.Artin.abelianArtinHom_ker K L))

/-- **Norm index**: for a finite abelian extension `L/K` of local fields,
`[Kˣ : N(Lˣ)] = [L : K]`. -/
theorem index_fieldNormSubgroup_of_isAbelianGalois :
    (DiscreteValuationField.fieldNormSubgroup K L).index = Module.finrank K L := by
  rw [Subgroup.index, ← Nat.card_congr (reciprocityEquiv K L).toEquiv,
    ← IsGalois.card_aut_eq_finrank]

end Reciprocity

section Norms

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {Ω : Type u} [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsSepClosure F Ω] in
theorem exists_norm_iff_mem_fieldNormSubgroup (E : IntermediateField F Ω) [FiniteDimensional F E]
    (a : Fˣ) : (∃ y : E, Algebra.norm F y = (a : F)) ↔
      a ∈ DiscreteValuationField.fieldNormSubgroup F E := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hy
      exact a.ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, Units.ext (by simp [hy])⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, rfl⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsSepClosure F Ω] in
theorem exists_norm_of_eq {E₁ E₂ : IntermediateField F Ω} (h : E₁ = E₂) {a : F}
    (hy : ∃ y : E₁, Algebra.norm F y = a) : ∃ y : E₂, Algebra.norm F y = a := by
  subst h
  exact hy

/-- An open normal subgroup `H` of `Gal(Ω/F)` with abelian quotient such that every element of
`Fˣ` is a norm from the fixed field of `H` is the whole group (from the norm index). -/
theorem eq_top_of_forall_exists_norm (H : Subgroup Gal(Ω/F)) [H.Normal]
    (hH : IsOpen (H : Set Gal(Ω/F))) (hcomm : ∀ σ τ : Gal(Ω/F), σ * τ * σ⁻¹ * τ⁻¹ ∈ H)
    (h : ∀ a : Fˣ, ∃ y : fixedField H, Algebra.norm F y = (a : F)) : H = ⊤ := by
  set E := fixedField H with hE
  have hfix : E.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, Subgroup.isClosed_of_isOpen H hH⟩
  have hfin : FiniteDimensional F E :=
    (InfiniteGalois.isOpen_iff_finite E).1 (by rw [hfix]; exact hH)
  have hgal : IsGalois F E :=
    (InfiniteGalois.normal_iff_isGalois E).1 (by rw [hfix]; infer_instance)
  have hc : ∀ σ' τ' : Gal(E/F), σ' * τ' = τ' * σ' := by
    intro σ' τ'
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) (E := Ω) σ'
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) (E := Ω) τ'
    have hk : σ * τ * σ⁻¹ * τ⁻¹ ∈ (AlgEquiv.restrictNormalHom E).ker := by
      rw [E.restrictNormalHom_ker, hfix]
      exact hcomm σ τ
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hk
    have key : ∀ {M : Type _} [Group M] (x y : M), x * y * x⁻¹ * y⁻¹ = 1 → x * y = y * x := by
      intro M _ x y hxy
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = y * x := by rw [hxy, one_mul]
    exact key _ _ hk
  have : IsAbelianGalois F E := { toIsGalois := hgal, toIsMulCommutative := ⟨⟨hc⟩⟩ }
  have hidx := index_fieldNormSubgroup_of_isAbelianGalois F E
  have htop : DiscreteValuationField.fieldNormSubgroup F E = ⊤ :=
    eq_top_iff.2 fun a _ => (exists_norm_iff_mem_fieldNormSubgroup E a).1 (h a)
  rw [htop, Subgroup.index_top] at hidx
  have hbot : E = ⊥ := IntermediateField.finrank_eq_one_iff.1 hidx.symm
  rw [← hfix, hbot, IntermediateField.fixingSubgroup_bot]

end Norms

end Langlands.GaloisCohomology.Local
