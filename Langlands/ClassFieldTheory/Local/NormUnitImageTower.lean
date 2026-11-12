import Langlands.ClassFieldTheory.Local.NormUnitImageIndexSupport
import Langlands.LocalFactor.Ramification.Herbrand.SubextensionProof

/-! # Level claims for norm images of unit filtrations, and their tower law

`LevelClaims K L` packages three divisibility statements at every nonnegative
upper level of a finite extension of p-adic fields with their canonical
topological data. They pass from `E/K` and `L/E` to `L/K` in a Galois tower.
-/

noncomputable section

namespace Langlands.LocalClassField.NormUnitImage

open Ramification

universe u v w

variable {p : ℕ} [Fact p.Prime]

/-- The three level claims for `L/K` at every real `a ≥ 0`. With `n = ⌈a⌉₊`,
`m = ⌈ψ_{L/K}(a)⌉₊` and `G^a` the upper group: the norm maps `U_L^m` into
`U_K^n`; the index of `N(U_L^m)` in `U_K^n` divides `|G^a|`; and
`[Kˣ : U_K^n · N(Lˣ)] · |G^a|` divides `[L : K]`. -/
def LevelClaims (K : PadicField.{u} p) (L : PadicField.{v} p) [Algebra K.Carrier L.Carrier]
    [IsScalarTower (Padic p) K.Carrier L.Carrier] [FiniteDimensional K.Carrier L.Carrier] :
    Prop :=
  ∀ a : ℝ, 0 ≤ a →
    (L.canonicalTopologicalData.unitFiltration
        ⌈Padic.herbrandPsi L.canonicalTopologicalData K.Carrier a⌉₊).map
        (normUnits K.Carrier L.Carrier) ≤ K.canonicalTopologicalData.unitFiltration ⌈a⌉₊ ∧
    ((L.canonicalTopologicalData.unitFiltration
        ⌈Padic.herbrandPsi L.canonicalTopologicalData K.Carrier a⌉₊).map
        (normUnits K.Carrier L.Carrier)).relIndex
        (K.canonicalTopologicalData.unitFiltration ⌈a⌉₊) ∣
      Nat.card (Padic.upperRamificationGroup L.canonicalTopologicalData K.Carrier a) ∧
    (K.canonicalTopologicalData.unitFiltration ⌈a⌉₊ ⊔ normSubgroup K.Carrier L.Carrier).index *
        Nat.card (Padic.upperRamificationGroup L.canonicalTopologicalData K.Carrier a) ∣
      Module.finrank K.Carrier L.Carrier

section Tower

variable (K : PadicField.{u} p) (L : PadicField.{v} p) (E : PadicField.{w} p)
  [Algebra K.Carrier L.Carrier] [Algebra K.Carrier E.Carrier] [Algebra E.Carrier L.Carrier]
  [IsScalarTower K.Carrier E.Carrier L.Carrier]
  [IsScalarTower (Padic p) K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier E.Carrier]
  [IsScalarTower (Padic p) E.Carrier L.Carrier]
  [FiniteDimensional K.Carrier L.Carrier] [FiniteDimensional K.Carrier E.Carrier]
  [FiniteDimensional E.Carrier L.Carrier]

omit [IsScalarTower (Padic p) K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier E.Carrier]
  [IsScalarTower (Padic p) E.Carrier L.Carrier] in
/-- Transitivity of the unit norms. -/
theorem normUnits_comp :
    (normUnits K.Carrier E.Carrier).comp (normUnits E.Carrier L.Carrier) =
      normUnits K.Carrier L.Carrier :=
  MonoidHom.ext fun x =>
    Units.ext (Algebra.norm_norm (R := K.Carrier) (S := E.Carrier) (a := (x : L.Carrier)))

omit [IsScalarTower (Padic p) K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier E.Carrier]
  [IsScalarTower (Padic p) E.Carrier L.Carrier] in
/-- The norm of `E/K` carries the norm subgroup of `L/E` onto that of `L/K`. -/
theorem normSubgroup_map_tower :
    (normSubgroup E.Carrier L.Carrier).map (normUnits K.Carrier E.Carrier) =
      normSubgroup K.Carrier L.Carrier := by
  rw [normSubgroup, MonoidHom.map_range, normUnits_comp]
  rfl

variable [IsGalois K.Carrier L.Carrier] [IsGalois K.Carrier E.Carrier]
  [IsGalois E.Carrier L.Carrier]

omit [FiniteDimensional K.Carrier L.Carrier] [FiniteDimensional K.Carrier E.Carrier]
  [FiniteDimensional E.Carrier L.Carrier] in
/-- The order of an upper group of `L/K` at a level `a ≥ 0` is the product of
the orders of the upper group of `E/K` at `a` and of the upper group of `L/E`
at `ψ_{E/K}(a)`. -/
theorem card_upperRamificationGroup_tower (a : ℝ) (ha : 0 ≤ a) :
    Nat.card (Padic.upperRamificationGroup L.canonicalTopologicalData K.Carrier a) =
      Nat.card (Padic.upperRamificationGroup E.canonicalTopologicalData K.Carrier a) *
        Nat.card (Padic.upperRamificationGroup L.canonicalTopologicalData E.Carrier
          (Padic.herbrandPsi E.canonicalTopologicalData K.Carrier a)) := by
  set TL := L.canonicalTopologicalData
  set TE := E.canonicalTopologicalData
  have hψ := HerbrandBridge.herbrandPsi_tower K L E TL TE a
  rw [card_eq_card_map_mul_card_inf_ker
      (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := L.Carrier) E.Carrier),
    HerbrandBridge.upperRestrictionCompatibility K L E TL TE a (by linarith)]
  congr 1
  have hmem : ∀ τ : L.Carrier ≃ₐ[E.Carrier] L.Carrier,
      τ.restrictScalars K.Carrier ∈ Padic.upperRamificationGroup TL K.Carrier a ↔
        τ ∈ Padic.upperRamificationGroup TL E.Carrier (Padic.herbrandPsi TE K.Carrier a) := by
    intro τ
    rw [HerbrandBridge.restrictScalars_mem_upperRamificationGroup_iff K.Carrier E.Carrier TL a τ,
      hψ, Padic.herbrandPhi_herbrandPsi]
  have hS : (AlgEquiv.restrictNormalHom (F := K.Carrier) (K₁ := L.Carrier) E.Carrier).ker ⊓
      Padic.upperRamificationGroup TL K.Carrier a =
      (Padic.upperRamificationGroup TL E.Carrier (Padic.herbrandPsi TE K.Carrier a)).map
        (AlgEquiv.restrictScalarsHom K.Carrier) := by
    ext σ
    simp only [Subgroup.mem_map, Subgroup.mem_inf, AlgEquiv.restrictScalarsHom_apply]
    constructor
    · rintro ⟨hσk, hσ⟩
      let τ := (HerbrandBridge.towerSubgroupEquiv K L E).symm ⟨σ, hσk⟩
      have hτ : τ.restrictScalars K.Carrier = σ :=
        congrArg Subtype.val ((HerbrandBridge.towerSubgroupEquiv K L E).apply_symm_apply ⟨σ, hσk⟩)
      refine ⟨τ, (hmem τ).mp ?_, hτ⟩
      rw [hτ]
      exact hσ
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨HerbrandBridge.restrictScalars_mem_towerKernel K L E τ, (hmem τ).mpr hτ⟩
  rw [hS, Subgroup.card_map_of_injective
    (AlgEquiv.restrictScalarsHom_injective K.Carrier (A := L.Carrier) (S := E.Carrier))]

/-- The level claims pass along a Galois tower `K ⊆ E ⊆ L`. -/
theorem levelClaims_tower (hKE : LevelClaims K E) (hEL : LevelClaims E L) :
    LevelClaims K L := by
  intro a ha
  set TK := K.canonicalTopologicalData
  set TE := E.canonicalTopologicalData
  set TL := L.canonicalTopologicalData
  have hb : 0 ≤ Padic.herbrandPsi TE K.Carrier a := by
    rw [← Padic.herbrandPsi_zero TE K.Carrier]
    exact (Padic.herbrandPsi_strictMono TE K.Carrier).monotone ha
  obtain ⟨C1, V1, W1⟩ := hKE a ha
  obtain ⟨C2, V2, W2⟩ := hEL _ hb
  rw [HerbrandBridge.herbrandPsi_tower K L E TL TE a, card_upperRamificationGroup_tower K L E a ha]
  set n := ⌈a⌉₊
  set k := ⌈Padic.herbrandPsi TE K.Carrier a⌉₊
  set m := ⌈Padic.herbrandPsi TL E.Carrier (Padic.herbrandPsi TE K.Carrier a)⌉₊
  have hX : (TL.unitFiltration m).map (normUnits K.Carrier L.Carrier) =
      ((TL.unitFiltration m).map (normUnits E.Carrier L.Carrier)).map
        (normUnits K.Carrier E.Carrier) := by
    rw [Subgroup.map_map, normUnits_comp]
  have hXY : (TL.unitFiltration m).map (normUnits K.Carrier L.Carrier) ≤
      (TE.unitFiltration k).map (normUnits K.Carrier E.Carrier) := by
    rw [hX]
    exact Subgroup.map_mono C2
  refine ⟨hXY.trans C1, ?_, ?_⟩
  · rw [← Subgroup.relIndex_mul_relIndex _ _ _ hXY C1, mul_comm]
    refine mul_dvd_mul V1 ?_
    rw [hX]
    exact (relIndex_map_dvd _ C2).trans V2
  · have hsup : TK.unitFiltration n ⊔ normSubgroup K.Carrier L.Carrier =
        TK.unitFiltration n ⊔ (TE.unitFiltration k ⊔ normSubgroup E.Carrier L.Carrier).map
          (normUnits K.Carrier E.Carrier) := by
      rw [Subgroup.map_sup, normSubgroup_map_tower, ← sup_assoc, sup_eq_left.mpr C1]
    have hle : TK.unitFiltration n ⊔ normSubgroup K.Carrier L.Carrier ≤
        TK.unitFiltration n ⊔ normSubgroup K.Carrier E.Carrier := by
      rw [← normSubgroup_map_tower K L E]
      exact sup_le_sup_left (Subgroup.map_le_range _ _) _
    have hrel : (TK.unitFiltration n ⊔ normSubgroup K.Carrier L.Carrier).relIndex
        (TK.unitFiltration n ⊔ normSubgroup K.Carrier E.Carrier) ∣
        (TE.unitFiltration k ⊔ normSubgroup E.Carrier L.Carrier).index := by
      have h := relIndex_sup_map_dvd (normUnits K.Carrier E.Carrier) (TK.unitFiltration n)
        (le_top : TE.unitFiltration k ⊔ normSubgroup E.Carrier L.Carrier ≤ ⊤)
      rw [Subgroup.relIndex_top_right, ← MonoidHom.range_eq_map, ← hsup] at h
      exact h
    rw [← Subgroup.relIndex_mul_index hle,
      ← Module.finrank_mul_finrank K.Carrier E.Carrier L.Carrier]
    calc _ = ((TK.unitFiltration n ⊔ normSubgroup K.Carrier E.Carrier).index *
            Nat.card (Padic.upperRamificationGroup TE K.Carrier a)) *
          ((TK.unitFiltration n ⊔ normSubgroup K.Carrier L.Carrier).relIndex
              (TK.unitFiltration n ⊔ normSubgroup K.Carrier E.Carrier) *
            Nat.card (Padic.upperRamificationGroup TL E.Carrier
              (Padic.herbrandPsi TE K.Carrier a))) := by ring
      _ ∣ _ := mul_dvd_mul W1 ((mul_dvd_mul_right hrel _).trans W2)

end Tower

end Langlands.LocalClassField.NormUnitImage
