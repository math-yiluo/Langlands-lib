import Langlands.BaseChange.UnramifiedWeylJacquetSupport.Characters
import Langlands.BaseChange.UnramifiedWeylJacquetSupport.Weights
import Langlands.Correspondence.OrderedUnramifiedSphericalGenerationProof
import Langlands.Representation.Exponents.DualEigenfunctionalExistence
import Langlands.Representation.Parabolic.NaturalFirstAdjointness

/-! An opposite-order Borel Jacquet exponent forces sphericity. -/

noncomputable section

namespace Langlands.BaseChange.WeylJacquet

open GeneralLinear GeneralLinear.BlockShape Correspondence Unramified
open Unramified.SphericalExistence

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}

attribute [local instance] heckeFieldTopology heckeGeneralLinearTopology
  heckeGeneralLinearTopologicalGroup

set_option hygiene false in
local notation "B" => borelShape r
set_option hygiene false in
local notation "M" => (borelShape r).Levi F.Carrier
set_option hygiene false in
local notation "K" => borelIntegralDiagonal F r

private theorem eq_top_of_contains_integral_and_uniformizers (H : Subgroup M) (hK : K ≤ H)
    (hG : ∀ i, borelUniformizerLevi F r i ∈ H) : H = ⊤ := by
  classical
  let T := F.canonicalTopologicalData
  let H' := H.comap (singletonLevi F.Carrier (n := r + 1))
  refine top_unique fun m _ => ?_
  obtain ⟨a, rfl⟩ := (singletonCoordinates F r).symm.surjective m
  change a ∈ H'
  let b (i : Fin (r + 1)) := a i * T.uniformizerUnit ^ (-T.ord (a i : F.Carrier))
  let c (i : Fin (r + 1)) := T.uniformizerUnit ^ T.ord (a i : F.Carrier)
  have hbc : b * c = a := by
    funext i
    change a i * T.uniformizerUnit ^ (-T.ord (a i : F.Carrier)) *
      T.uniformizerUnit ^ T.ord (a i : F.Carrier) = a i
    rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hb : b ∈ H' := hK ((singletonLevi_mem_borelIntegralDiagonal_iff F b).mpr fun i => by
    change T.ord ((a i * T.uniformizerUnit ^ (-T.ord (a i : F.Carrier)) : F.Carrierˣ) : F.Carrier) = 0
    rw [Units.val_mul, T.ord_mul (a i).ne_zero (Units.ne_zero _)]
    simp only [Units.val_zpow_eq_zpow_val, T.uniformizerUnit_val, T.ord_zpow,
      T.ord_uniformizer, mul_one, add_neg_cancel])
  have hc : c ∈ H' := by
    rw [← Finset.univ_prod_mulSingle c]
    refine H'.prod_mem fun i _ => ?_
    have hi : Pi.mulSingle i T.uniformizerUnit ∈ H' := by
      change singletonLevi F.Carrier (Pi.mulSingle i T.uniformizerUnit) ∈ H
      exact borelUniformizerLevi_eq_singletonLevi F r i ▸ hG i
    change Pi.mulSingle i (T.uniformizerUnit ^ T.ord (a i : F.Carrier)) ∈ H'
    rw [Pi.mulSingle_zpow]
    exact H'.zpow_mem hi _
  exact hbc ▸ H'.mul_mem hb hc

private theorem exists_torus_eigenfunctional {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ M V) (hρ : IsSmooth ρ) [FiniteDimensional ℂ (fixedVectors ρ K)]
    (z : Fin (r + 1) → ℂˣ) (hz : torusWeightSpace F ρ z ≠ ⊥) :
    ∃ ℓ : V →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧ ∀ m v, ℓ (ρ m v) = (borelCharacter F z m : ℂ) * ℓ v := by
  obtain ⟨x, hx, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz
  change x ∈ ⨅ i, (torusUniformizerAction F ρ i).maxGenEigenspace (z i : ℂ) at hx
  rw [Submodule.mem_iInf] at hx
  obtain ⟨eigen, heigen, h_eigen⟩ := DualEigenfunctional.exists_dual_eigenvector
    (torusUniformizerAction F ρ) (torusUniformizerAction_commute F ρ) _ hx₀ hx
  let := F.canonicalTopologicalData.leviTopologicalGroup B
  let K₀ := borelIntegralDiagonalOpen F r
  let hK₀ := borelIntegralDiagonal_isCompact F r
  let P := Compact.CharZero.fixedProjection ρ hρ K₀ hK₀
  let ℓ := eigen.comp P
  have hℓ : ℓ ≠ 0 := by
    intro h
    apply heigen
    apply LinearMap.ext
    intro v
    have hv := LinearMap.congr_fun h v.val
    change eigen (P v.val) = 0 at hv
    have hv' : P v.val = v := Compact.CharZero.fixedProjection_fixed ρ hρ K₀ hK₀ v
    exact (congrArg eigen hv').symm.trans hv
  let χ : M →* ℂˣ := borelCharacter F z
  let H : Subgroup M :=
    { carrier := {m | ∀ v, ℓ (ρ m v) = (χ m : ℂ) * ℓ v}
      one_mem' := by intro v; rw [map_one, Module.End.one_apply, map_one, Units.val_one, one_mul]
      mul_mem' := by
        intro m n hm hn v
        change ∀ v, ℓ (ρ m v) = (χ m : ℂ) * ℓ v at hm
        change ∀ v, ℓ (ρ n v) = (χ n : ℂ) * ℓ v at hn
        change ℓ (ρ (m * n) v) = (χ (m * n) : ℂ) * ℓ v
        rw [map_mul ρ, Module.End.mul_apply, hm, hn, map_mul χ, Units.val_mul, mul_assoc]
      inv_mem' := by
        intro m hm v
        have he := hm (ρ m⁻¹ v)
        change ℓ (ρ m (ρ m⁻¹ v)) = (χ m : ℂ) * ℓ (ρ m⁻¹ v) at he
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at he
        change ℓ (ρ m⁻¹ v) = (χ m⁻¹ : ℂ) * ℓ v
        rw [map_inv χ, Units.val_inv_eq_inv_val, he, ← mul_assoc, inv_mul_cancel₀ (χ m).ne_zero,
          one_mul] }
  have hunit : K ≤ H := by
    intro m hm v
    change eigen (P (ρ m v)) = (borelCharacter F z m : ℂ) * eigen (P v)
    rw [borelCharacter_eq_one_of_mem_integral F z hm, Units.val_one, one_mul]
    exact congrArg eigen (Compact.CharZero.fixedProjection_apply_rho ρ hρ K₀ hK₀ ⟨m, hm⟩ v)
  have hgen (i : Fin (r + 1)) : borelUniformizerLevi F r i ∈ H := by
    let u := borelUniformizerLevi F r i
    let a : ρ.IntertwiningMap ρ := ⟨ρ u, by
      intro m
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul,
        Subgroup.mem_center_iff.mp (borelUniformizerLevi_mem_center F r i) m]⟩
    intro v
    have h := LinearMap.congr_fun (Compact.CharZero.averageMap_commute ρ ρ hρ hρ K₀ hK₀ a) v
    have hP : P (ρ u v) = torusUniformizerAction F ρ i (P v) := Subtype.ext h.symm
    change eigen (P (ρ u v)) = (borelCharacter F z u : ℂ) * eigen (P v)
    rw [hP]
    exact (h_eigen i (P v)).trans
      (congrArg (fun c : ℂˣ => (c : ℂ) * eigen (P v)) (borelCharacter_uniformizer F z i).symm)
  have hH := eq_top_of_contains_integral_and_uniformizers F H hunit hgen
  exact ⟨ℓ, hℓ, fun m => show m ∈ H from hH ▸ Subgroup.mem_top m⟩

set_option backward.isDefEq.respectTransparency false in
/-- A prescribed Borel Jacquet weight of an irreducible admissible representation gives
 an actual embedding into the principal series with that ordered tuple. -/
theorem exists_embedding_of_borelJacquet_weight (A : AutomorphicObject.{uF, uV} F r.succPNat)
    {z : Fin (r + 1) → ℂˣ} (hz : z ∈ borelJacquetMultiset F (r := r) A.obj.representation) :
    ∃ j : A.obj.representation.IntertwiningMap (principalSeriesOfTuple F z), Function.Injective j := by
  classical
  let T := F.canonicalTopologicalData
  let ρ := A.obj.representation
  let J := T.normalizedJacquet B ρ
  let : FiniteDimensional ℂ (fixedVectors J K) :=
    finiteDimensional_borelJacquetIntegralFixed F ρ A.property.2
  have hm := Multiset.count_pos.mpr hz
  rw [count_borelJacquetMultiset_automorphicObject F A] at hm
  have hW : torusWeightSpace F J z ≠ ⊥ := by
    intro h
    change 0 < Module.finrank ℂ (torusWeightSpace F J z) at hm
    rw [h, finrank_bot] at hm
    exact (Nat.lt_irrefl 0) hm
  obtain ⟨ℓ, hℓ, htrans⟩ := exists_torus_eigenfunctional F J
    (T.isSmooth_normalizedJacquet B A.obj.isSmooth) z hW
  let σ := (B).blockTensor (blockCharacters F z)
  let f : J.IntertwiningMap σ :=
    { toLinearMap := ℓ.smulRight (sphericalTensor r)
      isIntertwining' := fun m => by
        apply LinearMap.ext
        intro v
        change ℓ (J m v) • sphericalTensor r = σ m (ℓ v • sphericalTensor r)
        change _ = (B).blockTensor (blockCharacters F z) m (ℓ v • sphericalTensor r)
        rw [htrans, blockTensor_eq_smul, smul_smul] }
  have hf : f ≠ 0 := by
    intro h
    apply hℓ
    apply LinearMap.ext
    intro v
    have hv : ℓ v • sphericalTensor r = 0 := congrArg (fun a : J.IntertwiningMap σ => a v) h
    exact (smul_eq_zero.mp hv).resolve_right (sphericalTensor_ne_zero r)
  let e : (ρ.IntertwiningMap (principalSeriesOfTuple F z)) ≃ₗ[ℂ] (J.IntertwiningMap σ) :=
    Parabolic.FirstAdjointness.equiv T B A.obj.isSmooth
  let j := e.symm f
  have hj : j ≠ 0 := (LinearEquiv.map_ne_zero_iff e.symm).mpr hf
  let : ρ.IsIrreducible := A.property.1
  exact ⟨j, (Representation.IsIrreducible.injective_or_eq_zero j).resolve_right hj⟩

private theorem orderedQuotient_fixed_ne_bot (z : Fin (r + 1) → ℂˣ)
    (hz : Monotone fun i => ‖(z i : ℂ)‖) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V}
    (q : (principalSeriesOfTuple F z).IntertwiningMap π) (hq : ∃ x, q.toLinearMap x ≠ 0) :
    fixedVectors π (sphericalSubgroup F r) ≠ ⊥ := by
  intro hπ
  obtain ⟨v, hval, hv⟩ := exists_fixed_smoothFunction ((B).parabolic F.Carrier)
    (borelInducing F z) (sphericalOpenSubgroup F r) (exists_borel_mul_spherical F)
    (sphericalTensor r) (borelInducing_sphericalTensor F z)
  have hv₀ : v ≠ 0 := by
    intro h
    apply sphericalTensor_ne_zero r
    rw [h] at hval
    exact hval.symm
  have hqv : q v = 0 := by
    have h := (fixedVectorsMap q (sphericalSubgroup F r) ⟨v, hv⟩).property
    have : q v ∈ fixedVectors π (sphericalSubgroup F r) := h
    rwa [hπ, Submodule.mem_bot] at this
  let w : q.ker.toSubmodule := ⟨v, hqv⟩
  have hw : w ∈ fixedVectors q.ker.toRepresentation (sphericalSubgroup F r) :=
    fun k => Subtype.ext (hv k)
  have hker : q.ker = ⊤ := orderedUnramifiedSphericalGeneration F r z hz q.ker
    ((Submodule.ne_bot_iff _).mpr ⟨w, hw, fun h => hv₀ (congrArg Subtype.val h)⟩)
  obtain ⟨x, hx⟩ := hq
  apply hx
  have h : x ∈ q.ker := hker ▸ Submodule.mem_top
  exact h

/-- An irreducible admissible representation with a weakly norm-decreasing Jacquet
 tuple has a nonzero spherical vector. -/
theorem spherical_of_opposite_borelJacquet_weight (A : AutomorphicObject.{uF, uV} F r.succPNat)
    {z : Fin (r + 1) → ℂˣ} (hz : z ∈ borelJacquetMultiset F (r := r) A.obj.representation)
    (ho : IsOppositeWeightOrder z) :
    fixedVectors A.obj.representation (sphericalSubgroup F r) ≠ ⊥ := by
  obtain ⟨j, hj⟩ := exists_embedding_of_borelJacquet_weight F A hz
  let T := F.canonicalTopologicalData
  let ρ := A.obj.representation
  let hP := principalSeriesOfTuple_isAdmissible F z
  let hcof := compactOpen_cofinal F T (r + 1)
  let z' : Fin (r + 1) → ℂˣ := fun i => (z i)⁻¹
  have hz' : Monotone fun i => ‖(z' i : ℂ)‖ := by
    intro i j hij
    change ‖(((z i)⁻¹ : ℂˣ) : ℂ)‖ ≤ ‖(((z j)⁻¹ : ℂˣ) : ℂ)‖
    simp only [Units.val_inv_eq_inv_val, norm_inv]
    exact inv_anti₀ (norm_pos_iff.mpr (Units.ne_zero (z j))) (ho hij)
  let e := principalSeriesOfTupleSmoothDualEquiv F z
  let D : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (r + 1) F.Carrier) := A.obj.contragredient
  let q : (principalSeriesOfTuple F z').IntertwiningMap D.representation :=
    (contragredientMap j).comp e.symm.toIntertwiningMap
  have hq : Function.Surjective q.toLinearMap := by
    change Function.Surjective ((contragredientMap j) ∘ e.symm.toLinearEquiv)
    exact (contragredientMap_surjective_of_injective_of_compact_cofinal
      hcof A.obj.isSmooth hP.1 j hj).comp e.symm.surjective
  have hirr : D.IsIrreducible :=
    (SmoothRep.isIrreducible_contragredient_iff hcof A.obj A.property.2).mpr A.property.1
  let : Nontrivial D :=
    CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible D.representation hirr
  obtain ⟨w, hw⟩ := exists_ne (0 : D)
  obtain ⟨v, hv⟩ := hq w
  have h := orderedQuotient_fixed_ne_bot F z' hz' q ⟨v, fun h₀ => hw (hv.symm.trans h₀)⟩
  let eK := smoothDualCompactFixedEquiv ρ A.obj.isSmooth (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r)
  have hn : Nontrivial (fixedVectors (smoothContragredient ρ) (sphericalSubgroup F r)) :=
    Submodule.nontrivial_iff_ne_bot.mpr h
  let Y : Submodule ℂ A.obj := fixedVectors ρ (sphericalSubgroup F r)
  have hY : Nontrivial (Module.Dual ℂ Y) := (Equiv.nontrivial_congr eK.toEquiv).mp hn
  have hY' : Nontrivial Y := (Module.nontrivial_dual_iff ℂ).mp hY
  exact Submodule.nontrivial_iff_ne_bot.mp hY'

end Langlands.BaseChange.WeylJacquet
