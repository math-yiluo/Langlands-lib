import Langlands.BaseChange.RankOneCyclicOrbitalGeometry
import Langlands.ClassFieldTheory.Local.NormExistenceClosedSupport
import Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof
import Langlands.Representation.Compact.CharZeroAverage
import Langlands.Representation.Exponents.DualEigenfunctionalExistence
import Langlands.Representation.Parabolic.NaturalFirstAdjointness
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof

/-! # Unramified principal series detected by Borel Jacquet fixed vectors -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence GeneralLinear GeneralLinear.BlockShape Unramified
open Unramified.SphericalExistence

universe u v

section Character

variable {M : Type*} [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M]
  {V : Type v} [AddCommGroup V] [Module ℂ V]

private theorem exists_character_of_fixedVectors (ρ : Representation ℂ M V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup M) (hK : IsCompact (K : Set M))
    [FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)] [Nontrivial (fixedVectors ρ K.toSubgroup)] :
    ∃ (χ : M →* ℂˣ) (ℓ : V →ₗ[ℂ] ℂ), ℓ ≠ 0 ∧
      (∀ k : K, χ k.val = 1) ∧ ∀ m x, ℓ (ρ m x) = (χ m : ℂ) * ℓ x := by
  classical
  let W := fixedVectors ρ K.toSubgroup
  let T (m : M) : ρ.IntertwiningMap ρ :=
    { toLinearMap := ρ m
      isIntertwining' := fun g => by
        rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, mul_comm m g] }
  let f (m : M) : Module.End ℂ W := fixedVectorsMap (T m) K.toSubgroup
  have hcomm (m n : M) : Commute (f m) (f n) := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    change ρ m (ρ n w.val) = ρ n (ρ m w.val)
    rw [← Module.End.mul_apply, ← map_mul, mul_comm m n, map_mul, Module.End.mul_apply]
  let E (c : M → ℂ) := ⨅ m, (f m).maxGenEigenspace (c m)
  have htop : ⨆ c, E c = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      (fun m n _ => hcomm m n) (fun m => Module.End.iSup_maxGenEigenspace_eq_top (f m))
  have hex : ∃ c, E c ≠ ⊥ := by
    by_contra! hz
    have h : (⊥ : Submodule ℂ W) = ⊤ := by simpa only [hz, iSup_const] using htop
    exact bot_ne_top h
  obtain ⟨c, hc⟩ := hex
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  change w ∈ ⨅ m, (f m).maxGenEigenspace (c m) at hw
  rw [Submodule.mem_iInf] at hw
  obtain ⟨dual, hdual, hEig⟩ := DualEigenfunctional.exists_dual_eigenvector f hcomm c hw0 hw
  let P := Compact.CharZero.fixedProjection ρ hρ K hK
  let ℓ := dual.comp P
  have hℓ : ℓ ≠ 0 := by
    intro hz
    apply hdual
    ext x
    have hPx : P x.val = x := Compact.CharZero.fixedProjection_fixed ρ hρ K hK x
    have h := LinearMap.congr_fun hz x.val
    simpa only [ℓ, LinearMap.comp_apply, hPx, LinearMap.zero_apply] using h
  have htrans (m : M) (x : V) : ℓ (ρ m x) = c m * ℓ x := by
    have hc' := LinearMap.congr_fun (Compact.CharZero.averageMap_commute ρ ρ hρ hρ K hK (T m)) x
    have hp : f m (P x) = P (ρ m x) := Subtype.ext hc'
    change dual (P (ρ m x)) = c m * dual (P x)
    rw [← hp, hEig]
  obtain ⟨x, hx⟩ : ∃ x, ℓ x ≠ 0 := by
    by_contra! h
    exact hℓ (LinearMap.ext fun x => h x)
  have hone : c 1 = 1 := mul_right_cancel₀ hx (by simpa using (htrans 1 x).symm)
  have hmul (m n : M) : c (m * n) = c m * c n := by
    apply mul_right_cancel₀ hx
    rw [← htrans, map_mul, Module.End.mul_apply, htrans m, htrans n, mul_assoc]
  have hne (m : M) : c m ≠ 0 := by
    intro hz
    have hh := hmul m m⁻¹
    rw [mul_inv_cancel, hone, hz, zero_mul] at hh
    exact one_ne_zero hh
  let χ : M →* ℂˣ :=
    { toFun := fun m => Units.mk0 (c m) (hne m)
      map_one' := Units.ext hone
      map_mul' := fun m n => Units.ext (hmul m n) }
  refine ⟨χ, ℓ, hℓ, ?_, htrans⟩
  intro k
  apply Units.ext
  change c k.val = 1
  apply mul_right_cancel₀ hx
  rw [← htrans, one_mul]
  exact congrArg dual (Compact.CharZero.fixedProjection_apply_rho ρ hρ K hK k x)

end Character

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup

private abbrev BorelLevi {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (r : ℕ) :=
  (borelShape r).Levi F.Carrier

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (r : ℕ)

set_option hygiene false in
local notation "B" => borelShape r
set_option hygiene false in
local notation "𝔐" => BorelLevi F r

private def unitCoordinates : 𝔐 ≃ₜ* (Fin (r + 1) → F.Carrierˣ) :=
  let rankOne := rankOneDeterminantEquiv F.Carrier
  { toFun := fun m i => rankOne (m i)
    invFun := fun a i => rankOne.symm (a i)
    left_inv := fun m => funext fun i => rankOne.symm_apply_apply (m i)
    right_inv := fun a => funext fun i => rankOne.apply_symm_apply (a i)
    map_mul' := fun m n => funext fun i => rankOne.map_mul (m i) (n i)
    continuous_toFun := continuous_pi fun i => rankOne.continuous.comp (continuous_apply i)
    continuous_invFun := continuous_pi fun i => rankOne.symm.continuous.comp (continuous_apply i) }

private def integralLevi : OpenSubgroup 𝔐 :=
  let T := F.canonicalTopologicalData
  ⟨T.normOneLevi B, T.isOpen_normOneLevi B⟩

private theorem isCompact_integralLevi : IsCompact (integralLevi F r : Set 𝔐) := by
  let T := F.canonicalTopologicalData
  let U := Set.pi Set.univ (fun _ : Fin (r + 1) => (T.unitSubgroup : Set F.Carrierˣ))
  have hU : IsCompact U := isCompact_univ_pi fun _ => by
    rw [← T.unitFiltration_zero]
    exact T.isCompact_unitFiltration 0
  convert hU.image (unitCoordinates F r).symm.continuous using 1
  ext m
  let e := unitCoordinates F r
  have hmem : m ∈ integralLevi F r ↔ e m ∈ U := by
    change m ∈ T.normOneLevi B ↔ e m ∈ U
    rw [T.mem_normOneLevi]
    simp only [U, Set.mem_pi, Set.mem_univ, true_implies]
    apply forall_congr'
    intro i
    change T.normalizedAbsUnits (e m i) = 1 ↔ e m i ∈ T.unitSubgroup
    rw [ClassFieldTheory.Local.mem_unitSubgroup_iff_ord_eq_zero F T, ← MonoidHom.mem_ker,
      ← T.ker_ordUnits, MonoidHom.mem_ker]
    rfl
  change m ∈ integralLevi F r ↔ m ∈ e.symm '' U
  rw [hmem]
  constructor
  · exact fun hm => ⟨e m, hm, e.symm_apply_apply m⟩
  · rintro ⟨a, ha, rfl⟩
    simpa only [e.apply_symm_apply] using ha

private theorem exists_tuple_of_leviCharacter (χ : 𝔐 →* ℂˣ)
    (hχ : ∀ k : integralLevi F r, χ k.val = 1) :
    ∃ z : Fin (r + 1) → ℂˣ, ∀ m, χ m =
      ∏ i, character F (z i) (GeneralLinear.determinant (m i)) := by
  classical
  let T := F.canonicalTopologicalData
  let e := unitCoordinates F r
  let χi (i : Fin (r + 1)) : F.Carrierˣ →* ℂˣ :=
    (χ.comp e.symm.toMonoidHom).comp (MonoidHom.mulSingle (fun _ : Fin (r + 1) => F.Carrierˣ) i)
  have hi (i : Fin (r + 1)) : T.IsUnramifiedCharacter (χi i) := by
    intro a ha
    let coordinates : Fin (r + 1) → F.Carrierˣ := Pi.mulSingle i a
    let k : 𝔐 := e.symm coordinates
    have hk : k ∈ integralLevi F r := by
      change k ∈ T.normOneLevi B
      rw [T.mem_normOneLevi]
      intro j
      have hj : determinant (k j) = coordinates j := by
        change e k j = coordinates j
        exact congrFun (e.apply_symm_apply coordinates) j
      change T.normalizedAbsUnits (determinant (k j)) = 1
      rw [hj]
      by_cases h : j = i
      · subst j
        simpa [coordinates] using ha
      · have hc : coordinates j = 1 :=
          Pi.mulSingle_eq_of_ne (M := fun _ : Fin (r + 1) => F.Carrierˣ) h a
        rw [hc, map_one]
    exact hχ ⟨k, hk⟩
  refine ⟨fun i => χi i T.uniformizerUnit, fun m => ?_⟩
  have hf : ∀ i, χi i = T.unramifiedCharacter (χi i T.uniformizerUnit) :=
    fun i => T.eq_unramifiedCharacter _ (hi i)
  change χ m = ∏ i, T.unramifiedCharacter (χi i T.uniformizerUnit) (e m i)
  simp_rw [← hf]
  rw [show χ m = (χ.comp e.symm.toMonoidHom) (e m) by
    change χ m = χ (e.symm (e m))
    rw [e.symm_apply_apply]]
  conv_lhs => rw [← Finset.univ_prod_mulSingle (e m), map_prod]
  rfl

/-- An irreducible representation with a nonzero integral-diagonal fixed
vector in its normalized Borel Jacquet module embeds into an unramified principal series. -/
def UnramifiedJacquetDetectionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (r : ℕ)
    (π : AutomorphicObject.{u,v} F r.succPNat),
    let J := F.canonicalTopologicalData.normalizedJacquet (borelShape r) π.obj.representation
    let W := fixedVectors J (F.canonicalTopologicalData.normOneLevi (borelShape r))
    FiniteDimensional ℂ W → Nontrivial W →
    ∃ (z : Fin (r + 1) → ℂˣ)
      (j : π.obj.representation.IntertwiningMap (principalSeriesOfTuple F z)),
      Function.Injective j.toLinearMap

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem unramifiedJacquetDetection : UnramifiedJacquetDetectionStatement.{u,v} := by
  intro p _ F r π J W hfin hnontrivial
  let T := F.canonicalTopologicalData
  let : IsTopologicalGroup 𝔐 := T.leviTopologicalGroup B
  let : FiniteDimensional ℂ (fixedVectors J (integralLevi F r).toSubgroup) := hfin
  let : Nontrivial (fixedVectors J (integralLevi F r).toSubgroup) := hnontrivial
  let : CommGroup (GeneralLinear 1 F.Carrier) := rankOneCommGroup F.Carrier
  let : CommGroup 𝔐 := inferInstanceAs (CommGroup (Fin (r + 1) → GeneralLinear 1 F.Carrier))
  obtain ⟨χ, ℓ, hℓ, hχ, hEigen⟩ := exists_character_of_fixedVectors J
    (T.isSmooth_normalizedJacquet B π.property.2.1) (integralLevi F r)
    (isCompact_integralLevi F r)
  obtain ⟨z, hz⟩ := exists_tuple_of_leviCharacter F r χ hχ
  let σ := (borelShape r).blockTensor (blockCharacters F z)
  have hs (m : 𝔐) : σ m (sphericalTensor r) = (χ m : ℂ) • sphericalTensor r := by
    change (borelShape r).blockTensor (blockCharacters F z) m (sphericalTensor r) = _
    rw [blockTensor_tprod]
    calc
      _ = PiTensorProduct.tprod ℂ (fun i : Fin (borelShape r).length =>
          (character F (z i) (determinant (m i)) : ℂ) • (1 : ℂ)) := rfl
      _ = _ := by
        rw [MultilinearMap.map_smul_univ, hz, Units.coe_prod]
        rfl
  let A : J.IntertwiningMap σ :=
    { toLinearMap := ℓ.smulRight (sphericalTensor r)
      isIntertwining' := fun m => by
        apply LinearMap.ext
        intro x
        change ℓ (J m x) • sphericalTensor r = σ m (ℓ x • sphericalTensor r)
        rw [hEigen, map_smul, hs, smul_smul, mul_comm] }
  have hA : A ≠ 0 := by
    intro h
    apply hℓ
    apply LinearMap.ext
    intro x
    have hz : ℓ x • sphericalTensor r = 0 := congrArg (fun f : J.IntertwiningMap σ => f x) h
    exact (smul_eq_zero.mp hz).resolve_right (sphericalTensor_ne_zero r)
  let e : (π.obj.representation.IntertwiningMap (principalSeriesOfTuple F z)) ≃ₗ[ℂ]
      (J.IntertwiningMap σ) := Parabolic.FirstAdjointness.equiv T B π.property.2.1
  let j := e.symm A
  have hj0 : j ≠ 0 := (LinearEquiv.map_ne_zero_iff e.symm).mpr hA
  let : π.obj.representation.IsIrreducible := π.property.1
  exact ⟨z, j, (Representation.IsIrreducible.injective_or_eq_zero j).resolve_right hj0⟩

end Langlands.BaseChange
