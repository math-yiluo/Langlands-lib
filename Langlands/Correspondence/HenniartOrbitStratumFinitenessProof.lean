import Langlands.Correspondence.HenniartOrbitStratumFinitenessStatement
import Langlands.Correspondence.PadicSupercuspidalFinitenessProof
import Langlands.Representation.RankinSelberg.IntegralDeterminant
import Langlands.Representation.Whittaker.MirabolicPairingRigidityElementary
import Langlands.Representation.Twist.AdmissibilityProof

/-!
# Finiteness of the supercuspidal unramified-orbit strata: proof
-/

noncomputable section

namespace Langlands.Henniart.OrbitStratumFiniteness

open Langlands.Correspondence Langlands.VirtualRepresentation GeneralLinear
open Langlands.Henniart.Numerical

universe uK uV

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance orbitFinitenessTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance orbitFinitenessValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance orbitFinitenessLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

/-- Elements of the newvector subgroups have determinant of order zero. -/
theorem ord_det_eq_zero_of_mem_level (k a : ℕ) {g : GeneralLinear (k + 1) K.Carrier}
    (hg : g ∈ Conductor.levelSubgroup K.Carrier k a) :
    K.canonicalTopologicalData.ord (GeneralLinear.determinant g : K.Carrier) = 0 := by
  let T := K.canonicalTopologicalData
  have h0 : g ∈ Conductor.integralSubgroup T.Integers k := by
    have h := Conductor.levelSubgroup_antitone K.Carrier k (Nat.zero_le a) hg
    rwa [Conductor.levelSubgroup_zero] at h
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  have h : (T.residueCardinality : ℝ) ^ (-T.ord (GeneralLinear.determinant g : K.Carrier)) =
      (T.residueCardinality : ℝ) ^ (-(0 : ℤ)) := by
    rw [← T.normalizedAbs_of_ne_zero (GeneralLinear.determinant g).ne_zero, neg_zero,
      zpow_zero]
    exact RankinSelberg.normalizedAbs_det_of_mem_integralSubgroup T h0
  exact neg_injective (zpow_right_injective₀ (zero_lt_one.trans hq) hq.ne' h)

/-- Unramified determinant characters are trivial on every newvector subgroup. -/
theorem levelSubgroup_le_ker (k a : ℕ) (z : ℂˣ) :
    Conductor.levelSubgroup K.Carrier k a ≤
      (K.canonicalTopologicalData.determinantUnramifiedCharacter (k + 1) z).ker := by
  intro g hg
  rw [MonoidHom.mem_ker, PadicField.TopologicalData.determinantUnramifiedCharacter_apply,
    ord_det_eq_zero_of_mem_level K k a hg, zpow_zero]

/-- Schur's lemma: a supercuspidal representation of `GL_(k+1)(K)` has a central
character. -/
theorem exists_hasCentralCharacter (k : ℕ)
    (A : SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := k + 1)) :
    ∃ χ : Subgroup.center (GeneralLinear (k + 1) K.Carrier) →* ℂˣ,
      A.obj.HasCentralCharacter χ := by
  have := K.canonicalTopologicalData.generalLinearTopologicalGroup (k + 1)
  have := K.canonicalTopologicalData.generalLinearSecondCountableTopology (k + 1)
  have hirr : A.obj.IsIrreducible := A.property.1
  have hrank := Whittaker.MirabolicRigidity.rank_le_aleph0 A.obj.representation
    A.obj.isSmooth hirr
  have hc : ∀ z : Subgroup.center (GeneralLinear (k + 1) K.Carrier), ∃ c : ℂ,
      ∀ v, A.obj.representation (z : GeneralLinear (k + 1) K.Carrier) v = c • v := fun z =>
    Whittaker.MirabolicRigidity.exists_scalar_of_commute A.obj.representation hrank hirr _
      (fun g => congrArg A.obj.representation (Subgroup.mem_center_iff.mp z.property g))
  choose c hc using hc
  obtain ⟨v, hv⟩ := Whittaker.MirabolicRigidity.exists_ne_zero_of_isIrreducible
    A.obj.representation hirr
  have c_one : c 1 = 1 := by
    apply smul_left_injective ℂ hv
    change c 1 • v = (1 : ℂ) • v
    rw [← hc, OneMemClass.coe_one, map_one, one_smul]
    rfl
  have c_mul (z w : Subgroup.center (GeneralLinear (k + 1) K.Carrier)) :
      c (z * w) = c z * c w := by
    apply smul_left_injective ℂ hv
    change c (z * w) • v = (c z * c w) • v
    rw [← hc, Subgroup.coe_mul, map_mul, Module.End.mul_apply, hc, hc, smul_smul]
  have c_ne (z : Subgroup.center (GeneralLinear (k + 1) K.Carrier)) : c z ≠ 0 := by
    intro hz
    have h := c_mul z⁻¹ z
    rw [inv_mul_cancel, c_one, hz, mul_zero] at h
    exact one_ne_zero h
  refine ⟨{ toFun := fun z => Units.mk0 (c z) (c_ne z)
            map_one' := Units.ext c_one
            map_mul' := fun z w => Units.ext (c_mul z w) }, ?_⟩
  intro z w
  exact hc z w

/-! ### Normalized central characters -/

/-- A nonzero field element of order zero is an integer. -/
theorem mem_integers_of_ord_eq_zero {x : K.Carrier} (hx : x ≠ 0)
    (h : K.canonicalTopologicalData.ord x = 0) : x ∈ K.canonicalTopologicalData.Integers := by
  let T := K.canonicalTopologicalData
  rw [← T.normalizedAbs_le_one_iff_mem_integers, T.normalizedAbs_of_ne_zero hx, h, neg_zero,
    zpow_zero]

/-- A scalar matrix with an order-zero entry lies in the integral group. -/
theorem scalar_mem_levelSubgroup_zero (k : ℕ) {u : K.Carrierˣ}
    (hu : K.canonicalTopologicalData.ord (u : K.Carrier) = 0) :
    (GeneralLinear.scalar u : GeneralLinear (k + 1) K.Carrier) ∈
      Conductor.levelSubgroup K.Carrier k 0 := by
  let T := K.canonicalTopologicalData
  have h1 : (u : K.Carrier) ∈ T.Integers := mem_integers_of_ord_eq_zero K u.ne_zero hu
  have h2 : ((u⁻¹ : K.Carrierˣ) : K.Carrier) ∈ T.Integers := by
    apply mem_integers_of_ord_eq_zero K (Units.ne_zero _)
    rw [Units.val_inv_eq_inv_val, T.ord_inv, hu, neg_zero]
  rw [Conductor.levelSubgroup_zero, Conductor.mem_integralSubgroup]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change (Matrix.scalar (Fin (k + 1)) (u : K.Carrier)) i j ∈ _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact h1
    · exact Subring.zero_mem _
  · rw [← map_inv]
    change (Matrix.scalar (Fin (k + 1)) ((u⁻¹ : K.Carrierˣ) : K.Carrier)) i j ∈ _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact h2
    · exact Subring.zero_mem _

/-- The central elements of the integral group `GL_(k+1)(O)`. -/
def integralCenter (k : ℕ) : Subgroup (Subgroup.center (GeneralLinear (k + 1) K.Carrier)) :=
  (Conductor.levelSubgroup K.Carrier k 0).comap
    (Subgroup.center (GeneralLinear (k + 1) K.Carrier)).subtype

/-- The central elements of the level-`a` newvector subgroup, inside `integralCenter`. -/
def levelCenter (k a : ℕ) : Subgroup (integralCenter K k) :=
  (Conductor.levelSubgroup K.Carrier k a).comap
    ((Subgroup.center (GeneralLinear (k + 1) K.Carrier)).subtype.comp
      (integralCenter K k).subtype)

/-- Every central element is a power of the scalar uniformizer times an integral one. -/
theorem exists_uniformizer_zpow_mul (k : ℕ)
    (y : Subgroup.center (GeneralLinear (k + 1) K.Carrier)) :
    ∃ (m : ℤ) (y₀ : Subgroup.center (GeneralLinear (k + 1) K.Carrier)),
      y₀ ∈ integralCenter K k ∧
        y = scalarToCenter K.canonicalTopologicalData.uniformizerUnit ^ m * y₀ := by
  let T := K.canonicalTopologicalData
  obtain ⟨x, rfl⟩ : ∃ x : K.Carrierˣ, scalarToCenter x = y := by
    have hy : (y : GeneralLinear (k + 1) K.Carrier) ∈
        (Matrix.GeneralLinearGroup.scalar (Fin (k + 1))).range := by
      simpa only [Matrix.GeneralLinearGroup.center_eq_range_scalar] using y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let m : ℤ := T.ord (x : K.Carrier)
  let u : K.Carrierˣ := x * T.uniformizerUnit ^ (-m)
  have hu : T.ord (u : K.Carrier) = 0 := by
    change T.ord ((x * T.uniformizerUnit ^ (-m) : K.Carrierˣ) : K.Carrier) = 0
    rw [Units.val_mul, T.ord_mul x.ne_zero (Units.ne_zero _), Units.val_zpow_eq_zpow_val,
      PadicField.TopologicalData.uniformizerUnit_val, T.ord_zpow, T.ord_uniformizer, mul_one,
      add_neg_cancel]
  refine ⟨m, scalarToCenter u, scalar_mem_levelSubgroup_zero K k hu, ?_⟩
  rw [← map_zpow, ← map_mul]
  congr 1
  change x = T.uniformizerUnit ^ m * (x * T.uniformizerUnit ^ (-m))
  rw [mul_left_comm, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

/-- The integral center modulo its level-`a` part is finite: it embeds in the quotient
of the compact group `GL_(k+1)(O)` by its open subgroup of level `a`. -/
theorem finite_quotient_levelCenter (k a : ℕ) :
    Finite (integralCenter K k ⧸ levelCenter K k a) := by
  have := K.canonicalTopologicalData.generalLinearTopologicalGroup (k + 1)
  let L₀ := Conductor.levelOpenSubgroup K.Carrier k 0
  let Lₐ := Conductor.levelOpenSubgroup K.Carrier k a
  have : CompactSpace L₀.toSubgroup :=
    isCompact_iff_compactSpace.mp (Conductor.isCompact_levelOpenSubgroup K.Carrier k 0)
  have : Finite (L₀.toSubgroup ⧸ Lₐ.toSubgroup.subgroupOf L₀.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ Lₐ.isOpen)
  have : (Lₐ.toSubgroup.subgroupOf L₀.toSubgroup).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let ψ : integralCenter K k →* L₀.toSubgroup :=
    ((Subgroup.center (GeneralLinear (k + 1) K.Carrier)).subtype.comp
      (integralCenter K k).subtype).codRestrict L₀.toSubgroup (fun y => y.property)
  have h : ((Lₐ.toSubgroup.subgroupOf L₀.toSubgroup).comap ψ).FiniteIndex := inferInstance
  have : (levelCenter K k a).FiniteIndex := h
  exact Subgroup.finite_quotient_of_finiteIndex

/-- Central characters that are trivial at the scalar uniformizer and on the central
elements of the level-`a` newvector subgroup. -/
def normalizedCentral (k a : ℕ) :
    Set (Subgroup.center (GeneralLinear (k + 1) K.Carrier) →* ℂˣ) :=
  {χ | χ (scalarToCenter K.canonicalTopologicalData.uniformizerUnit) = 1 ∧
    ∀ y : Subgroup.center (GeneralLinear (k + 1) K.Carrier),
      (y : GeneralLinear (k + 1) K.Carrier) ∈ Conductor.levelSubgroup K.Carrier k a → χ y = 1}

/-- There are finitely many normalized central characters of level `a`. -/
theorem normalizedCentral_finite (k a : ℕ) : (normalizedCentral K k a).Finite := by
  have := finite_quotient_levelCenter K k a
  have := CompactOpenFiniteness.finite_monoidHom_units (integralCenter K k ⧸ levelCenter K k a)
  let Φ : normalizedCentral K k a → (integralCenter K k ⧸ levelCenter K k a →* ℂˣ) :=
    fun χ => QuotientGroup.lift (levelCenter K k a)
      ((χ : Subgroup.center (GeneralLinear (k + 1) K.Carrier) →* ℂˣ).comp
        (integralCenter K k).subtype)
      (fun y hy => χ.property.2 _ hy)
  have hΦ : Function.Injective Φ := by
    intro χ χ' h
    apply Subtype.ext
    apply MonoidHom.ext
    intro y
    obtain ⟨m, y₀, hy₀, rfl⟩ := exists_uniformizer_zpow_mul K k y
    have h₀ : (χ : Subgroup.center (GeneralLinear (k + 1) K.Carrier) →* ℂˣ) y₀ =
        (χ' : Subgroup.center (GeneralLinear (k + 1) K.Carrier) →* ℂˣ) y₀ :=
      DFunLike.congr_fun h (QuotientGroup.mk (⟨y₀, hy₀⟩ : integralCenter K k))
    rw [map_mul, map_mul, map_zpow, map_zpow, χ.property.1, χ'.property.1, h₀]
  have : Finite (normalizedCentral K k a) := Finite.of_injective Φ hΦ
  exact Set.toFinite _

/-! ### The covering by central-level strata -/

/-- Every orbit in the stratum contains a class of level at most `a` whose central
character is normalized: twist by `z` with `z ^ (k + 1) = ω(ϖ)⁻¹`. -/
theorem supercuspidalOrbitStratum_subset (k a : ℕ) :
    supercuspidalOrbitStratum.{uK, uV} K k a ⊆
      ⋃ χ ∈ normalizedCentral K k a,
        (fun π => PadicSupercuspidal.unramifiedOrbitClass.{uK, uV} K ⟨k.succPNat, π⟩) ''
          GeneralLinear.SupercuspidalClass.centralLevelStratum.{uK, uV} χ a := by
  let T := K.canonicalTopologicalData
  rintro c ⟨π, rfl, hπ⟩
  obtain ⟨A, rfl⟩ : ∃ A : GeneralLinear.SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := k + 1),
      A.isoClass = π := Quotient.exists_rep π
  obtain ⟨ω, hω⟩ := exists_hasCentralCharacter K k A
  let c : ℂˣ := ω (scalarToCenter T.uniformizerUnit)
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((c⁻¹ : ℂˣ) : ℂ) (Nat.succ_pos k)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero k)] at hw
    exact (Units.ne_zero _) hw.symm
  let z : ℂˣ := Units.mk0 w hw0
  have hz : z ^ (k + 1) = c⁻¹ := Units.ext (by simp [z, hw])
  let χz := T.determinantUnramifiedCharacter (k + 1) z
  let A' := GeneralLinear.SupercuspidalRep.twist χz
    (T.isOpen_ker_determinantUnramifiedCharacter (k + 1) z)
    (T.ker_determinant_le_ker_determinantUnramifiedCharacter (k + 1) z) A
  let ω' : Subgroup.center (GeneralLinear (k + 1) K.Carrier) →* ℂˣ :=
    (χz.comp (Subgroup.center (GeneralLinear (k + 1) K.Carrier)).subtype) * ω
  have hω' : A'.obj.HasCentralCharacter ω' := by
    intro y v
    change (χz (y : GeneralLinear (k + 1) K.Carrier) : ℂ) •
        A.obj.representation (y : GeneralLinear (k + 1) K.Carrier) v =
      ((χz (y : GeneralLinear (k + 1) K.Carrier) * ω y : ℂˣ) : ℂ) • v
    rw [hω y v, Units.val_mul]
    exact (mul_smul (χz (y : GeneralLinear (k + 1) K.Carrier) : ℂ) (ω y : ℂ) v).symm
  have hfixA : fixedVectors A.obj.representation (Conductor.levelSubgroup K.Carrier k a) ≠ ⊥ := by
    have h : GeneralLinear.SupercuspidalClass.firstFixedLevel A.isoClass ≤ (a : WithTop ℕ) :=
      le_of_eq hπ
    exact (GeneralLinear.SupercuspidalClass.firstFixedLevel_le_iff _ a).mp h
  have hfixA' :
      fixedVectors A'.obj.representation (Conductor.levelSubgroup K.Carrier k a) ≠ ⊥ := by
    change fixedVectors (Langlands.twist χz A.obj.representation) _ ≠ ⊥
    rw [fixedVectors_twist_eq_of_le_ker χz _ _ (levelSubgroup_le_ker K k a z)]
    exact hfixA
  refine Set.mem_biUnion (x := ω') ⟨?_, ?_⟩ ⟨A'.isoClass, ⟨hω', ?_⟩, ?_⟩
  · change χz (GeneralLinear.scalar T.uniformizerUnit) * c = 1
    rw [T.determinantUnramifiedCharacter_scalar, T.unramifiedCharacter_uniformizer, hz,
      inv_mul_cancel]
  · intro y hy
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfixA'
    have h1 : A'.obj.representation (y : GeneralLinear (k + 1) K.Carrier) v = v := hv ⟨y, hy⟩
    rw [hω' y v] at h1
    have h2 : ((ω' y : ℂ) - 1) • v = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact Units.ext (sub_eq_zero.mp h)
    · exact absurd h hv0
  · exact (GeneralLinear.SupercuspidalClass.firstFixedLevel_le_iff _ a).mpr hfixA'
  · exact PadicSupercuspidal.unramifiedOrbitClass_twist K z ⟨k.succPNat, A.isoClass⟩

/-- Each orbit stratum is finite. -/
theorem supercuspidalOrbitStratum_finite (k a : ℕ) :
    (supercuspidalOrbitStratum.{uK, uV} K k a).Finite := by
  refine Set.Finite.subset ?_ (supercuspidalOrbitStratum_subset K k a)
  refine (normalizedCentral_finite K k a).biUnion fun χ _ => ?_
  exact (CompactOpenFiniteness.centralLevelStratum_finite.{uK, uV} K k χ a).image _

end Langlands.Henniart.OrbitStratumFiniteness

namespace Langlands.Henniart

universe uK uV

/-- Proof of `SupercuspidalOrbitStratumFinitenessStatement`. -/
theorem supercuspidalOrbitStratumFiniteness :
    SupercuspidalOrbitStratumFinitenessStatement.{uK, uV} :=
  fun _ _ K k a => OrbitStratumFiniteness.supercuspidalOrbitStratum_finite K k a

end Langlands.Henniart
