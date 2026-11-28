import Langlands.Correspondence.HenniartLadicClasses
import Langlands.Weil.Local.SepClosedTopology
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # Unramified ℓ-adic Galois characters and their Frobenius values -/

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology

namespace Langlands.Henniart.LocalNumerical

open Weil.Local.SepClosed

private def normOneUnits (F : Type*) [NormedField F] : Subgroup Fˣ :=
  ((normHom : F →*₀ ℝ).toMonoidHom.comp (Units.coeHom F)).ker

private theorem compactSpace_normOneUnits (F : Type*) [NormedField F] [ProperSpace F] :
    CompactSpace (normOneUnits F) := by
  apply isCompact_iff_compactSpace.mp
  have hS : IsCompact {x : F | ‖x‖ = 1} := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : F) 1
  change IsCompact (Units.val ⁻¹' {x : F | ‖x‖ = 1})
  apply Units.isEmbedding_val₀.isInducing.isCompact_preimage' hS
  intro x hx
  exact ⟨Units.mk0 x (by intro h; simp [h] at hx), rfl⟩

/-- A continuous character of a compact group into a normed field has
norm one at every group element. -/
theorem norm_eq_one_of_compact_character {G F : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [NormedField F] (χ : G →ₜ* Fˣ) (g : G) : ‖(χ g : F)‖ = 1 := by
  obtain ⟨r, hr⟩ := (isCompact_range
    (continuous_norm.comp (Units.continuous_val.comp χ.continuous))).bddAbove
  have hle (x : G) : ‖(χ x : F)‖ ≤ 1 := by
    apply le_of_not_gt
    intro hx
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt r hx
    have hb : ‖(χ (x ^ m) : F)‖ ≤ r := hr ⟨x ^ m, rfl⟩
    apply (not_lt_of_ge hb)
    simpa only [map_pow, Units.val_pow_eq_pow_val, norm_pow] using hm
  have hinv := hle g⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at hinv
  exact le_antisymm (hle g)
    ((inv_le_one₀ (norm_pos_iff.mpr (χ g).ne_zero)).mp hinv)

variable (ℓ : ℕ) [Fact ℓ.Prime]

local notation "E" => PadicAlgCl ℓ

/-- The ℓ-adic units of norm one in the algebraic closure. -/
abbrev ladicUnitSphere : Subgroup Eˣ := normOneUnits E

@[simp] theorem mem_ladicUnitSphere (a : Eˣ) :
    a ∈ ladicUnitSphere ℓ ↔ ‖(a : E)‖ = 1 := Iff.rfl

private theorem exists_ladicProfiniteIntegerPowers (a : Eˣ) (ha : ‖(a : E)‖ = 1) :
    ∃ χ : Weil.ProfiniteIntegers →ₜ* Eˣ,
      (∀ n : Weil.Degree, χ (Weil.frobenius n) = a ^ n.toAdd) ∧
      ∃ L : IntermediateField ℚ_[ℓ] E, FiniteDimensional ℚ_[ℓ] L ∧
        ∀ z, (χ z : E) ∈ L := by
  let L := IntermediateField.adjoin ℚ_[ℓ] ({(a : E)} : Set E)
  let : FiniteDimensional ℚ_[ℓ] L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  let : ProperSpace L := FiniteDimensional.proper ℚ_[ℓ] L
  let U := normOneUnits L
  let : CompactSpace U := compactSpace_normOneUnits L
  have hU : IsEmbedding (fun x : U => ((x : Lˣ) : L)) :=
    Units.isEmbedding_val₀.comp IsEmbedding.subtypeVal
  let : TotallyDisconnectedSpace U :=
    hU.isTotallyDisconnected_range.mp (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  let v : L := ⟨a, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩
  let vU : U := ⟨Units.mk0 v (fun h => a.ne_zero (congrArg Subtype.val h)), ha⟩
  let P := ProfiniteGrp.of U
  let f : GrpCat.of Weil.Degree ⟶ (forget₂ ProfiniteGrp GrpCat).obj P :=
    GrpCat.ofHom (zpowersHom U vU)
  let F : Weil.ProfiniteIntegers →ₜ* U := (ProfiniteGrp.ProfiniteCompletion.lift f).hom
  have hF (n : Weil.Degree) : F (Weil.frobenius n) = vU ^ n.toAdd :=
    congrArg (fun t : GrpCat.of Weil.Degree ⟶ (forget₂ ProfiniteGrp GrpCat).obj P => t.hom n)
      (ProfiniteGrp.ProfiniteCompletion.lift_eta f)
  let j : U →ₜ* Eˣ :=
    ⟨(Units.map L.val.toMonoidHom).comp U.subtype,
      (continuous_subtype_val.units_map L.val.toMonoidHom).comp continuous_subtype_val⟩
  have hj : j vU = a := Units.ext rfl
  refine ⟨j.comp F, fun n => ?_, L, inferInstance, fun z => ?_⟩
  · change j (F (Weil.frobenius n)) = a ^ n.toAdd
    rw [hF, map_zpow, hj]
  · exact ((F z : Lˣ) : L).property

universe uK uΩ

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [IsSepClosed Ω]

/-- The unramified ℓ-adic character with the given norm-one value at
geometric Frobenius. -/
def ladicUnramifiedCharacter (a : ladicUnitSphere ℓ) : ladicUnramifiedCharacters K Ω ℓ := by
  let h := exists_ladicProfiniteIntegerPowers ℓ a.val a.property
  refine ⟨h.choose.comp (localResidueDegree K Ω), ?_, ?_⟩
  · intro i
    have hi : (i : Ω ≃ₐ[K] Ω) ∈ (localResidueDegree K Ω).toMonoidHom.ker := by
      rw [localResidueDegree_ker]
      exact i.property
    change localResidueDegree K Ω i = 1 at hi
    change h.choose (localResidueDegree K Ω i) = 1
    rw [hi, map_one]
  · obtain ⟨L, hL, hvals⟩ := h.choose_spec.2
    exact ⟨L, hL, fun g => hvals (localResidueDegree K Ω g)⟩

@[simp] theorem ladicUnramifiedCharacter_localProjection (a : ladicUnitSphere ℓ)
    (w : localWeilGroup K Ω) :
    (ladicUnramifiedCharacter ℓ K Ω a).val (localProjection K Ω w) =
      a.val ^ localDegreeInt K Ω w := by
  change (exists_ladicProfiniteIntegerPowers ℓ a.val a.property).choose
    (localResidueDegree K Ω (localProjection K Ω w)) = _
  rw [show localResidueDegree K Ω (localProjection K Ω w) =
    Weil.frobenius (localDegree K Ω w) from w.property]
  exact (exists_ladicProfiniteIntegerPowers ℓ a.val a.property).choose_spec.1 _

/-- An unramified ℓ-adic Galois character restricts to integer powers of
its value at geometric Frobenius. -/
theorem ladicUnramifiedCharacter_value_on_Weil (χ : ladicUnramifiedCharacters K Ω ℓ)
    (w : localWeilGroup K Ω) :
    χ.val (localProjection K Ω w) =
      χ.val (localProjection K Ω (localGeometricFrobenius K Ω)) ^ localDegreeInt K Ω w := by
  let w₀ := localGeometricFrobenius K Ω
  have hd : localDegree K Ω (w₀ ^ localDegreeInt K Ω w) = localDegree K Ω w := by
    rw [map_zpow, localGeometricFrobenius_degree]
    apply Multiplicative.toAdd.injective
    simp [localDegreeInt]
  have hi : w / w₀ ^ localDegreeInt K Ω w ∈ localInertia K Ω := by
    change localDegree K Ω (w / w₀ ^ localDegreeInt K Ω w) = 1
    rw [map_div, hd, div_self']
  have hχ := χ.property.1 ⟨_, localProjection_mem_absoluteInertia K Ω hi⟩
  change χ.val (localProjection K Ω (w / w₀ ^ localDegreeInt K Ω w)) = 1 at hχ
  rw [map_div, map_zpow, map_div, map_zpow] at hχ
  exact div_eq_one.mp hχ

/-- Evaluation at geometric Frobenius identifies the unramified ℓ-adic
Galois characters with the ℓ-adic units of norm one. -/
def ladicUnramifiedCharacterEquiv :
    ladicUnramifiedCharacters K Ω ℓ ≃* ladicUnitSphere ℓ where
  toFun χ := ⟨χ.val (localProjection K Ω (localGeometricFrobenius K Ω)),
    (mem_ladicUnitSphere ℓ _).mpr (norm_eq_one_of_compact_character χ.val _)⟩
  invFun := ladicUnramifiedCharacter ℓ K Ω
  left_inv χ := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro g
    let a : ladicUnitSphere ℓ :=
      ⟨χ.val (localProjection K Ω (localGeometricFrobenius K Ω)),
        (mem_ladicUnitSphere ℓ _).mpr (norm_eq_one_of_compact_character χ.val _)⟩
    change (ladicUnramifiedCharacter ℓ K Ω a).val g = χ.val g
    apply congrFun ((localProjection_denseRange K Ω).equalizer
      (ladicUnramifiedCharacter ℓ K Ω a).val.continuous χ.val.continuous ?_) g
    funext w
    change (ladicUnramifiedCharacter ℓ K Ω a).val (localProjection K Ω w) =
      χ.val (localProjection K Ω w)
    rw [ladicUnramifiedCharacter_localProjection]
    exact (ladicUnramifiedCharacter_value_on_Weil ℓ K Ω χ w).symm
  right_inv a := by
    apply Subtype.ext
    change (ladicUnramifiedCharacter ℓ K Ω a).val
      (localProjection K Ω (localGeometricFrobenius K Ω)) = a.val
    simp [localDegreeInt, localGeometricFrobenius_degree]
  map_mul' _ _ := rfl

end Langlands.Henniart.LocalNumerical
