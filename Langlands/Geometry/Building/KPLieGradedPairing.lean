import Langlands.Geometry.Building.KPLieGradedAction

/-!
# The residue pairing between `𝔤*_{x,r}` and `𝔤_{x,-r}`

For supplied `L : P.LieFiltrationData` satisfying the periodicity `IsPeriodic`, the value `X(Y)` of
`X ∈ 𝔤*_{x,r}` on `Y ∈ 𝔤_{x,-r}` lies in `𝒪`. Reducing it modulo `𝔪` gives an `𝒪`-bilinear pairing
with values in the residue field `𝔣`. It vanishes when `X ∈ 𝔤*_{x,r+}` or `Y ∈ 𝔤_{x,(-r)+}`, so it
descends to the graded piece `𝔤_{x,-r}/𝔤_{x,(-r)+}`, and it is invariant under the stabilizer of
the filtration.

The graded pairing is nondegenerate: on the right if `𝔤_{x,-r}` is a lattice
(`eq_zero_of_forall_gradedLieDualPairing_eq_zero`), and on the left, with kernel `𝔤*_{x,r+}`, if
the filtration is left-continuous at `-r` (`gradedLieDualPairing_eq_zero_iff`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} {L : P.LieFiltrationData}

/-! ### Shifting the real-depth lattices by the maximal ideal -/

/-- Under periodicity, `𝔪 • 𝔤_{x,t} ⊆ 𝔤_{x,t+1}` for every real `t`. -/
theorem smul_mem_lieFiltrationReal_add_one (hL : L.IsPeriodic) {x : P.Apartment} {t : ℝ}
    {a : 𝒪[F]} (ha : a ∈ 𝓂[F]) {X : GenericLie 𝒪[F] G} (hX : X ∈ L.lieFiltrationReal x t) :
    a • X ∈ L.lieFiltrationReal x (t + 1) := by
  rw [mem_lieFiltrationReal] at hX ⊢
  intro b hb
  have hn : indexShift (t + 1) = indexShift t - 1 := by
    change ⌈-(t + 1)⌉₊ = ⌈-t⌉₊ - 1
    rw [neg_add, ← sub_eq_add_neg]
    exact Nat.ceil_sub_one _
  rcases Nat.eq_zero_or_pos (indexShift t) with h0 | hpos
  · have h1 : indexShift (t + 1) = 0 := by rw [hn, h0]
    have hs : shiftedIndex (t + 1) = shiftedIndex t + 1 := by
      apply NNReal.eq
      change (t + 1) + (indexShift (t + 1) : ℝ) = (t + (indexShift t : ℝ)) + 1
      rw [h0, h1]
      push_cast
      ring
    have hX0 : X ∈ L.lieFiltration x (shiftedIndex t) := by
      have h := hX 1 (by rw [h0, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
      rwa [one_smul] at h
    rw [hs, hL x]
    exact Submodule.smul_mem _ b (Submodule.smul_mem_smul ha hX0)
  · obtain ⟨k, hk⟩ : ∃ k, indexShift t = k + 1 := ⟨indexShift t - 1, by omega⟩
    have h1 : indexShift (t + 1) = k := by rw [hn, hk, Nat.add_sub_cancel]
    have hs : shiftedIndex (t + 1) = shiftedIndex t := by
      apply NNReal.eq
      change (t + 1) + (indexShift (t + 1) : ℝ) = t + (indexShift t : ℝ)
      rw [h1, hk]
      push_cast
      ring
    rw [hs, smul_smul]
    apply hX
    rw [h1] at hb
    rw [hk, pow_succ]
    exact Ideal.mul_mem_mul hb ha

/-! ### Integrality of the pairing -/

/-- Under periodicity, `X(Y) ∈ 𝒪` for `X ∈ 𝔤*_{x,r}` and `Y ∈ 𝔤_{x,-r}`. -/
theorem exists_integer_eq_apply (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    {X : Module.Dual F (GenericLie 𝒪[F] G)} (hX : X ∈ L.dualLieFiltration x r)
    {Y : GenericLie 𝒪[F] G} (hY : Y ∈ L.lieFiltrationReal x (-r)) :
    ∃ c : 𝒪[F], (c : F) = X Y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hϖm : ϖ ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hY' : ϖ • Y ∈ L.lieFiltrationReal x (-r + 1) :=
    smul_mem_lieFiltrationReal_add_one hL hϖm hY
  obtain ⟨m, hm, e⟩ := L.mem_dualLieFiltration.1 hX (-r + 1) (by linarith) _ hY'
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    Ideal.mem_span_singleton'] at hm
  obtain ⟨c, rfl⟩ := hm
  refine ⟨c, ?_⟩
  have hsmul : X (ϖ • Y) = (ϖ : F) * X Y := by
    have h := (X.restrictScalars 𝒪[F]).map_smul ϖ Y
    rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, Algebra.smul_def] at h
    exact h
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  apply mul_left_cancel₀ hϖ0
  rw [← hsmul, ← e]
  push_cast
  ring

/-- `X(Y) ∈ 𝔪` for `X ∈ 𝔤*_{x,r}` and `Y ∈ 𝔤_{x,(-r)+}`; this is the definition of `𝔤*_{x,r}`. -/
theorem exists_mem_maximalIdeal_eq_apply {x : P.Apartment} {r : ℝ}
    {X : Module.Dual F (GenericLie 𝒪[F] G)} (hX : X ∈ L.dualLieFiltration x r)
    {Y : GenericLie 𝒪[F] G} (hY : Y ∈ L.lieFiltrationPlusReal x (-r)) :
    ∃ m ∈ 𝓂[F], (m : F) = X Y :=
  (mem_dualPairingSubmodule X Y).1 (hX hY)

/-- `X(Y) ∈ 𝔪` for `X ∈ 𝔤*_{x,r+}` and `Y ∈ 𝔤_{x,-r}`. -/
theorem exists_mem_maximalIdeal_eq_apply_of_mem_dualLieFiltrationPlus {x : P.Apartment} {r : ℝ}
    {X : Module.Dual F (GenericLie 𝒪[F] G)} (hX : X ∈ L.dualLieFiltrationPlus x r)
    {Y : GenericLie 𝒪[F] G} (hY : Y ∈ L.lieFiltrationReal x (-r)) :
    ∃ m ∈ 𝓂[F], (m : F) = X Y := by
  obtain ⟨s, hs, hXs⟩ := L.mem_dualLieFiltrationPlus.1 hX
  exact L.mem_dualLieFiltration.1 hXs (-r) (by linarith) Y hY

variable (L)

/-- The element `X(Y)` of `𝒪`, for `X ∈ 𝔤*_{x,r}` and `Y ∈ 𝔤_{x,-r}` (under periodicity). -/
def pairingInteger (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ) (X : L.dualLieFiltration x r)
    (Y : L.lieFiltrationReal x (-r)) : 𝒪[F] :=
  Classical.choose (exists_integer_eq_apply hL X.2 Y.2)

variable {L}

theorem coe_pairingInteger (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    (X : L.dualLieFiltration x r) (Y : L.lieFiltrationReal x (-r)) :
    (L.pairingInteger hL x r X Y : F) = (X : Module.Dual F (GenericLie 𝒪[F] G)) Y :=
  Classical.choose_spec (exists_integer_eq_apply hL X.2 Y.2)

theorem pairingInteger_eq_iff (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    (X : L.dualLieFiltration x r) (Y : L.lieFiltrationReal x (-r)) (c : 𝒪[F]) :
    L.pairingInteger hL x r X Y = c ↔ (c : F) = (X : Module.Dual F (GenericLie 𝒪[F] G)) Y := by
  rw [← coe_pairingInteger hL X Y]
  exact ⟨fun h => by rw [h], fun h => (Subtype.ext h).symm⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem apply_smul_eq (X : Module.Dual F (GenericLie 𝒪[F] G)) (c : 𝒪[F])
    (Y : GenericLie 𝒪[F] G) : X (c • Y) = (c : F) * X Y := by
  have h := (X.restrictScalars 𝒪[F]).map_smul c Y
  rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, Algebra.smul_def] at h
  exact h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem smul_apply_eq (X : Module.Dual F (GenericLie 𝒪[F] G)) (c : 𝒪[F])
    (Y : GenericLie 𝒪[F] G) : (c • X) Y = (c : F) * X Y := by
  rw [LinearMap.smul_apply, Algebra.smul_def]
  rfl

/-! ### The pairing with values in the residue field -/

variable (L)

/-- The residue pairing `𝔤*_{x,r} × 𝔤_{x,-r} → 𝔣`, `(X, Y) ↦ X(Y) mod 𝔪`, under periodicity. -/
def lieDualPairing (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ) :
    L.dualLieFiltration x r →ₗ[𝒪[F]] L.lieFiltrationReal x (-r) →ₗ[𝒪[F]] 𝓀[F] :=
  LinearMap.mk₂ 𝒪[F] (fun X Y => IsLocalRing.residue 𝒪[F] (L.pairingInteger hL x r X Y))
    (fun X X' Y => by
      rw [← map_add]
      congr 1
      rw [pairingInteger_eq_iff]
      push_cast
      rw [coe_pairingInteger, coe_pairingInteger]
      rfl)
    (fun c X Y => by
      rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, ← map_mul]
      congr 1
      rw [pairingInteger_eq_iff]
      push_cast
      rw [coe_pairingInteger, smul_apply_eq])
    (fun X Y Y' => by
      rw [← map_add]
      congr 1
      rw [pairingInteger_eq_iff]
      push_cast
      rw [coe_pairingInteger, coe_pairingInteger, map_add])
    (fun c X Y => by
      rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, ← map_mul]
      congr 1
      rw [pairingInteger_eq_iff]
      push_cast
      rw [coe_pairingInteger, apply_smul_eq])

variable {L}

/-- The pairing is the residue of the integer `X(Y)`. -/
theorem lieDualPairing_apply (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    (X : L.dualLieFiltration x r) (Y : L.lieFiltrationReal x (-r)) {c : 𝒪[F]}
    (hc : (c : F) = (X : Module.Dual F (GenericLie 𝒪[F] G)) Y) :
    L.lieDualPairing hL x r X Y = IsLocalRing.residue 𝒪[F] c := by
  change IsLocalRing.residue 𝒪[F] (L.pairingInteger hL x r X Y) = _
  rw [(pairingInteger_eq_iff hL X Y c).2 hc]

theorem lieDualPairing_eq_zero_of_exists (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    (X : L.dualLieFiltration x r) (Y : L.lieFiltrationReal x (-r))
    (h : ∃ m ∈ 𝓂[F], (m : F) = (X : Module.Dual F (GenericLie 𝒪[F] G)) Y) :
    L.lieDualPairing hL x r X Y = 0 := by
  obtain ⟨m, hm, e⟩ := h
  rw [lieDualPairing_apply hL X Y e]
  exact (IsLocalRing.residue_eq_zero_iff m).2 hm

/-- The pairing vanishes on `𝔤*_{x,r} × 𝔤_{x,(-r)+}`. -/
theorem lieDualPairing_eq_zero_of_mem_lieFiltrationPlusReal (hL : L.IsPeriodic) {x : P.Apartment}
    {r : ℝ} (X : L.dualLieFiltration x r) (Y : L.lieFiltrationReal x (-r))
    (hY : (Y : GenericLie 𝒪[F] G) ∈ L.lieFiltrationPlusReal x (-r)) :
    L.lieDualPairing hL x r X Y = 0 :=
  lieDualPairing_eq_zero_of_exists hL X Y (exists_mem_maximalIdeal_eq_apply X.2 hY)

/-- The pairing vanishes on `𝔤*_{x,r+} × 𝔤_{x,-r}`. -/
theorem lieDualPairing_eq_zero_of_mem_dualLieFiltrationPlus (hL : L.IsPeriodic)
    {x : P.Apartment} {r : ℝ} (X : L.dualLieFiltration x r) (Y : L.lieFiltrationReal x (-r))
    (hX : (X : Module.Dual F (GenericLie 𝒪[F] G)) ∈ L.dualLieFiltrationPlus x r) :
    L.lieDualPairing hL x r X Y = 0 :=
  lieDualPairing_eq_zero_of_exists hL X Y
    (exists_mem_maximalIdeal_eq_apply_of_mem_dualLieFiltrationPlus hX Y.2)

/-- The pairing is invariant under the stabilizer of the filtration:
`⟨g X, g Y⟩ = ⟨X, Y⟩` for the coadjoint and adjoint actions. -/
theorem lieDualPairing_coadjoint (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    (g : L.filtrationStabilizer x) (X : L.dualLieFiltration x r) (Y : L.lieFiltrationReal x (-r)) :
    L.lieDualPairing hL x r ⟨coadjoint g.1 X, coadjoint_mem_dualLieFiltration g.2 X.2⟩
        ⟨GenericLie.adjoint 𝒪[F] g.1 Y, adjoint_mem_lieFiltrationReal g.2 Y.2⟩ =
      L.lieDualPairing hL x r X Y := by
  refine lieDualPairing_apply hL _ _ ?_
  change _ = (X : Module.Dual F (GenericLie 𝒪[F] G))
    (GenericLie.adjoint 𝒪[F] g.1⁻¹ (GenericLie.adjoint 𝒪[F] g.1 Y))
  rw [← adjointF_apply, ← adjointF_apply, adjointF_inv_apply, coe_pairingInteger]

/-! ### Descent to the graded piece `𝔤_{x,-r}/𝔤_{x,(-r)+}` -/

variable (L)

/-- The residue pairing `𝔤*_{x,r} × 𝔤_{x,-r}/𝔤_{x,(-r)+} → 𝔣`, under periodicity. -/
def gradedLieDualPairing (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ) :
    L.dualLieFiltration x r →ₗ[𝒪[F]] L.gradedLie x (-r) →ₗ[𝒪[F]] 𝓀[F] where
  toFun X := Submodule.liftQ _ (L.lieDualPairing hL x r X) fun Y hY =>
    lieDualPairing_eq_zero_of_mem_lieFiltrationPlusReal hL X Y hY
  map_add' X X' := Submodule.linearMap_qext _ (LinearMap.ext fun Y => by
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply, map_add,
      LinearMap.add_apply]
    rfl)
  map_smul' c X := Submodule.linearMap_qext _ (LinearMap.ext fun Y => by
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply, map_smul,
      LinearMap.smul_apply, RingHom.id_apply]
    rfl)

variable {L}

theorem gradedLieDualPairing_mk (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    (X : L.dualLieFiltration x r) (Y : L.lieFiltrationReal x (-r)) :
    L.gradedLieDualPairing hL x r X (Submodule.Quotient.mk Y) = L.lieDualPairing hL x r X Y :=
  rfl

/-- The graded pairing vanishes on `𝔤*_{x,r+}`. -/
theorem gradedLieDualPairing_eq_zero_of_mem_dualLieFiltrationPlus (hL : L.IsPeriodic)
    {x : P.Apartment} {r : ℝ} (X : L.dualLieFiltration x r) (Y : L.gradedLie x (-r))
    (hX : (X : Module.Dual F (GenericLie 𝒪[F] G)) ∈ L.dualLieFiltrationPlus x r) :
    L.gradedLieDualPairing hL x r X Y = 0 := by
  induction Y using Submodule.Quotient.induction_on with
  | H Y => exact lieDualPairing_eq_zero_of_mem_dualLieFiltrationPlus hL X Y hX

/-- The graded pairing is invariant under the stabilizer of the filtration. -/
theorem gradedLieDualPairing_gradedAdjoint (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    (g : L.filtrationStabilizer x) (X : L.dualLieFiltration x r) (Y : L.gradedLie x (-r)) :
    L.gradedLieDualPairing hL x r ⟨coadjoint g.1 X, coadjoint_mem_dualLieFiltration g.2 X.2⟩
        (L.gradedAdjoint x (-r) g Y) =
      L.gradedLieDualPairing hL x r X Y := by
  induction Y using Submodule.Quotient.induction_on with
  | H Y => exact lieDualPairing_coadjoint hL g X Y


/-! ### Nondegeneracy -/

/-- Under periodicity, `𝔪 • 𝔤_{x,t} ⊆ 𝔤_{x,t+}`. -/
theorem smul_mem_lieFiltrationPlusReal (hL : L.IsPeriodic) {x : P.Apartment} {t : ℝ}
    {a : 𝒪[F]} (ha : a ∈ 𝓂[F]) {Y : GenericLie 𝒪[F] G} (hY : Y ∈ L.lieFiltrationReal x t) :
    a • Y ∈ L.lieFiltrationPlusReal x t :=
  L.lieFiltrationReal_le_lieFiltrationPlusReal x (lt_add_one t)
    (smul_mem_lieFiltrationReal_add_one hL ha hY)

/-- Under periodicity, `𝔪` kills the graded piece `𝔤_{x,t}/𝔤_{x,t+}`. -/
theorem isTorsionBySet_gradedLie (hL : L.IsPeriodic) (x : P.Apartment) (t : ℝ) :
    Module.IsTorsionBySet 𝒪[F] (L.gradedLie x t) (𝓂[F] : Set 𝒪[F]) := by
  intro Y a
  induction Y using Submodule.Quotient.induction_on with
  | H Y =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact smul_mem_lieFiltrationPlusReal hL a.2 Y.2

/-- Under periodicity, a nonzero element of `𝔤_{x,t}/𝔤_{x,t+}` is detected by an `𝒪`-linear map
to the residue field: the graded piece is a vector space over `𝔣`. -/
theorem exists_linearMap_residueField_ne_zero (hL : L.IsPeriodic) {x : P.Apartment} {t : ℝ}
    {Y : L.gradedLie x t} (hY : Y ≠ 0) :
    ∃ φ : L.gradedLie x t →ₗ[𝒪[F]] 𝓀[F], φ Y ≠ 0 := by
  have hT := isTorsionBySet_gradedLie hL x t
  let _ := hT.module
  have _ := hT.isScalarTower (S := 𝒪[F])
  let _ : Field (𝒪[F] ⧸ 𝓂[F]) := Ideal.Quotient.field _
  have _ : Module.Free (𝒪[F] ⧸ 𝓂[F]) (L.gradedLie x t) := Module.Free.of_divisionRing _ _
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (𝒪[F] ⧸ 𝓂[F]) (L.gradedLie x t), φ Y ≠ 0 := by
    by_contra h
    exact hY ((Module.forall_dual_apply_eq_zero_iff _ Y).1 fun φ => not_not.1 fun hne => h ⟨φ, hne⟩)
  exact ⟨φ.restrictScalars 𝒪[F], hφ⟩

/-- Surjectivity: under periodicity, if `𝔤_{x,-r}` is a lattice, every `𝒪`-linear map
`φ : 𝔤_{x,-r}/𝔤_{x,(-r)+} → 𝔣` is the graded pairing with some `X ∈ 𝔤*_{x,r}`. The proof lifts
`φ` to an `𝒪`-linear form on the free module `𝔤_{x,-r}` and extends it `F`-linearly to `𝔤`. -/
theorem gradedLieDualPairing_surjective (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    [Submodule.IsLattice F (L.lieFiltrationReal x (-r))] :
    Function.Surjective (L.gradedLieDualPairing hL x r) := by
  intro φ
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (Algebra.linearMap 𝒪[F] 𝓀[F])
    (φ ∘ₗ Submodule.mkQ _) IsLocalRing.residue_surjective
  have hres : ∀ m : L.lieFiltrationReal x (-r),
      IsLocalRing.residue 𝒪[F] (l m) = φ (Submodule.Quotient.mk m) := by
    intro m
    have h := LinearMap.congr_fun hl m
    rw [LinearMap.comp_apply, Algebra.linearMap_apply, IsLocalRing.ResidueField.algebraMap_eq]
      at h
    exact h
  let b := Module.Free.chooseBasis 𝒪[F] (L.lieFiltrationReal x (-r))
  let B := b.extendOfIsLattice F
  let X : Module.Dual F (GenericLie 𝒪[F] G) := B.constr F fun i => ((l (b i) : 𝒪[F]) : F)
  have hX : ∀ m : L.lieFiltrationReal x (-r), X m = ((l m : 𝒪[F]) : F) := by
    have h : (X.restrictScalars 𝒪[F]) ∘ₗ (L.lieFiltrationReal x (-r)).subtype =
        (Algebra.linearMap 𝒪[F] F) ∘ₗ l := by
      refine b.ext fun i => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.restrictScalars_apply, ← Module.Basis.extendOfIsLattice_apply F b i,
        Module.Basis.constr_basis]
      rfl
    intro m
    exact LinearMap.congr_fun h m
  have hXmem : X ∈ L.dualLieFiltration x r := by
    change L.lieFiltrationPlusReal x (-r) ≤ dualPairingSubmodule X
    intro Z hZ
    have hZN : Z ∈ L.lieFiltrationReal x (-r) := L.lieFiltrationPlusReal_le hL x (-r) hZ
    refine (mem_dualPairingSubmodule X Z).2 ⟨l ⟨Z, hZN⟩, ?_, (hX ⟨Z, hZN⟩).symm⟩
    rw [← IsLocalRing.residue_eq_zero_iff, hres,
      (Submodule.Quotient.mk_eq_zero _).2 (show (⟨Z, hZN⟩ : L.lieFiltrationReal x (-r)) ∈
        (L.lieFiltrationPlusReal x (-r)).comap (L.lieFiltrationReal x (-r)).subtype from hZ),
      map_zero]
  refine ⟨⟨X, hXmem⟩, Submodule.linearMap_qext _ (LinearMap.ext fun Y => ?_)⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, gradedLieDualPairing_mk,
    lieDualPairing_apply hL ⟨X, hXmem⟩ Y (hX Y).symm, hres]

/-- Under periodicity, if `𝔤_{x,-r}` is a lattice and `Y ∈ 𝔤_{x,-r}` is not in `𝔤_{x,(-r)+}`,
some `X ∈ 𝔤*_{x,r}` has `X(Y) ∈ 𝒪` with nonzero residue. -/
theorem exists_mem_dualLieFiltration_residue_ne_zero (hL : L.IsPeriodic) {x : P.Apartment}
    {r : ℝ} [Submodule.IsLattice F (L.lieFiltrationReal x (-r))] (Y : L.lieFiltrationReal x (-r))
    (hY : (Y : GenericLie 𝒪[F] G) ∉ L.lieFiltrationPlusReal x (-r)) :
    ∃ X ∈ L.dualLieFiltration x r, ∃ c : 𝒪[F],
      (c : F) = X Y ∧ IsLocalRing.residue 𝒪[F] c ≠ 0 := by
  have hY0 : (Submodule.Quotient.mk Y : L.gradedLie x (-r)) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hY
  obtain ⟨φ, hφ⟩ := exists_linearMap_residueField_ne_zero hL hY0
  obtain ⟨X, hX⟩ := gradedLieDualPairing_surjective hL φ
  obtain ⟨c, hc⟩ := exists_integer_eq_apply hL X.2 Y.2
  refine ⟨X, X.2, c, hc, ?_⟩
  rw [← lieDualPairing_apply hL X Y hc, ← gradedLieDualPairing_mk, hX]
  exact hφ

/-- Right nondegeneracy: under periodicity, if `𝔤_{x,-r}` is a lattice, an element of
`𝔤_{x,-r}/𝔤_{x,(-r)+}` on which the pairing with every `X ∈ 𝔤*_{x,r}` vanishes is zero. -/
theorem eq_zero_of_forall_gradedLieDualPairing_eq_zero (hL : L.IsPeriodic) {x : P.Apartment}
    {r : ℝ} [Submodule.IsLattice F (L.lieFiltrationReal x (-r))] {Y : L.gradedLie x (-r)}
    (h : ∀ X, L.gradedLieDualPairing hL x r X Y = 0) : Y = 0 := by
  induction Y using Submodule.Quotient.induction_on with
  | H Y =>
    by_contra hne
    rw [Submodule.Quotient.mk_eq_zero] at hne
    obtain ⟨X, hX, c, hc, hres⟩ := exists_mem_dualLieFiltration_residue_ne_zero hL Y hne
    apply hres
    rw [← lieDualPairing_apply hL ⟨X, hX⟩ Y hc]
    exact h ⟨X, hX⟩

/-- Right nondegeneracy as a kernel: the flipped pairing
`𝔤_{x,-r}/𝔤_{x,(-r)+} → (𝔤*_{x,r} → 𝔣)` is injective. -/
theorem ker_gradedLieDualPairing_flip (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    [Submodule.IsLattice F (L.lieFiltrationReal x (-r))] :
    LinearMap.ker (L.gradedLieDualPairing hL x r).flip = ⊥ :=
  (Submodule.eq_bot_iff _).2 fun _ hY => eq_zero_of_forall_gradedLieDualPairing_eq_zero hL
    fun X => LinearMap.congr_fun (LinearMap.mem_ker.1 hY) X

/-- `𝔤_{x,(-r)+}` is the annihilator of `𝔤*_{x,r}` inside `𝔤_{x,-r}`: under periodicity, if
`𝔤_{x,-r}` is a lattice, `Y ∈ 𝔤_{x,-r}` lies in `𝔤_{x,(-r)+}` if and only if `X(Y) ∈ 𝔪` for every
`X ∈ 𝔤*_{x,r}`. -/
theorem mem_lieFiltrationPlusReal_iff_forall_dual (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    [Submodule.IsLattice F (L.lieFiltrationReal x (-r))] {Y : GenericLie 𝒪[F] G}
    (hY : Y ∈ L.lieFiltrationReal x (-r)) :
    Y ∈ L.lieFiltrationPlusReal x (-r) ↔
      ∀ X ∈ L.dualLieFiltration x r, ∃ m ∈ 𝓂[F], (m : F) = X Y := by
  refine ⟨fun h X hX => exists_mem_maximalIdeal_eq_apply hX h, fun h => ?_⟩
  by_contra hne
  obtain ⟨X, hX, c, hc, hres⟩ := exists_mem_dualLieFiltration_residue_ne_zero hL ⟨Y, hY⟩ hne
  obtain ⟨m, hm, e⟩ := h X hX
  have hcm : c = m := Subtype.ext (hc.trans e.symm)
  exact hres ((IsLocalRing.residue_eq_zero_iff c).2 (hcm ▸ hm))

/-- The left kernel of the graded pairing: `X ∈ 𝔤*_{x,r}` pairs to zero with
`𝔤_{x,-r}/𝔤_{x,(-r)+}` if and only if `X(Y) ∈ 𝔪` for every `Y ∈ 𝔤_{x,-r}`. -/
theorem gradedLieDualPairing_eq_zero_iff_forall (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    (X : L.dualLieFiltration x r) :
    L.gradedLieDualPairing hL x r X = 0 ↔
      ∀ Y ∈ L.lieFiltrationReal x (-r), ∃ m ∈ 𝓂[F],
        (m : F) = (X : Module.Dual F (GenericLie 𝒪[F] G)) Y := by
  constructor
  · intro h Y hY
    obtain ⟨c, hc⟩ := exists_integer_eq_apply hL X.2 hY
    have h0 : L.lieDualPairing hL x r X ⟨Y, hY⟩ = 0 :=
      LinearMap.congr_fun h (Submodule.Quotient.mk ⟨Y, hY⟩)
    rw [lieDualPairing_apply hL X ⟨Y, hY⟩ hc] at h0
    exact ⟨c, (IsLocalRing.residue_eq_zero_iff c).1 h0, hc⟩
  · intro h
    refine LinearMap.ext fun Y => ?_
    induction Y using Submodule.Quotient.induction_on with
    | H Y => exact lieDualPairing_eq_zero_of_exists hL X Y (h Y Y.2)

/-! ### The left kernel under left continuity (`IsLeftContinuousAt`, `KPLieGradedAction`) -/

/-- Under periodicity and left continuity at `-r`, a linear form with `X(𝔤_{x,-r}) ⊆ 𝔪` lies in
`𝔤*_{x,r+}`. -/
theorem mem_dualLieFiltrationPlus_of_forall (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    (hc : L.IsLeftContinuousAt x (-r)) {X : Module.Dual F (GenericLie 𝒪[F] G)}
    (hX : ∀ Y ∈ L.lieFiltrationReal x (-r), ∃ m ∈ 𝓂[F], (m : F) = X Y) :
    X ∈ L.dualLieFiltrationPlus x r := by
  obtain ⟨s, hs, hle⟩ := exists_lieFiltrationPlusReal_le hL hc
  refine L.mem_dualLieFiltrationPlus.2 ⟨-s, by linarith, ?_⟩
  change L.lieFiltrationPlusReal x (-(-s)) ≤ dualPairingSubmodule X
  rw [neg_neg]
  intro Y hY
  exact (mem_dualPairingSubmodule X Y).2 (hX Y (hle hY))

/-- Left nondegeneracy: under periodicity and left continuity at `-r`, `X ∈ 𝔤*_{x,r}` pairs to
zero with `𝔤_{x,-r}/𝔤_{x,(-r)+}` if and only if `X ∈ 𝔤*_{x,r+}`. -/
theorem gradedLieDualPairing_eq_zero_iff (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    (hc : L.IsLeftContinuousAt x (-r)) (X : L.dualLieFiltration x r) :
    L.gradedLieDualPairing hL x r X = 0 ↔
      (X : Module.Dual F (GenericLie 𝒪[F] G)) ∈ L.dualLieFiltrationPlus x r := by
  rw [gradedLieDualPairing_eq_zero_iff_forall hL X]
  refine ⟨mem_dualLieFiltrationPlus_of_forall hL hc, fun h Y hY => ?_⟩
  exact exists_mem_maximalIdeal_eq_apply_of_mem_dualLieFiltrationPlus h hY

/-- Left nondegeneracy as a kernel: the kernel of the graded pairing on `𝔤*_{x,r}` is
`𝔤*_{x,r+}`. -/
theorem ker_gradedLieDualPairing (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    (hc : L.IsLeftContinuousAt x (-r)) :
    LinearMap.ker (L.gradedLieDualPairing hL x r) =
      (L.dualLieFiltrationPlus x r).comap (L.dualLieFiltration x r).subtype := by
  ext X
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  exact gradedLieDualPairing_eq_zero_iff hL hc X

end Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData
