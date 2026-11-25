import Langlands.LocalFactor.Ramification.CloseFieldsStatement
import Langlands.LocalFactor.Ramification.Wintenberger.Comparison
import Langlands.LocalFactor.Ramification.Wintenberger.KummerTower
import Langlands.LocalFactor.Ramification.Herbrand.InertiaProof

/-!
# Proof of the close-fields comparison of Galois quotients

For a `p`-adic field `F` with absolute ramification index `e`, the quotients `G_F/G_F^e` and
`G_X/G_X^e`, `X = k((t))` over the residue field `k` of `F`, are isomorphic as topological groups,
compatibly with the upper filtrations up to `e`. The proof follows Wintenberger's field of norms of
the Kummer tower `F(ϖ^{1/p^∞})`.
-/

noncomputable section

namespace Langlands.Ramification.Local

universe u

section QuotientIso

variable {A G : Type*} [Group A] [TopologicalSpace A] [CompactSpace A]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A continuous homomorphism `ι : A → G` from a compact group, whose image together with `F_G x`
generates `G` and which pulls `F_G y` back to `F_A y` for `a₀ ≤ y ≤ x`, induces a topological
isomorphism `A/F_A x ≃ G/F_G x`, the class of `a` going to the class of `ι a`, carrying the image of
`F_A y` onto the image of `F_G y`. -/
theorem exists_quotientIso_of_comap (ι : A →* G) (hι : Continuous ι) (FA : ℝ → Subgroup A)
    (FG : ℝ → Subgroup G) {a₀ x : ℝ} (ha₀ : a₀ ≤ x) [(FA x).Normal] [(FG x).Normal]
    [IsClosed (FG x : Set G)] (hanti : ∀ y : ℝ, y ≤ x → FG x ≤ FG y)
    (hcomap : ∀ y : ℝ, a₀ ≤ y → y ≤ x → (FG y).comap ι = FA y)
    (hsplit : ∀ g : G, ∃ a : A, ∃ n ∈ FG x, ι a * n = g) :
    ∃ φ : (A ⧸ FA x) ≃ₜ* (G ⧸ FG x), (∀ y : ℝ, a₀ ≤ y → y ≤ x →
      ((FA y).map (QuotientGroup.mk' (FA x))).map φ.toMulEquiv.toMonoidHom =
        (FG y).map (QuotientGroup.mk' (FG x))) ∧
      ∀ a : A, φ (QuotientGroup.mk a) = QuotientGroup.mk (ι a) := by
  let f := (QuotientGroup.mk' (FG x)).comp ι
  have hker : FA x = f.ker :=
    calc FA x = (FG x).comap ι := (hcomap x ha₀ le_rfl).symm
      _ = (QuotientGroup.mk' (FG x)).ker.comap ι :=
        congrArg (Subgroup.comap ι) (QuotientGroup.ker_mk' _).symm
      _ = f.ker := MonoidHom.comap_ker _ _
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, n, hn, han⟩ := hsplit g
    exact ⟨a, (QuotientGroup.mk'_eq_mk' _).mpr ⟨n, hn, han⟩⟩
  let e := QuotientGroup.liftEquiv (FA x) hsurj hker
  have hcont : Continuous e :=
    (QuotientGroup.isQuotientMap_mk (FA x)).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp hι)
  let φ : (A ⧸ FA x) ≃ₜ* (G ⧸ FG x) :=
    { toMulEquiv := e
      continuous_toFun := hcont
      continuous_invFun := hcont.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) }
  refine ⟨φ, fun y hy hyx => ?_, fun a => rfl⟩
  rw [Subgroup.map_map]
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨ι a, ?_, rfl⟩
    rw [SetLike.mem_coe, ← hcomap y hy hyx, Subgroup.mem_comap] at ha
    exact ha
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, n, hn, han⟩ := hsplit g
    refine ⟨a, ?_, ?_⟩
    · rw [SetLike.mem_coe, ← hcomap y hy hyx, Subgroup.mem_comap]
      have hm := (FG y).mul_mem hg ((FG y).inv_mem (hanti y hyx hn))
      rwa [← han, mul_inv_cancel_right] at hm
    · change QuotientGroup.mk' (FG x) (ι a) = QuotientGroup.mk' (FG x) g
      exact (QuotientGroup.mk'_eq_mk' _).mpr ⟨n, hn, han⟩

end QuotientIso

/-- Every `p`-adic field has a uniformizer with a compatible system of `p^n`-th roots in its
algebraic closure. -/
theorem exists_kummerRootSystem {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    ∃ (ϖ : F.Carrier) (πs : ℕ → AlgebraicClosure F.Carrier),
      Kummer.IsKummerRootSystem F ϖ πs := by
  let ϖ := F.canonicalTopologicalData.uniformizer
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  let πs : ℕ → AlgebraicClosure F.Carrier := fun n => Nat.rec
    (algebraMap F.Carrier (AlgebraicClosure F.Carrier) ϖ)
    (fun _ z => Classical.choose (IsAlgClosed.exists_pow_nat_eq z (Nat.pos_of_ne_zero hp))) n
  refine ⟨ϖ, πs, F.canonicalTopologicalData.ord_uniformizer, rfl, fun n => ?_⟩
  exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (πs n) (Nat.pos_of_ne_zero hp))

section Galois

attribute [local instance] LocalField.Laurent.valuativeRel

local instance closeFieldsPadicNormedField {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    NontriviallyNormedField F.Carrier :=
  F.canonicalNormedField
local instance closeFieldsPadicNormedAlgebra {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    NormedAlgebra (Padic p) F.Carrier :=
  F.canonicalNormedAlgebra
local instance closeFieldsPadicLocalField {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    FontaineWintenberger.IsPerfectResidueLocalField F.Carrier :=
  Wintenberger.padicField_isPerfectResidueLocalField F
local instance closeFieldsPadicCharZero {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier

theorem ramificationIndex_le_kummerBreak {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    (F.canonicalTopologicalData.ramificationIndex : ℝ) ≤ Kummer.kummerBreak F := by
  unfold Kummer.kummerBreak
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have he : (0 : ℝ) ≤ F.canonicalTopologicalData.ramificationIndex := Nat.cast_nonneg _
  rw [le_div_iff₀ (by linarith)]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The close-fields comparison of Galois quotients, with residue degrees.** For a `p`-adic field
`F` with absolute ramification index `e` and `X = k((t))`, there is an isomorphism of topological
groups `G_F/G_F^e ≃ G_X/G_X^e` carrying the image of `G_F^v` onto the image of `G_X^v` for
`0 ≤ v ≤ e`, and preserving residue degrees: `G_F^e` and `G_X^e` lie in the kernels of the residue
degrees, and corresponding classes have the same degree. -/
theorem exists_closeFieldsGaloisQuotient {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    let X := LaurentSeries (Weil.Local.localResidueField F)
    let Ω := SeparableClosure X
    let e : ℝ := F.canonicalTopologicalData.ramificationIndex
    let upperK := Padic.absoluteUpperRamificationGroup F
    let upperX := localAbsoluteUpperRamificationGroup X Ω
    ∃ φ : (Field.absoluteGaloisGroup F.Carrier ⧸ upperK e) ≃ₜ* ((Ω ≃ₐ[X] Ω) ⧸ upperX e),
      (∀ v : ℝ, 0 ≤ v → v ≤ e →
        ((upperK v).map (QuotientGroup.mk' (upperK e))).map φ.toMulEquiv.toMonoidHom =
          (upperX v).map (QuotientGroup.mk' (upperX e))) ∧
      (∀ (g₁ : Field.absoluteGaloisGroup F.Carrier) (g₂ : Ω ≃ₐ[X] Ω),
        φ (QuotientGroup.mk g₁) = QuotientGroup.mk g₂ →
          Weil.Local.localResidueDegree F g₁ = Weil.Local.SepClosed.localResidueDegree X Ω g₂) ∧
      upperK e ≤ (Weil.Local.localResidueDegree F).toMonoidHom.ker ∧
      upperX e ≤ (Weil.Local.SepClosed.localResidueDegree X Ω).toMonoidHom.ker := by
  obtain ⟨ϖ, πs, hπ⟩ := exists_kummerRootSystem F
  set L := Kummer.kummerTower F πs
  have hinf : ¬ Module.Finite F.Carrier L := Wintenberger.kummerTower_not_finite πs hπ
  have hAPF := Wintenberger.kummerTower_isAPF πs hπ
  have hopen : ∀ v : ℝ, -1 ≤ v → IsOpen ((L.fixingSubgroup ⊔
      Padic.absoluteUpperRamificationGroup F v : Subgroup (Field.absoluteGaloisGroup F.Carrier)) :
        Set (Field.absoluteGaloisGroup F.Carrier)) := by
    have h := (Wintenberger.isAPF_iff_isOpen (Padic p) (Wintenberger.padicBaseNorm_compatible p)
      F.Carrier (AlgebraicClosure F.Carrier) L L.val).mp hAPF
    rw [IntermediateField.fieldRange_val] at h
    exact h
  have hkb := Wintenberger.kummerBreak_pos F
  have hek := ramificationIndex_le_kummerBreak F
  have htot : L.fixingSubgroup ⊔ Padic.absoluteUpperRamificationGroup F 0 = ⊤ :=
    Kummer.kummerTowerLimitUpperSup p F ϖ πs hπ 0 (by norm_num) hkb.le
  obtain ⟨θ, hθ, hdeg⟩ := Wintenberger.normFieldComparison F L hinf hopen htot
  intro X Ω e upperK upperX
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hψ : ∀ v : ℝ, v ≤ e → Wintenberger.wintenbergerPsi F L v = v := by
    intro v hv
    rw [Wintenberger.wintenbergerPsi_eq_apfPsi]
    exact Wintenberger.kummerTower_apfPsi πs hπ (hv.trans hek)
  have : IsGalois L (AlgebraicClosure F.Carrier) := inferInstance
  let ι : (AlgebraicClosure F.Carrier ≃ₐ[L] AlgebraicClosure F.Carrier) →*
      Field.absoluteGaloisGroup F.Carrier := AlgEquiv.restrictScalarsHom F.Carrier
  have hι : Continuous ι :=
    Wintenberger.continuous_restrictScalarsHom F.Carrier L (AlgebraicClosure F.Carrier)
  let FA : ℝ → Subgroup (AlgebraicClosure F.Carrier ≃ₐ[L] AlgebraicClosure F.Carrier) :=
    fun y => (upperK y).comap ι
  have : IsClosed (upperK e : Set (Field.absoluteGaloisGroup F.Carrier)) :=
    Padic.absoluteUpperRamificationGroup_isClosed F e
  have : IsClosed (upperX e : Set (Ω ≃ₐ[X] Ω)) :=
    localAbsoluteUpperRamificationGroup_isClosed X Ω e
  have htop : L.fixingSubgroup ⊔ upperK e = ⊤ :=
    Kummer.kummerTowerLimitUpperSup p F ϖ πs hπ e (by linarith) hek
  have hsplit : ∀ g : Field.absoluteGaloisGroup F.Carrier, ∃ a, ∃ n ∈ upperK e, ι a * n = g := by
    intro g
    have hg : g ∈ L.fixingSubgroup ⊔ upperK e := htop ▸ Subgroup.mem_top g
    obtain ⟨h, hh, n, hn, rfl⟩ := (Subgroup.mem_sup_of_normal_right
      (ht := Padic.absoluteUpperRamificationGroup_normal F e)).mp hg
    exact ⟨L.fixingSubgroupEquiv ⟨h, hh⟩, n, hn, by congr 1⟩
  have hcomapX : ∀ y : ℝ, -1 ≤ y → y ≤ e → (upperX y).comap θ.toMulEquiv.toMonoidHom = FA y := by
    intro y hy hye
    have h := hθ y hy
    rw [hψ y hye] at h
    exact (congrArg (Subgroup.comap θ.toMulEquiv.toMonoidHom) h).symm.trans
      (Subgroup.comap_map_eq_self_of_injective θ.injective _)
  obtain ⟨φ₁, hφ₁, hφ₁mk⟩ := exists_quotientIso_of_comap ι hι FA upperK (a₀ := -1) (x := e)
    (by linarith) (fun y hy => Padic.absoluteUpperRamificationGroup_antitone F hy)
    (fun y _ _ => rfl) hsplit
  obtain ⟨φ₂, hφ₂, hφ₂mk⟩ := exists_quotientIso_of_comap θ.toMulEquiv.toMonoidHom θ.continuous FA
    upperX (a₀ := -1) (x := e) (by linarith)
    (fun y hy => localAbsoluteUpperRamificationGroup_antitone X Ω hy) hcomapX
    (fun g => ⟨θ.symm g, 1, Subgroup.one_mem _, by
      rw [mul_one]
      exact θ.apply_symm_apply g⟩)
  have hNK : upperK e ≤ (Weil.Local.localResidueDegree F).toMonoidHom.ker := by
    rw [Weil.Local.localResidueDegree_ker F, ← HerbrandBridge.absoluteUpperCanonicalInertia F]
    exact Padic.absoluteUpperRamificationGroup_antitone F he0
  have hNX : upperX e ≤
      (Weil.Local.SepClosed.localResidueDegree X Ω).toMonoidHom.ker := by
    intro g hg
    have hg' : θ.symm g ∈ FA e := by
      rw [← hcomapX e (by linarith) le_rfl, Subgroup.mem_comap]
      change θ (θ.symm g) ∈ upperX e
      rw [θ.apply_symm_apply]
      exact hg
    have h1 := hdeg (θ.symm g)
    rw [θ.apply_symm_apply] at h1
    change Weil.Local.SepClosed.localResidueDegree X Ω g = 1
    rw [← h1]
    exact hNK hg'
  refine ⟨φ₁.symm.trans φ₂, fun v hv hve => ?_, fun g₁ g₂ hg => ?_, hNK, hNX⟩
  · have h1 := hφ₁ v (by linarith) hve
    have h2 := hφ₂ v (by linarith) hve
    rw [← h2, ← h1, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    exact congrArg φ₂ (φ₁.symm_apply_apply _)
  · obtain ⟨a, n, hn, han⟩ := hsplit g₁
    have ha : φ₁.symm (QuotientGroup.mk g₁) = QuotientGroup.mk a := by
      rw [ContinuousMulEquiv.symm_apply_eq, hφ₁mk]
      exact ((QuotientGroup.mk'_eq_mk' _).mpr ⟨n, hn, han⟩).symm
    change φ₂ (φ₁.symm (QuotientGroup.mk g₁)) = _ at hg
    rw [ha, hφ₂mk] at hg
    have hm : (θ a)⁻¹ * g₂ ∈ upperX e := QuotientGroup.eq.mp hg
    have hm' := hNX hm
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hm'
    have hn' : Weil.Local.localResidueDegree F n = 1 := hNK hn
    rw [← han, map_mul, hn', mul_one]
    exact (hdeg a).trans hm'

/-- **The close-fields comparison of Galois quotients** (Deligne), proved through Wintenberger's
field of norms of the Kummer tower. -/
theorem closeFieldsGaloisQuotient : CloseFieldsGaloisQuotientStatement.{u} := by
  intro p _ F
  obtain ⟨φ, hφ, -⟩ := exists_closeFieldsGaloisQuotient F
  exact ⟨φ, hφ⟩

end Galois

end Langlands.Ramification.Local
