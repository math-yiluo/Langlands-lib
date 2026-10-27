import Langlands.Representation.Whittaker.CoordinateJacquetKernelStatement
import Langlands.Representation.Whittaker.PrerequisiteInterfaces
import Langlands.HarmonicAnalysis.Conductor
import Langlands.LocalField.Normalization.Proof

/-!
# Proof of uniform Whittaker vanishing on a coordinate Jacquet kernel

Each generating relation `ρ u w - w` of the two-block Jacquet kernel has coefficient
`(ψ ((a_i / a_(i+1)) u_(i,i+1)) - 1) ℓ (ρ (torus a) w)` at the diagonal element
`torus a`. A positive normalized-absolute-value threshold kills the character factor,
and span induction combines finitely many thresholds by minima.
-/

namespace Langlands.Whittaker.CoordinateJacquetKernel

open GeneralLinear HarmonicAnalysis

universe uF uV

section Threshold

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- A continuous unit-norm complex additive character is trivial on a ball of positive
normalized-absolute-value radius around zero. -/
theorem exists_pos_forall_addChar_eq_one (ψ : AddChar F.Carrier ℂ)
    (hc : @Continuous _ _ T.topology _ ψ) (hu : ∀ x, ‖ψ x‖ = 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, T.normalizedAbs x < ε → ψ x = 1 := by
  by_cases h1 : ψ = 1
  · exact ⟨1, one_pos, fun x _ => by rw [h1, AddChar.one_apply]⟩
  let := T.topology
  obtain ⟨n, hn⟩ :=
    T.exists_additiveTrivialAt (UnitaryAdditiveCharacter.ofComplex ψ hc h1 hu)
  have hπ : T.uniformizer ≠ 0 := by
    intro h
    have ho := T.ord_uniformizer
    rw [h, T.ord_zero] at ho
    exact zero_ne_one ho
  have hy : T.uniformizer ^ (-n) ≠ 0 := zpow_ne_zero _ hπ
  have hypos := T.normalizedAbs_pos hy
  refine ⟨T.normalizedAbs (T.uniformizer ^ (-n)), hypos, fun x hx => ?_⟩
  have hmem : x ∈ T.additiveLattice n := by
    rw [T.mem_additiveLattice_iff_div_mem_integers,
      ← T.normalizedAbs_le_one_iff_mem_integers]
    have hsplit : T.normalizedAbs x =
        T.normalizedAbs (x / T.uniformizer ^ (-n)) * T.normalizedAbs (T.uniformizer ^ (-n)) := by
      rw [← T.normalizedAbs_mul, div_mul_cancel₀ x hy]
    rw [hsplit] at hx
    exact (lt_of_mul_lt_mul_right (by simpa using hx) hypos.le).le
  exact congrArg Subtype.val (hn x hmem)

/-- After multiplication by a fixed field element, the character is still trivial on a
ball of positive normalized-absolute-value radius. -/
theorem exists_pos_forall_addChar_mul_eq_one (ψ : AddChar F.Carrier ℂ)
    (hc : @Continuous _ _ T.topology _ ψ) (hu : ∀ x, ‖ψ x‖ = 1) (c : F.Carrier) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r, T.normalizedAbs r < δ → ψ (r * c) = 1 := by
  by_cases hc0 : c = 0
  · exact ⟨1, one_pos, fun r _ => by rw [hc0, mul_zero, AddChar.map_zero_eq_one]⟩
  obtain ⟨ε, hε, hψ⟩ := exists_pos_forall_addChar_eq_one T ψ hc hu
  have hcpos := T.normalizedAbs_pos hc0
  refine ⟨ε / T.normalizedAbs c, div_pos hε hcpos, fun r hr => hψ _ ?_⟩
  rw [T.normalizedAbs_mul]
  exact (lt_div_iff₀ hcpos).mp hr

end Threshold

section Conjugation

variable {K : Type*} [CommRing K] {m : ℕ}

/-- The diagonal torus parametrization used by the statement. -/
abbrev torus (m : ℕ) (K : Type*) [CommRing K] : (Fin m → Kˣ) →* GeneralLinear m K :=
  (Units.map (Matrix.diagonalRingHom (Fin m) K).toMonoidHom).comp
    MulEquiv.piUnits.symm.toMonoidHom

theorem torus_val (a : Fin m → Kˣ) :
    ((torus m K a : GeneralLinear m K) : Matrix (Fin m) (Fin m) K) =
      Matrix.diagonal fun j => (a j : K) := rfl

/-- Diagonal conjugation multiplies the `(j, k)` entry by `a_j / a_k`. -/
theorem torus_conj_apply (a : Fin m → Kˣ) (g : GeneralLinear m K) (j k : Fin m) :
    ((torus m K a * g * (torus m K a)⁻¹ : GeneralLinear m K) :
        Matrix (Fin m) (Fin m) K) j k =
      (a j : K) * g.val j k * (((a k)⁻¹ : Kˣ) : K) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, torus_val, torus_val,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

end Conjugation

section Kernel

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The threshold property of a vector, for one selected adjacent ratio. -/
def HasThreshold (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V) (i : Fin n) (v : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ a : Fin (n + 1) → F.Carrierˣ,
    T.normalizedAbs ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier) < ε →
    ℓ (ρ (torus (n + 1) F.Carrier a) v) = 0

/-- Vectors with a threshold form a submodule. -/
def thresholdSubmodule (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V) (i : Fin n) : Submodule ℂ V where
  carrier := {v | HasThreshold T ρ ℓ i v}
  zero_mem' := ⟨1, one_pos, fun a _ => by rw [map_zero, map_zero]⟩
  add_mem' := by
    rintro v w ⟨ε, hε, hv⟩ ⟨δ, hδ, hw⟩
    refine ⟨min ε δ, lt_min hε hδ, fun a ha => ?_⟩
    rw [map_add, map_add, hv a (ha.trans_le (min_le_left _ _)),
      hw a (ha.trans_le (min_le_right _ _)), add_zero]
  smul_mem' := by
    rintro c v ⟨ε, hε, hv⟩
    refine ⟨ε, hε, fun a ha => ?_⟩
    rw [map_smul, map_smul, hv a ha, smul_zero]

/-- The coordinate Whittaker conjugation identity and threshold for one generating relation
of the two-block Jacquet kernel. -/
theorem hasThreshold_relation
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (ψ : AddChar F.Carrier ℂ) (hc : @Continuous _ _ T.topology _ ψ) (hu : ∀ x, ‖ψ x‖ = 1)
    (ℓ : Module.Dual ℂ V)
    (hℓ : ∀ g : GeneralLinear (n + 1) F.Carrier,
      ((∀ j k, k < j → g.val j k = 0) ∧ ∀ j, g.val j j = 1) →
        ∀ w, ℓ (ρ g w) = (∏ j : Fin n, ψ (g.val j.castSucc j.succ)) * ℓ w)
    (i : Fin n) (u : GeneralLinear (n + 1) F.Carrier)
    (hu' : u ∈ (CuspidalSupport.LeviAdmissibility.twoBlock (n + 1) i.val
      (by omega)).unipotentSubgroup F.Carrier) (w : V) :
    HasThreshold T ρ ℓ i (ρ u w - w) := by
  have hs := CuspidalSupport.LeviAdmissibility.splitUnipotent_of_mem_twoBlock _ hu'
  obtain ⟨δ, hδ, hψ⟩ :=
    exists_pos_forall_addChar_mul_eq_one T ψ hc hu (u.val i.castSucc i.succ)
  refine ⟨δ, hδ, fun a ha => ?_⟩
  set t := torus (n + 1) F.Carrier a
  have hconj : ρ t (ρ u w) = ρ (t * u * t⁻¹) (ρ t w) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel_right]
  have hunip : (∀ j k, k < j → (t * u * t⁻¹ : GeneralLinear (n + 1) F.Carrier).val j k = 0) ∧
      ∀ j, (t * u * t⁻¹ : GeneralLinear (n + 1) F.Carrier).val j j = 1 := by
    refine ⟨fun j k hkj => ?_, fun j => ?_⟩
    · rw [torus_conj_apply, hs j k (by omega), Matrix.one_apply_ne (ne_of_gt hkj),
        mul_zero, zero_mul]
    · rw [torus_conj_apply, hs j j (by omega), Matrix.one_apply_eq, mul_one,
        ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hθ : (∏ j : Fin n, ψ ((t * u * t⁻¹ : GeneralLinear (n + 1) F.Carrier).val
      j.castSucc j.succ)) =
      ψ (((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier) * u.val i.castSucc i.succ) := by
    rw [Finset.prod_eq_single i]
    · rw [torus_conj_apply, Units.val_div_eq_div_val, div_eq_mul_inv, Units.val_inv_eq_inv_val]
      ring_nf
    · intro j _ hji
      rw [torus_conj_apply, hs j.castSucc j.succ ?_,
        Matrix.one_apply_ne (ne_of_lt j.castSucc_lt_succ), mul_zero, zero_mul,
        AddChar.map_zero_eq_one]
      rintro ⟨h1, h2⟩
      apply hji
      ext
      simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
      omega
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [map_sub, map_sub, hconj, hℓ _ hunip, hθ, hψ _ ha, one_mul, sub_self]

/-- Every vector of the actual two-block Jacquet kernel has a threshold. -/
theorem hasThreshold_of_jacquetMk_eq_zero
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (ψ : AddChar F.Carrier ℂ) (hc : @Continuous _ _ T.topology _ ψ) (hu : ∀ x, ‖ψ x‖ = 1)
    (ℓ : Module.Dual ℂ V)
    (hℓ : ∀ g : GeneralLinear (n + 1) F.Carrier,
      ((∀ j k, k < j → g.val j k = 0) ∧ ∀ j, g.val j j = 1) →
        ∀ w, ℓ (ρ g w) = (∏ j : Fin n, ψ (g.val j.castSucc j.succ)) * ℓ w)
    (i : Fin n) (v : V)
    (hv : (CuspidalSupport.LeviAdmissibility.twoBlock (n + 1) i.val
      (by omega)).jacquetMk ρ v = 0) :
    HasThreshold T ρ ℓ i v := by
  set B := CuspidalSupport.LeviAdmissibility.twoBlock (n + 1) i.val (by omega)
  have hrel : v ∈ Jacquet.relations ρ (B.unipotentSubgroup F.Carrier) := by
    rw [← Jacquet.mk_eq_zero, ← B.jacquetModuleEquiv_mk, hv, map_zero]
  change v ∈ thresholdSubmodule T ρ ℓ i
  refine (Submodule.span_le.mpr ?_) hrel
  rintro _ ⟨⟨u, w⟩, rfl⟩
  exact hasThreshold_relation T ρ ψ hc hu ℓ hℓ i u u.property w

end Kernel

end Langlands.Whittaker.CoordinateJacquetKernel

namespace Langlands.Whittaker

universe uF uV

/-- Uniform Whittaker vanishing on a coordinate Jacquet kernel. -/
theorem coordinateJacquetKernelStatement :
    CoordinateJacquetKernelStatement.{uF, uV} := by
  intro p _hp F T n V _ _ ρ ψ hc hu _hsmooth _ _ _ ℓ hℓ i _ v hv
  exact CoordinateJacquetKernel.hasThreshold_of_jacquetMk_eq_zero T ρ ψ hc hu ℓ hℓ i v hv

end Langlands.Whittaker
