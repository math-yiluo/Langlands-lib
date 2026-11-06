import Langlands.Cohomology.SupercuspidalExtCharZero.CoefficientMap
import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Representation.Smooth.SmoothPart.BasicProof

/-!
# Retractions onto representations with compact coefficients

Let `ρ` be a smooth representation on `V` over a field of characteristic zero whose
compact open fixed vectors are finite-dimensional, and whose coefficients against smooth
functionals have compact support. Fix a compact open `U`, a `U`-invariant functional `ξ`
and a `U`-fixed vector `w`, and let `i : ρ → τ` be an injective intertwiner into a smooth
representation. Extend `ξ ∘ i⁻¹` to a `U`-invariant functional `η` on the target. The
pairing

`(y, ψ) ↦ ∑_{gU} η (τ g⁻¹ y) ψ (ρ g w)`

is a finite sum for every smooth functional `ψ`. For a fixed `y` it is invariant under a
compact open subgroup fixing `y`, hence is the evaluation at a unique vector `r y` of `V`.
The map `r` is an intertwiner with `r ∘ i` equal to the coefficient map of `(ρ, w)`.
-/

noncomputable section

namespace Langlands.Cohomology.SupercuspidalExtCharZero

open Function
open Langlands.Compact.CharZero

universe uk uG uV uY

variable {k : Type uk} [Field k] [CharZero k]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable {Y : Type uY} [AddCommGroup Y] [Module k Y]

section Bidual

omit [CharZero k] in
theorem smoothContragredient_apply_val (ρ : Representation k G V) (g : G)
    (ψ : SmoothDual ρ) : (smoothContragredient ρ g ψ).val = ρ.dual g ψ.val :=
  rfl

/-- If the `K`-fixed vectors of a smooth representation form a finite-dimensional space,
then a `K`-invariant linear form on the smooth dual is the evaluation at a `K`-fixed
vector. -/
theorem exists_eq_eval_of_invariant (ρ : Representation k G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    [FiniteDimensional k (fixedVectors ρ K.toSubgroup)] (Φ : SmoothDual ρ →ₗ[k] k)
    (hΦ : ∀ g ∈ K, ∀ ψ, Φ (smoothContragredient ρ g ψ) = Φ ψ) :
    ∃ v ∈ fixedVectors ρ K.toSubgroup, ∀ ψ : SmoothDual ρ, Φ ψ = ψ.val v := by
  set F := fixedVectors ρ K.toSubgroup
  let ext : Module.Dual k F →ₗ[k] SmoothDual ρ :=
    LinearMap.codRestrict (smoothVectors ρ.dual) (fixedProjection ρ hρ K hK).dualMap
      fun ℓ => (mem_smoothVectors_iff _).2 (fixedExtension_isSmoothVector ρ hρ K hK ℓ)
  set v₀ : F := (Module.evalEquiv k F).symm (Φ ∘ₗ ext)
  refine ⟨v₀.val, v₀.2, fun ψ => ?_⟩
  have hσ := isSmooth_smoothContragredient ρ
  set ψ' := averageMap (smoothContragredient ρ) hσ K hK ψ
  have ha : Φ ψ' = Φ ψ := apply_averageMap_of_invariant _ hσ K hK Φ hΦ ψ
  have hb : ψ'.val v₀.val = ψ.val v₀.val := by
    refine apply_averageMap_of_invariant (smoothContragredient ρ) hσ K hK
      (Module.Dual.eval k V v₀.val ∘ₗ (smoothVectors ρ.dual).subtype) (fun g hg χ => ?_) ψ
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Dual.eval_apply,
      smoothContragredient_apply_val, Representation.dual_apply, Module.Dual.transpose_apply]
    rw [mem_fixedVectors_iff.1 v₀.2 g⁻¹ (K.inv_mem hg)]
  have hc : ∀ g ∈ K, ∀ x, ψ'.val (ρ g x) = ψ'.val x := by
    have h1 := mem_fixedVectors_iff.1 (averageMap_mem_fixedVectors _ hσ K hK ψ)
    refine mem_fixedVectors_dual_iff.1 (mem_fixedVectors_iff.2 fun g hg => ?_)
    exact congrArg Subtype.val (h1 g hg)
  have hd : ext (ψ'.val ∘ₗ F.subtype) = ψ' := by
    apply Subtype.ext
    ext x
    exact apply_averageMap_of_invariant ρ hρ K hK ψ'.val hc x
  calc Φ ψ = Φ ψ' := ha.symm
    _ = (Φ ∘ₗ ext) (ψ'.val ∘ₗ F.subtype) := by rw [LinearMap.comp_apply, hd]
    _ = (ψ'.val ∘ₗ F.subtype) v₀ := (Module.apply_evalEquiv_symm_apply k F _ _).symm
    _ = ψ.val v₀.val := hb

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- Smooth functionals separate the vectors of a smooth representation. -/
theorem eq_of_forall_smoothDual (ρ : Representation k G V) (hρ : IsSmooth ρ) {v v' : V}
    (h : ∀ ψ : SmoothDual ρ, ψ.val v = ψ.val v') : v = v' := by
  refine sub_eq_zero.1 (eq_zero_of_forall_smooth_dual ρ hρ fun ψ hψ => ?_)
  rw [map_sub, h ⟨ψ, (mem_smoothVectors_iff _).2 hψ⟩, sub_self]

end Bidual

section Pairing

omit [CharZero k]

variable (ρ : Representation k G V) (τ : Representation k G Y)

/-- The pairing `(y, ψ) ↦ ∑_{gU} η (τ g⁻¹ y) ψ (ρ g w)` over the left cosets of `U`. -/
def retractionPairing (U : Subgroup G) (η : Module.Dual k Y) (w : V) (y : Y)
    (ψ : Module.Dual k V) : k :=
  cosetSum U fun g => η (τ g⁻¹ y) * ψ (ρ g w)

variable {ρ τ} {U : Subgroup G} {η : Module.Dual k Y} {w : V}

theorem retractionPairing_hasFiniteSupport (hU : IsOpen (U : Set G)) {ψ : Module.Dual k V}
    (hψ : HasCompactSupport fun g => ψ (ρ g w)) (y : Y) :
    (fun q : G ⧸ U => η (τ q.out⁻¹ y) * ψ (ρ q.out w)).HasFiniteSupport :=
  (hasFiniteSupport_out_of_hasCompactSupport hU hψ).subset (support_mul_subset_right _ _)

theorem retractionPairing_add_left (hU : IsOpen (U : Set G)) {ψ : Module.Dual k V}
    (hψ : HasCompactSupport fun g => ψ (ρ g w)) (y y' : Y) :
    retractionPairing ρ τ U η w (y + y') ψ =
      retractionPairing ρ τ U η w y ψ + retractionPairing ρ τ U η w y' ψ := by
  unfold retractionPairing cosetSum
  simp only [map_add, add_mul]
  exact finsum_add_distrib (retractionPairing_hasFiniteSupport hU hψ y)
    (retractionPairing_hasFiniteSupport hU hψ y')

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem retractionPairing_smul_left (c : k) (y : Y) (ψ : Module.Dual k V) :
    retractionPairing ρ τ U η w (c • y) ψ = c * retractionPairing ρ τ U η w y ψ := by
  unfold retractionPairing cosetSum
  rw [mul_finsum]
  simp only [map_smul, smul_eq_mul, mul_assoc]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem retractionPairing_rightInvariant (hη : ∀ u ∈ U, ∀ y, η (τ u y) = η y)
    (hw : ∀ u ∈ U, ρ u w = w) (y : Y) (ψ : Module.Dual k V) :
    RightInvariant U fun g => η (τ g⁻¹ y) * ψ (ρ g w) := by
  intro g u hu
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply]
  rw [hη u⁻¹ (U.inv_mem hu), hw u hu]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem retractionPairing_apply_rep (hη : ∀ u ∈ U, ∀ y, η (τ u y) = η y)
    (hw : ∀ u ∈ U, ρ u w = w) (h : G) (y : Y) (ψ : Module.Dual k V) :
    retractionPairing ρ τ U η w (τ h y) ψ = retractionPairing ρ τ U η w y (ψ ∘ₗ ρ h) := by
  unfold retractionPairing
  rw [← cosetSum_mul_left (retractionPairing_rightInvariant hη hw (τ h y) ψ) h]
  refine cosetSum_congr fun g => ?_
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply, LinearMap.comp_apply,
    Representation.inv_self_apply]

/-- For a fixed `y`, the pairing is a linear form on the smooth dual. -/
def retractionForm (hU : IsOpen (U : Set G))
    (hc : ∀ ψ : Module.Dual k V, IsSmoothVector ρ.dual ψ → HasCompactSupport fun g => ψ (ρ g w))
    (y : Y) : SmoothDual ρ →ₗ[k] k where
  toFun ψ := retractionPairing ρ τ U η w y ψ.val
  map_add' ψ ψ' := by
    unfold retractionPairing cosetSum
    simp only [Submodule.coe_add, LinearMap.add_apply, mul_add]
    exact finsum_add_distrib
      (retractionPairing_hasFiniteSupport hU (hc _ ((mem_smoothVectors_iff _).1 ψ.2)) y)
      (retractionPairing_hasFiniteSupport hU (hc _ ((mem_smoothVectors_iff _).1 ψ'.2)) y)
  map_smul' c ψ := by
    unfold retractionPairing cosetSum
    simp only [SetLike.val_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_finsum]
    simp only [mul_left_comm]

theorem retractionForm_apply (hU : IsOpen (U : Set G))
    (hc : ∀ ψ : Module.Dual k V, IsSmoothVector ρ.dual ψ → HasCompactSupport fun g => ψ (ρ g w))
    (y : Y) (ψ : SmoothDual ρ) :
    retractionForm (τ := τ) (η := η) hU hc y ψ = retractionPairing ρ τ U η w y ψ.val :=
  rfl

/-- The linear form attached to a `K`-fixed vector is `K`-invariant. -/
theorem retractionForm_invariant (hU : IsOpen (U : Set G))
    (hc : ∀ ψ : Module.Dual k V, IsSmoothVector ρ.dual ψ → HasCompactSupport fun g => ψ (ρ g w))
    (hη : ∀ u ∈ U, ∀ y, η (τ u y) = η y) (hw : ∀ u ∈ U, ρ u w = w) {K : Subgroup G} {y : Y}
    (hy : y ∈ fixedVectors τ K) (g : G) (hg : g ∈ K) (ψ : SmoothDual ρ) :
    retractionForm (τ := τ) (η := η) hU hc y (smoothContragredient ρ g ψ) =
      retractionForm (τ := τ) (η := η) hU hc y ψ := by
  rw [retractionForm_apply, retractionForm_apply, smoothContragredient_apply_val,
    Representation.dual_apply, Module.Dual.transpose_apply,
    ← retractionPairing_apply_rep hη hw, mem_fixedVectors_iff.1 hy g⁻¹ (K.inv_mem hg)]

/-- On the image of an intertwiner `i` with `η ∘ i = ξ`, the pairing is evaluation at the
coefficient map. -/
theorem retractionPairing_apply_intertwining (hU : IsOpen (U : Set G)) {ξ : Module.Dual k V}
    (hcξ : ∀ v, HasCompactSupport fun g => ξ (ρ g v)) (i : ρ.IntertwiningMap τ)
    (hηi : ∀ v, η (i v) = ξ v) (v : V) (ψ : Module.Dual k V) :
    retractionPairing ρ τ U η w (i v) ψ = ψ (coefficientMap ρ ρ U ξ w v) := by
  rw [map_coefficientMap ψ hU hcξ]
  unfold retractionPairing
  refine cosetSum_congr fun g => ?_
  rw [← Representation.IntertwiningMap.isIntertwining, hηi, map_smul, smul_eq_mul]

end Pairing

section Retraction

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- Let `ρ` be smooth with finite-dimensional compact open fixed vectors and compactly
supported coefficients, `U` compact open, `ξ` a `U`-invariant functional and `w` a
`U`-fixed vector. For every injective intertwiner `i : ρ → τ` into a smooth
representation there is an intertwiner `r : τ → ρ` with `r ∘ i` equal to the coefficient
map `v ↦ ∑_{gU} ξ (ρ g⁻¹ v) • ρ g w`. -/
theorem exists_intertwining_comp_eq_coefficientMap (ρ : Representation k G V)
    (hρ : IsSmooth ρ)
    (hadm : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      FiniteDimensional k (fixedVectors ρ K.toSubgroup))
    (hc : ∀ (v : V) (ℓ : Module.Dual k V), IsSmoothVector ρ.dual ℓ →
      HasCompactSupport (matrixCoefficient ρ ℓ v))
    (τ : Representation k G Y) (hτ : IsSmooth τ) (i : ρ.IntertwiningMap τ)
    (hi : Injective i) (U : OpenSubgroup G) (hUc : IsCompact (U : Set G))
    (ξ : Module.Dual k V) (hξ : ∀ u ∈ U, ∀ v, ξ (ρ u v) = ξ v) (w : V)
    (hw : ∀ u ∈ U, ρ u w = w) :
    ∃ r : τ.IntertwiningMap ρ, ∀ v, r (i v) = coefficientMap ρ ρ U ξ w v := by
  -- a `U`-invariant extension `η` of `ξ ∘ i⁻¹`
  obtain ⟨r₀, hr₀⟩ := LinearMap.exists_leftInverse_of_injective i.toLinearMap
    (LinearMap.ker_eq_bot.2 hi)
  set η : Module.Dual k Y := (ξ ∘ₗ r₀) ∘ₗ averageMap τ hτ U hUc
  have hη : ∀ u ∈ U, ∀ y, η (τ u y) = η y := fun u hu y => by
    simp only [η, LinearMap.comp_apply]
    rw [averageMap_apply_rho τ hτ U hUc ⟨u, hu⟩ y]
  have hηi : ∀ v, η (i v) = ξ v := fun v => by
    have h1 := LinearMap.congr_fun (averageMap_commute ρ τ hρ hτ U hUc i) v
    simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply] at h1
    simp only [η, LinearMap.comp_apply]
    rw [← h1, ← Representation.IntertwiningMap.toLinearMap_apply, ← LinearMap.comp_apply r₀,
      hr₀, LinearMap.id_apply, apply_averageMap_of_invariant ρ hρ U hUc ξ hξ v]
  have hcw : ∀ ψ : Module.Dual k V, IsSmoothVector ρ.dual ψ →
      HasCompactSupport fun g => ψ (ρ g w) := fun ψ hψ => hc w ψ hψ
  have hξs : IsSmoothVector ρ.dual ξ :=
    ⟨U, mem_fixedVectors_dual_iff.2 fun u hu v => hξ u hu v⟩
  have hcξ : ∀ v, HasCompactSupport fun g => ξ (ρ g v) := fun v => hc v ξ hξs
  let Φ : Y → SmoothDual ρ →ₗ[k] k := retractionForm (τ := τ) (η := η) U.isOpen hcw
  -- each form is an evaluation
  have hex : ∀ y, ∃ v : V, ∀ ψ : SmoothDual ρ, Φ y ψ = ψ.val v := by
    intro y
    obtain ⟨K, hKc, hyK⟩ := exists_compact_fixing (hτ y)
    have := hadm K hKc
    obtain ⟨v, -, hv⟩ := exists_eq_eval_of_invariant ρ hρ K hKc (Φ y)
      fun g hg ψ => retractionForm_invariant U.isOpen hcw hη hw hyK g hg ψ
    exact ⟨v, hv⟩
  choose r hr using hex
  have hadd : ∀ y y', r (y + y') = r y + r y' := fun y y' =>
    eq_of_forall_smoothDual ρ hρ fun ψ => by
      rw [map_add, ← hr, ← hr, ← hr]
      exact retractionPairing_add_left U.isOpen
        (hcw _ ((mem_smoothVectors_iff _).1 ψ.2)) y y'
  have hsmul : ∀ (c : k) y, r (c • y) = c • r y := fun c y =>
    eq_of_forall_smoothDual ρ hρ fun ψ => by
      rw [map_smul, ← hr, ← hr, smul_eq_mul]
      exact retractionPairing_smul_left c y ψ.val
  have hrep : ∀ (h : G) y, r (τ h y) = ρ h (r y) := fun h y =>
    eq_of_forall_smoothDual ρ hρ fun ψ => by
      rw [← hr]
      have h1 := hr y (smoothContragredient ρ h⁻¹ ψ)
      rw [smoothContragredient_apply_val, Representation.dual_apply,
        Module.Dual.transpose_apply, LinearMap.comp_apply, inv_inv] at h1
      rw [← h1]
      show retractionPairing ρ τ U η w (τ h y) ψ.val =
        retractionPairing ρ τ U η w y (ρ.dual h⁻¹ ψ.val)
      rw [retractionPairing_apply_rep hη hw, Representation.dual_apply,
        Module.Dual.transpose_apply, inv_inv]
  refine ⟨⟨⟨⟨r, hadd⟩, hsmul⟩, fun h => LinearMap.ext fun y => hrep h y⟩, fun v => ?_⟩
  refine eq_of_forall_smoothDual ρ hρ fun ψ => ?_
  show ψ.val (r (i v)) = _
  rw [← hr]
  exact retractionPairing_apply_intertwining U.isOpen hcξ i hηi v ψ.val

end Retraction

end Langlands.Cohomology.SupercuspidalExtCharZero
