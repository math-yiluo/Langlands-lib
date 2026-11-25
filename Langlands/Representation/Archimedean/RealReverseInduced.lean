import Langlands.Representation.Archimedean.RealLeviWitness
import Langlands.Representation.Archimedean.RealParabolicLimitValue
import Langlands.Representation.Archimedean.RealReverseSplit
import Langlands.Representation.Archimedean.RealPairingAnnihilator

/-!
# Intertwiners to the reversed standard module along the tie classes

Let `dss_0, …, dss_{c-1}` be lists of real blocks of ranks `sz_i`, `N = ∑_i sz_i`,
`ds = dss_0 ++ ⋯ ++ dss_{c-1}`, and `Q` the standard parabolic subgroup with diagonal blocks
of sizes `sz_i`. For `u` in the `O(N)`-finite dual principal series `Y` of `ds` and `h` in the
`O(N)`-finite standard module `X` of `ds` let

`Θ(u, h) = ∫_{K_M} ∫_{N̄_Q} c_Z(x ↦ u(x diag(κ)) h(x n̄(X) diag(κ))) dX dκ`

be the torus-averaged limit pairing `RealLeviPairing.theta (slots ds N) u h` (Library module
`RealLeviPairing`). Using that `Θ(u, h)` depends only on the jointly allowed coefficients of `u`
on `K_M` (`RealLeviPairing.theta_congr`), this module proves:

* `integral_mul_eq_of_forall`: equal pairings against a `(𝔤, K)`-stable subspace of `X` give
  equal matrix coefficients `∫ u(κ g) w(κ) dκ`;
* `theta_eq_zero_of_mem`: if every class standard module is irreducible, `Θ(x, y) = 0` for every
  `x ∈ Y` and every `y` of a proper `(𝔤, K)`-submodule of `X`;
* `reverseKernel`: under the hypotheses of `RealLeviLimitStatement` on `ds` and irreducibility
  of every class standard module, every intertwiner from `X` to the standard module of
  `ds.reverse` vanishes on every proper `(𝔤, K)`-submodule of `X`. The nonvanishing of the limit
  pairing it needs is `realLeviWitness` (Library module `RealLeviWitness`).
-/

noncomputable section

open MeasureTheory Matrix

open scoped TensorProduct Matrix.Norms.Operator Manifold ContDiff

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealReverseInduced

open RealInducedBlockBound RealInducedTorusCore RealInducedStandardBound RealLeviChart
  RealLeviLimit RealParabolicLimitValue RealLeviSlices RealLeviProducts RealLeviDensity
  RealLeviDuality
open RealPrincipalSeriesDuality PartialJacquet JacquetDual JacquetKernel MatrixCoefficientAnalytic
  RealStrictCharacterLanglandsQuotient
open RealReverseTransfer RealReverseSplit RealSplitFrobenius RealPairingAnnihilator

attribute [local instance] measurableSpaceK

/-! ## Matrix coefficients from pairings -/

section Pairing

variable {n : ℕ}

/-- **Matrix coefficients from pairings.** If `u` and `z` in the `O(n)`-finite dual principal
series of `ds` have the same pairings with a `(𝔤, K)`-stable subspace `W'` of the
`O(n)`-finite standard module, then `∫ u(κ g) w(κ) dκ = ∫ z(κ g) w(κ) dκ` for all `w ∈ W'`
and `g ∈ GL_n(ℝ)`. -/
theorem integral_mul_eq_of_forall {ds : List RealBlock}
    (W' : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)))
    (hWK : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ), ∀ w ∈ W', realStandardRep n ds k w ∈ W')
    (hWL : ∀ (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ), ∀ w ∈ W', realStandardLie n ds X w ∈ W')
    {u z : Langlands.GeneralLinear n ℝ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
      (unitaryCompact ℝ n))
    (hz : z ∈ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
      (unitaryCompact ℝ n))
    (huz : ∀ w ∈ W', ∫ κ, u (κ : Langlands.GeneralLinear n ℝ) *
        (w : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n =
      ∫ κ, z (κ : Langlands.GeneralLinear n ℝ) * (w : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n)
    {w : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)} (hw : w ∈ W')
    (g : Langlands.GeneralLinear n ℝ) :
    ∫ κ, u ((κ : Langlands.GeneralLinear n ℝ) * g) * (w : Langlands.GeneralLinear n ℝ → ℂ) κ
        ∂haarK n =
      ∫ κ, z ((κ : Langlands.GeneralLinear n ℝ) * g) * (w : Langlands.GeneralLinear n ℝ → ℂ) κ
        ∂haarK n := by
  set μ := (haarK n).map (toUnitaryGroup n)
  have hcont : ∀ {a b : Langlands.GeneralLinear n ℝ → ℂ}, Continuous a → Continuous b →
      ∀ g : Langlands.GeneralLinear n ℝ,
        Continuous fun y : Langlands.GeneralLinear n ℝ => a (y * g) * b y :=
    fun ha hb g => (ha.comp (continuous_id.mul continuous_const)).mul hb
  have hmc : ∀ {a b : Langlands.GeneralLinear n ℝ → ℂ}, Continuous a → Continuous b →
      ∀ g : Langlands.GeneralLinear n ℝ,
        MatrixCoefficientAnalytic.matrixCoefficient μ a (b ∘ Unitary.toUnits) g =
          ∫ κ, a ((κ : Langlands.GeneralLinear n ℝ) * g) * b κ ∂haarK n := by
    intro a b ha hb g
    simp only [MatrixCoefficientAnalytic.matrixCoefficient]
    exact integral_map_toUnitaryGroup (f := fun y => a (y * g) * b y) (hcont ha hb g)
  have huc := continuous_of_mem hu
  have hzc := continuous_of_mem hz
  have key := matrixCoefficient_eq_of_rel μ _ _
    (isSignedPower ds).eq (isSignedPower ds).eq
    (fun a b => ∃ w' ∈ W', a = (w' : Langlands.GeneralLinear n ℝ → ℂ) ∧
      b = (w' : Langlands.GeneralLinear n ℝ → ℂ))
    (fun a b ⟨w', _, ha, hb⟩ => ⟨ha ▸ mem_kFiniteFunctions_principalSeries w'.2,
      hb ▸ mem_kFiniteFunctions_principalSeries w'.2⟩)
    (fun k hk a b ⟨w', hw', ha, hb⟩ =>
      ⟨realStandardRep n ds ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ w', hWK _ _ hw',
        by rw [realStandardRep_apply_coe, RealReverseTransfer.toUnits_mk, ha],
        by rw [realStandardRep_apply_coe, RealReverseTransfer.toUnits_mk, hb]⟩)
    (fun X a b ⟨w', hw', ha, hb⟩ => ⟨realStandardLie n ds (1 ⊗ₜ X) w', hWL _ _ hw',
      by rw [realStandardLie_one_tmul_apply_coe, ha],
      by rw [realStandardLie_one_tmul_apply_coe, hb]⟩)
    (huc.comp continuous_unitary_toUnits) (hzc.comp continuous_unitary_toUnits)
    (fun a b ⟨w', hw', ha, hb⟩ => by
      subst ha hb
      rw [hmc (continuous_of_mem_kFiniteFunctions w'.2) huc,
        hmc (continuous_of_mem_kFiniteFunctions w'.2) hzc]
      simp only [mul_one]
      calc ∫ κ, (w' : Langlands.GeneralLinear n ℝ → ℂ) (κ : Langlands.GeneralLinear n ℝ) *
              u κ ∂haarK n
          = ∫ κ, u (κ : Langlands.GeneralLinear n ℝ) *
              (w' : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n :=
            integral_congr_ae (ae_of_all _ fun κ => mul_comm _ _)
        _ = ∫ κ, z (κ : Langlands.GeneralLinear n ℝ) *
              (w' : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n := huz w' hw'
        _ = _ := integral_congr_ae (ae_of_all _ fun κ => mul_comm _ _))
    _ _ ⟨w, hw, rfl, rfl⟩ g⁻¹
  rw [hmc (continuous_of_mem_kFiniteFunctions w.2) huc,
    hmc (continuous_of_mem_kFiniteFunctions w.2) hzc] at key
  have hwp := realStandardModule_le_principalSeries n ds w.2.1
  rw [← integral_mul_inv_swap (isSignedPower ds) hu.1 hwp g,
    ← integral_mul_inv_swap (isSignedPower ds) hz.1 hwp g]
  exact key

end Pairing

/-! ## Values of the limit pairing -/

section Values

variable {c : ℕ} {sz : Fin c → ℕ}

/-- `Θ(u, h) = Θ(z, h)` if `u` and `z` have the same pairings with the whole standard module. -/
theorem theta_eq_of_pairing (hT1 : RealLeviChartIntegrableStatement)
    (hT3 : RealLeviParabolicIntegrationStatement) {ds : List RealBlock}
    (hN : realRank ds = ∑ i, sz i)
    (hanti : ∀ p q : Fin (∑ i, sz i), p ≤ q →
      realPositionBlockExponent ds q ≤ realPositionBlockExponent ds p)
    (hstrict : ∀ p q : Fin (∑ i, sz i), cls sz p < cls sz q →
      realPositionBlockExponent ds q < realPositionBlockExponent ds p)
    {u z : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
      (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
    (hz : z ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
      (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
    (huz : ∀ w : kFiniteFunctions (realStandardModule (∑ i, sz i) ds)
        (unitaryCompact ℝ (∑ i, sz i)),
      ∫ κ, u (κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) *
          (w : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ) κ ∂haarK (∑ i, sz i) =
        ∫ κ, z (κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) *
          (w : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ) κ ∂haarK (∑ i, sz i))
    (h : kFiniteFunctions (realStandardModule (∑ i, sz i) ds) (unitaryCompact ℝ (∑ i, sz i))) :
    RealLeviPairing.theta (slots ds (∑ i, sz i)) u h =
      RealLeviPairing.theta (slots ds (∑ i, sz i)) z h :=
  integral_coeffs_eq_of_eq hT1 hT3 hN hanti hstrict hu h.2 hz h.2 fun _ _ =>
    integral_mul_eq_of_forall ⊤ (fun _ _ _ => Submodule.mem_top) (fun _ _ _ => Submodule.mem_top)
      hu hz (fun w _ => huz w) Submodule.mem_top _

/-- `Θ(u, h) = 0` if all matrix coefficients `∫ u(κ g) h(κ) dκ` vanish. -/
theorem theta_eq_zero (hT1 : RealLeviChartIntegrableStatement)
    (hT3 : RealLeviParabolicIntegrationStatement) {ds : List RealBlock}
    (hN : realRank ds = ∑ i, sz i)
    (hanti : ∀ p q : Fin (∑ i, sz i), p ≤ q →
      realPositionBlockExponent ds q ≤ realPositionBlockExponent ds p)
    (hstrict : ∀ p q : Fin (∑ i, sz i), cls sz p < cls sz q →
      realPositionBlockExponent ds q < realPositionBlockExponent ds p)
    {u h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
    (hu : u ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
      (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
    (hh : h ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds) (unitaryCompact ℝ (∑ i, sz i)))
    (h0 : ∀ g : Langlands.GeneralLinear (∑ i, sz i) ℝ,
      ∫ κ, u ((κ : Langlands.GeneralLinear (∑ i, sz i) ℝ) * g) * h κ ∂haarK (∑ i, sz i) = 0) :
    RealLeviPairing.theta (slots ds (∑ i, sz i)) u h = 0 :=
  integral_coeffs_eq_zero hT1 hT3 hN hanti hstrict hu hh h0

/-- `d_s` is symmetric. -/
theorem transposeGL_scaleGL {s : ℝ} (hs : 0 < s) :
    RealReverseTwist.transposeGL (scaleGL sz hs) = scaleGL sz hs := by
  apply Units.ext
  rw [RealReverseTwist.transposeGL_val, scaleGL_val, Matrix.diagonal_transpose]

end Values

/-! ## Vanishing on proper submodules -/

section Vanishing

variable {c : ℕ} {dss : Fin c → List RealBlock}

/-- Equality of the jointly allowed coefficients, checked on mode lists split by classes. -/
theorem coeffs_eq_of_split {u u' : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ}
    (h : ∀ Js : Fin c → List ℤ, (∀ i, (Js i).length = (slots (cl dss i) (sz dss i)).length) →
      (∀ i, ∀ t ∈ withModes (slots (cl dss i) (sz dss i)) (Js i), (t.M : ℤ) ≤ |t.j|) →
      ∀ κ : ∀ i, unitaryCompact ℝ (sz dss i),
        coeffs (withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn Js).flatten) u
            (bdK (sz dss) κ) =
          coeffs (withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn Js).flatten) u'
            (bdK (sz dss) κ)) :
    ∀ J : List ℤ, J.length = (slots (flat dss) (∑ j, sz dss j)).length →
      (∀ t ∈ withModes (slots (flat dss) (∑ j, sz dss j)) J, (t.M : ℤ) ≤ |t.j|) →
      ∀ κ : ∀ i, unitaryCompact ℝ (sz dss i),
        coeffs (withModes (slots (flat dss) (∑ j, sz dss j)) J) u (bdK (sz dss) κ) =
          coeffs (withModes (slots (flat dss) (∑ j, sz dss j)) J) u' (bdK (sz dss) κ) := by
  intro J hJlen hJall κ
  obtain ⟨Js, hJs, rfl⟩ := exists_split (fun i => (slots (cl dss i) (sz dss i)).length) J
    (hJlen.trans (length_slots_flat dss))
  have h3 := map_key3_flat dss Js hJs
  exact h Js hJs (fun i t ht => allowed_of_map_key3 h3 hJall _
    (liftSlot_mem_globalSlots (fun i => withModes (slots (cl dss i) (sz dss i)) (Js i))
      (List.mem_finRange i) ht)) κ

/-- **Vanishing on proper submodules.** If every class standard module is irreducible and `W`
is a proper `(𝔤, K)`-submodule of the standard module of `ds = dss_0 ++ ⋯ ++ dss_{c-1}`, then
`Θ(x, y) = 0` for every `x` of the dual space and every `y ∈ W`. -/
theorem theta_eq_zero_of_mem (hT1 : RealLeviChartIntegrableStatement)
    (hT3 : RealLeviParabolicIntegrationStatement)
    (hanti : ∀ p q : Fin (∑ i, sz dss i), p ≤ q →
      realPositionBlockExponent (flat dss) q ≤ realPositionBlockExponent (flat dss) p)
    (hstrict : ∀ p q : Fin (∑ i, sz dss i), cls (sz dss) p < cls (sz dss) q →
      realPositionBlockExponent (flat dss) q < realPositionBlockExponent (flat dss) p)
    (hX : ∀ i, IsIrreducibleGKModule (realStandardRep (sz dss i) (cl dss i))
      (realStandardLie (sz dss i) (cl dss i)))
    (W : Submodule ℂ (StdSpace (∑ j, sz dss j) (flat dss)))
    (hWK : ∀ (k : Matrix.unitaryGroup (Fin (∑ j, sz dss j)) ℝ), ∀ w ∈ W,
      realStandardRep (∑ j, sz dss j) (flat dss) k w ∈ W)
    (hWL : ∀ (X : ℂ ⊗[ℝ] Matrix (Fin (∑ j, sz dss j)) (Fin (∑ j, sz dss j)) ℝ), ∀ w ∈ W,
      realStandardLie (∑ j, sz dss j) (flat dss) X w ∈ W)
    (hW : W ≠ ⊤) {y : StdSpace (∑ j, sz dss j) (flat dss)} (hy : y ∈ W)
    (x : DualSpace (∑ j, sz dss j) (flat dss)) :
    RealLeviPairing.theta (slots (flat dss) (∑ j, sz dss j)) x y = 0 := by
  classical
  obtain ⟨m, C, w, hw⟩ := exists_isProdForm x
  choose u hu hcoef using fun a => exists_density hX (w a) W hWK hWL hW
  let x' : DualSpace (∑ j, sz dss j) (flat dss) := ∑ a, C a • u a
  have hx'W : x' ∈ annW W := Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hu a)
  have hx'fun : (x' : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) =
      fun g => ∑ a, C a * (u a : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) g := by
    funext g
    simp only [x', Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  have hN := realRank_flat dss
  have hDEP : RealLeviPairing.theta (slots (flat dss) (∑ j, sz dss j)) x y =
      RealLeviPairing.theta (slots (flat dss) (∑ j, sz dss j)) x' y := by
    refine RealLeviPairing.theta_congr x.2 x'.2 y.2 (coeffs_eq_of_split ?_)
    intro Js hJs hall κ
    unfold bdK
    rw [coeffs_congr_key3 (map_key3_flat dss Js hJs),
      coeffs_globalSlots hw (fun a j => continuous_of_mem_dualSpace (w a j).2) _
        (fun j => (κ j).2),
      hx'fun, coeffs_sum_mul C (fun a => continuous_of_mem_dualSpace (u a).2)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hcoef a Js hJs hall _ (fun j => (κ j).2)]
  rw [hDEP]
  refine theta_eq_zero hT1 hT3 hN hanti hstrict x'.2 y.2 fun g => ?_
  have e := integral_mul_eq_of_forall W hWK hWL x'.2
    (zero_mem (DualSpace (∑ j, sz dss j) (flat dss))) ?_ hy g
  · simpa using e
  · intro w' hw'
    simp only [Pi.zero_apply, zero_mul, integral_zero]
    exact mem_annW.mp hx'W w' hw'

end Vanishing

/-! ## Intertwiners to the reversed module -/

section Reverse

variable {c : ℕ}

theorem isCharacterList_split : ∀ ds : List RealBlock, IsCharacterList (split ds)
  | [] => fun b hb => by simp [split] at hb
  | b :: ds => by
    intro x hx
    rw [split_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · cases b with
      | character a =>
        simp only [splitBlock, List.mem_singleton] at hx
        exact ⟨a, hx⟩
      | induced e =>
        simp only [splitBlock, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> exact ⟨_, rfl⟩
    · exact isCharacterList_split ds x hx

theorem dualChar_dualChar (χ : ℕ → ℝˣ → ℂ) : dualChar (dualChar χ) = χ := by
  funext l x
  simp [dualChar]

/-- **Intertwiners to the reversed module kill proper submodules.** Let
`ds = dss_0 ++ ⋯ ++ dss_{c-1}` satisfy the hypotheses of `RealLeviLimitStatement` for the
class sizes, and let every class standard module be irreducible. Then every
`(𝔤, K)`-intertwiner `T` from the `O(N)`-finite standard module of `ds` to that of `ds.reverse`
vanishes on every proper `(𝔤, K)`-submodule. -/
theorem reverseKernel (hT1 : RealLeviChartIntegrableStatement)
    (hT3 : RealLeviParabolicIntegrationStatement) {dss : Fin c → List RealBlock}
    (hanti : ∀ p q : Fin (∑ i, sz dss i), p ≤ q →
      realPositionBlockExponent (flat dss) q ≤ realPositionBlockExponent (flat dss) p)
    (hstrict : ∀ p q : Fin (∑ i, sz dss i), cls (sz dss) p < cls (sz dss) q →
      realPositionBlockExponent (flat dss) q < realPositionBlockExponent (flat dss) p)
    (hX : ∀ i, IsIrreducibleGKModule (realStandardRep (sz dss i) (cl dss i))
      (realStandardLie (sz dss i) (cl dss i)))
    (T : kFiniteFunctions (realStandardModule (∑ j, sz dss j) (flat dss))
        (unitaryCompact ℝ (∑ j, sz dss j)) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule (∑ j, sz dss j) (flat dss).reverse)
        (unitaryCompact ℝ (∑ j, sz dss j)))
    (hT : IsRealStandardIntertwiner (∑ j, sz dss j)
      (realStandardRep (∑ j, sz dss j) (flat dss).reverse)
      (realStandardLie (∑ j, sz dss j) (flat dss).reverse) (flat dss) T)
    (W : Submodule ℂ (kFiniteFunctions (realStandardModule (∑ j, sz dss j) (flat dss))
      (unitaryCompact ℝ (∑ j, sz dss j))))
    (hW : IsGKSubmodule (realStandardRep (∑ j, sz dss j) (flat dss))
      (realStandardLie (∑ j, sz dss j) (flat dss)) W)
    (hWne : W ≠ ⊤) : W ≤ LinearMap.ker T := by
  classical
  have hN := realRank_flat dss
  obtain ⟨D, hD, hDonto, hL, hU, hZ⟩ := exists_splitTranspose (flat dss) hN T hT
  -- the pairings
  let SY := DualSpace (∑ j, sz dss j) (flat dss)
  let SX := StdSpace (∑ j, sz dss j) (flat dss)
  let SYs := kFiniteFunctions (principalSeries ℝ (∑ j, sz dss j)
    (dualChar (realPositionCharacter (split (flat dss))))) (unitaryCompact ℝ (∑ j, sz dss j))
  let SXs := kFiniteFunctions (realStandardModule (∑ j, sz dss j) (split (flat dss)))
    (unitaryCompact ℝ (∑ j, sz dss j))
  let Lmap : SX →ₗ[ℂ] SYs := LinearMap.codRestrict SYs
    ((RealReverseTwist.twistLin _).comp ((Submodule.subtype _).comp T)) hL
  let Φ : SY →ₗ[ℂ] Module.Dual ℂ SXs :=
    (intPairing SY SX (fun _ ha => continuous_of_mem ha)
      (fun _ ha => continuous_of_mem_kFiniteFunctions ha)).compl₂ D
  let Ψ : SX →ₗ[ℂ] Module.Dual ℂ SXs :=
    (intPairing SYs SXs (fun _ ha => continuous_of_mem ha)
      (fun _ ha => continuous_of_mem_kFiniteFunctions ha)).comp Lmap
  let V : Submodule ℂ SY := (W.map Ψ).comap Φ
  have hmemV : ∀ z : SY, z ∈ V ↔ ∃ w ∈ W, ∀ f : SXs,
      ∫ κ, (z : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
          (κ : Langlands.GeneralLinear (∑ j, sz dss j) ℝ) *
          (D f : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) κ ∂haarK (∑ j, sz dss j) =
        ∫ κ, RealReverseTwist.twistLin _
            (T w : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
            (κ : Langlands.GeneralLinear (∑ j, sz dss j) ℝ) *
          (f : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) κ ∂haarK (∑ j, sz dss j) := by
    intro z
    simp only [V, Submodule.mem_comap, Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, he⟩
      exact ⟨w, hw, fun f => (LinearMap.congr_fun he f).symm⟩
    · rintro ⟨w, hw, he⟩
      exact ⟨w, hw, LinearMap.ext fun f => (he f).symm⟩
  -- `V` is `O(N)`-stable
  have hVK : ∀ (k : Matrix.unitaryGroup (Fin (∑ j, sz dss j)) ℝ), ∀ z ∈ V,
      principalSeriesRep ℝ (∑ j, sz dss j) (dualChar (realPositionCharacter (flat dss))) k z ∈
        V := by
    intro k z hz
    obtain ⟨w, hw, hzw⟩ := (hmemV z).mp hz
    refine (hmemV _).mpr ⟨realStandardRep _ (flat dss) k w, hW.1 k w hw, fun f => ?_⟩
    have hk : (Unitary.toUnits k : Langlands.GeneralLinear (∑ j, sz dss j) ℝ) ∈
        unitaryCompact ℝ (∑ j, sz dss j) := k.2
    have e1 := hzw (realStandardRep _ (split (flat dss)) k⁻¹ f)
    rw [hD.map_realStandardRep, realStandardRep_apply_coe, realStandardRep_apply_coe,
      map_inv] at e1
    have e2 := integral_translate_mul (z : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
      (D f : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) hk
    have e3 := integral_translate_mul (RealReverseTwist.twistLin _
      (T w : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ))
      (f : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) hk
    rw [principalSeriesRep_apply_coe, hT.map_realStandardRep, realStandardRep_apply_coe,
      ← RealReverseTwist.rightTranslation_twistLin _ hk]
    exact e2.trans (e1.trans e3.symm)
  -- `V` is stable under `𝔤`
  have hVL1 : ∀ (Y0 : Matrix (Fin (∑ j, sz dss j)) (Fin (∑ j, sz dss j)) ℝ), ∀ z ∈ V,
      principalSeriesLie ℝ (∑ j, sz dss j) (dualChar (realPositionCharacter (flat dss)))
        (1 ⊗ₜ Y0) z ∈ V := by
    intro Y0 z hz
    obtain ⟨w, hw, hzw⟩ := (hmemV z).mp hz
    refine (hmemV _).mpr ⟨realStandardLie _ (flat dss) (1 ⊗ₜ (-Y0ᵀ)) w, hW.2 _ w hw,
      fun f => ?_⟩
    have e1 := hzw (realStandardLie _ (split (flat dss)) (1 ⊗ₜ Y0) f)
    rw [hD.map_realStandardLie, realStandardLie_one_tmul_apply_coe,
      realStandardLie_one_tmul_apply_coe] at e1
    have hTw : RealReverseTwist.twistLin _ (T (realStandardLie _ (flat dss) (1 ⊗ₜ (-Y0ᵀ)) w) :
        Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) =
        rightDerivative (matrixModel ℝ (∑ j, sz dss j)) Y0 (RealReverseTwist.twistLin _
          (T w : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)) := by
      rw [hT.map_realStandardLie, realStandardLie_one_tmul_apply_coe,
        RealReverseTwist.rightDerivative_twistLin
          (contMDiff_of_mem_realStandardModule (T w).2.1)]
    rw [principalSeriesLie_one_tmul_apply_coe, hTw]
    have s1 := integral_rightDerivative_mul_add (flat dss) Y0 z.2.1 (D f).2.1
      (by
        rw [← principalSeriesLie_one_tmul_apply_coe]
        exact continuous_of_mem (principalSeriesLie ℝ _ _ (1 ⊗ₜ Y0) z).2)
      (by
        rw [← realStandardLie_one_tmul_apply_coe]
        exact continuous_of_mem_kFiniteFunctions (realStandardLie _ _ (1 ⊗ₜ Y0) (D f)).2)
    have s2 := integral_rightDerivative_mul_add (split (flat dss)) Y0 (hL w).1 f.2.1
      (by
        rw [← hTw]
        exact continuous_of_mem (hL _))
      (by
        rw [← realStandardLie_one_tmul_apply_coe]
        exact continuous_of_mem_kFiniteFunctions (realStandardLie _ _ (1 ⊗ₜ Y0) f).2)
    rw [e1] at s1
    linear_combination s1 - s2
  have hVL : ∀ (Xl : ℂ ⊗[ℝ] Matrix (Fin (∑ j, sz dss j)) (Fin (∑ j, sz dss j)) ℝ), ∀ z ∈ V,
      principalSeriesLie ℝ (∑ j, sz dss j) (dualChar (realPositionCharacter (flat dss))) Xl z ∈
        V := by
    intro Xl
    induction Xl using TensorProduct.inductionOn with
    | tmul a Y0 =>
        intro z hz
        have hcY : (a ⊗ₜ[ℝ] Y0 : ℂ ⊗[ℝ] Matrix (Fin (∑ j, sz dss j)) (Fin (∑ j, sz dss j)) ℝ) =
            a • ((1 : ℂ) ⊗ₜ[ℝ] Y0) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hcY, map_smul, LinearMap.smul_apply]
        exact V.smul_mem _ (hVL1 Y0 z hz)
    | add X₁ X₂ h₁ h₂ =>
        intro z hz
        rw [map_add, LinearMap.add_apply]
        exact V.add_mem (h₁ z hz) (h₂ z hz)
  have hP := isGKSubmodule_perp (flat dss) (V := V) ⟨hVK, hVL⟩
  -- `Θ(z, h) = 0` for the transposes `z` of `W`
  have hzero : ∀ w ∈ W, ∀ z : SY, (∀ f : SXs,
      ∫ κ, (z : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
          (κ : Langlands.GeneralLinear (∑ j, sz dss j) ℝ) *
          (D f : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) κ ∂haarK (∑ j, sz dss j) =
        ∫ κ, RealReverseTwist.twistLin _
            (T w : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
            (κ : Langlands.GeneralLinear (∑ j, sz dss j) ℝ) *
          (f : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) κ ∂haarK (∑ j, sz dss j)) →
      ∀ h : SX, RealLeviPairing.theta (slots (flat dss) (∑ j, sz dss j)) z h = 0 := by
    intro w hw z hz h
    obtain ⟨f, rfl⟩ := hDonto h
    obtain ⟨zw, hzw, hzw1, hzw2⟩ := hZ w
    obtain ⟨uf, huf, hufw⟩ := hU f
    have e1 : RealLeviPairing.theta (slots (flat dss) (∑ j, sz dss j)) z (D f) =
        RealLeviPairing.theta (slots (flat dss) (∑ j, sz dss j)) zw (D f) := by
      refine theta_eq_of_pairing hT1 hT3 hN hanti hstrict z.2 hzw (fun h => ?_) (D f)
      obtain ⟨f', rfl⟩ := hDonto h
      exact (hz f').trans (hzw1 f').symm
    have e2 : RealLeviPairing.theta (slots (flat dss) (∑ j, sz dss j)) uf w =
        RealLeviPairing.theta (slots (flat dss) (∑ j, sz dss j)) zw (D f) :=
      integral_coeffs_eq_of_eq hT1 hT3 hN hanti hstrict huf w.2 hzw (D f).2 fun s hs => by
        rw [hufw w, transposeGL_scaleGL, hzw2 f]
    rw [e1, ← e2]
    exact theta_eq_zero_of_mem hT1 hT3 hanti hstrict hX W hW.1 hW.2 hWne hw ⟨uf, huf⟩
  -- the orthogonal of `V` is everything
  have hperp : perp (flat dss) V = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, h0, hh0, hM⟩ := realLeviWitness hT1 c dss hanti hstrict hX
    obtain ⟨u, hu, hcoef⟩ := exists_density hX (fun i => ⟨φ i, hφ i⟩) (perp (flat dss) V)
      hP.1 hP.2 hne
    have hθ := hM u u.2 hcoef
    obtain ⟨z, hzV, hz⟩ := exists_eq_of_vanishing (flat dss) hVK u
      (fun h hh => mem_annW.mp hu h hh)
    obtain ⟨w, hw, hzw⟩ := (hmemV z).mp hzV
    have e1 : RealLeviPairing.theta (slots (flat dss) (∑ j, sz dss j)) u h0 =
        RealLeviPairing.theta (slots (flat dss) (∑ j, sz dss j)) z h0 :=
      theta_eq_of_pairing hT1 hT3 hN hanti hstrict u.2 z.2 hz ⟨h0, hh0⟩
    exact hθ (e1.trans (hzero w hw z hzw ⟨h0, hh0⟩))
  -- conclusion
  intro w hw
  rw [LinearMap.mem_ker]
  obtain ⟨zw, hzw, hzw1, -⟩ := hZ w
  have hzV : (⟨zw, hzw⟩ : SY) ∈ V := (hmemV _).mpr ⟨w, hw, hzw1⟩
  have hvan : ∀ f : SXs, ∫ κ, RealReverseTwist.twistLin _
      (T w : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
      (κ : Langlands.GeneralLinear (∑ j, sz dss j) ℝ) *
        (f : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) κ ∂haarK (∑ j, sz dss j) = 0 := by
    intro f
    rw [← hzw1 f]
    have hmem : D f ∈ perp (flat dss) V := by
      rw [hperp]
      exact Submodule.mem_top
    exact (mem_perp (D f)).mp hmem _ hzV
  have hLw0 : RealReverseTwist.twistLin _
      (T w : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) = 0 := by
    by_contra hne
    obtain ⟨v, hv, hv0⟩ := exists_integral_mul_ne_zero
      (isSignedPower (split (flat dss))).dual (hL w) hne
    rw [dualChar_dualChar] at hv
    have hv' : v ∈ SXs := by
      show v ∈ kFiniteFunctions (realStandardModule (∑ j, sz dss j) (split (flat dss)))
        (unitaryCompact ℝ (∑ j, sz dss j))
      rw [realStandardModule_eq (isCharacterList_split _)]
      exact hv
    apply hv0
    rw [← hvan ⟨v, hv'⟩]
    exact integral_congr_ae (ae_of_all _ fun κ => mul_comm _ _)
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero, ← RealReverseTwist.twistLin_twistLin
    (T w : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ), hLw0, map_zero]

end Reverse

end RealReverseInduced

end Langlands.Archimedean
