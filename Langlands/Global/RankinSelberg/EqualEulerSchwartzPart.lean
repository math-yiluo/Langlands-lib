import Langlands.Global.RankinSelberg.PartialIntegralExhaustion
import Langlands.Global.RankinSelberg.PartialWhittakerIntegrals
import Langlands.Global.RankinSelberg.SchwartzBruhat
import Langlands.Global.RankinSelberg.EqualIntegrals
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.Global.RankinSelberg.WhittakerCellDecompositionStatement

/-! # The Schwartz–Bruhat factor under a one-place torus translation

For `Φ` equal to `1_(𝒪_v^n)` outside a finite set `S`, a finite place `v ∉ S`, and `g` with
`g_v ∈ N_n(F_v) GL_n(𝒪_v)`, translating `g` on the left by an adelic point supported at `v`
with component `ϖ^λ` multiplies `Φ(e_n g)` by the indicator of `λ_n ≥ 0`. Auxiliary lemmas
for the partial Euler factorization of the equal-rank global Whittaker integral
(Cogdell 2004, §2.3). See the paired Markdown.
-/

noncomputable section
universe u
open NumberField
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualEulerSchwartz

local instance equalEulerSchwartzSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalEulerSchwartzSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F]

/-- The archimedean part of the `j`-th coordinate of `e_n g` is the `(n, j)` entry of the
infinite component of `g`. -/
theorem lastRow_fst {r : ℕ} (g : Points F (r + 1)) (j : Fin (r + 1)) :
    (lastRow F r g 0 j).1 =
      AdelicGL.infinite F (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1) g)
        (Fin.last r) j :=
  rfl

/-- The `v`-coordinates of `e_n g` are the last row of `g_v`. -/
theorem localCoordinates_lastRow {r : ℕ} (w : FinitePlace F) (g : Points F (r + 1))
    (j : Fin (r + 1)) :
    localCoordinates F (r + 1) w (lastRow F r g) j =
      finiteComponent F (r + 1) w g (Fin.last r) j :=
  rfl

/-- Left translation by a point with trivial infinite component does not change the
archimedean coordinates of the last row. -/
theorem lastRow_mul_fst {r : ℕ} {h : Points F (r + 1)}
    (hinf : AdelicGL.infinite F (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1) h) = 1)
    (g : Points F (r + 1)) (j : Fin (r + 1)) :
    (lastRow F r (h * g) 0 j).1 = (lastRow F r g 0 j).1 := by
  rw [lastRow_fst, lastRow_fst, map_mul, map_mul, hinf, one_mul]

/-- Left translation by a point with trivial component at the finite place `w` does not
change the `w`-coordinates of the last row. -/
theorem localCoordinates_lastRow_mul_of_eq_one {r : ℕ} {w : FinitePlace F}
    {h : Points F (r + 1)} (hw : finiteComponent F (r + 1) w h = 1) (g : Points F (r + 1)) :
    localCoordinates F (r + 1) w (lastRow F r (h * g)) =
      localCoordinates F (r + 1) w (lastRow F r g) := by
  funext j
  rw [localCoordinates_lastRow, localCoordinates_lastRow, finiteComponent_mul, hw, one_mul]

/-- Left translation by a point with component `ϖ^λ` at `v` multiplies the `v`-coordinates
of the last row by `ϖ^(λ_n)`. -/
theorem localCoordinates_lastRow_mul_torus {r : ℕ} {v : FinitePlace F}
    {ϖ : (FiniteCompletion F v)ˣ} {lam : Fin (r + 1) → ℤ} {h : Points F (r + 1)}
    (hv : finiteComponent F (r + 1) v h = GeneralLinear.Iwasawa.torus ϖ lam)
    (g : Points F (r + 1)) (j : Fin (r + 1)) :
    localCoordinates F (r + 1) v (lastRow F r (h * g)) j =
      ((ϖ ^ lam (Fin.last r) : (FiniteCompletion F v)ˣ) : FiniteCompletion F v) *
        localCoordinates F (r + 1) v (lastRow F r g) j := by
  rw [localCoordinates_lastRow, localCoordinates_lastRow, finiteComponent_mul, hv]
  change ((GeneralLinear.Iwasawa.torus ϖ lam).val * (finiteComponent F (r + 1) v g).val)
    (Fin.last r) j = _
  rw [GeneralLinear.Iwasawa.torus_val, Matrix.diagonal_mul]

/-- If `x ∈ N_n(F_v) GL_n(𝒪_v)`, the last row of `x` is integral and primitive: its entries lie
in `𝒪_v` and one of them is a unit. -/
theorem lastRow_integral_primitive {r : ℕ} {v : FinitePlace F} {x : FiniteLocalGL F (r + 1) v}
    (hx : IsUnipotentIntegral F (r + 1) v x) :
    (∀ j, x (Fin.last r) j ∈ v.adicCompletionIntegers F) ∧
      ∃ j, Valued.v (x (Fin.last r) j) = 1 := by
  obtain ⟨k, hk, hdiag, hlow⟩ := hx
  rw [FiniteAdelicGL.mem_localIntegral] at hk
  -- the last row of `x` is the last row of `k⁻¹`
  have hrow : ∀ j, x (Fin.last r) j = k⁻¹ (Fin.last r) j := by
    intro j
    have hxk : x = (x * k) * k⁻¹ := by rw [mul_inv_cancel_right]
    change (x : Matrix (Fin (r + 1)) (Fin (r + 1)) (FiniteCompletion F v)) (Fin.last r) j = _
    rw [hxk, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]
    · rw [show ((x * k : FiniteLocalGL F (r + 1) v) : Matrix (Fin (r + 1)) (Fin (r + 1))
          (FiniteCompletion F v)) (Fin.last r) (Fin.last r) = 1 from hdiag _, one_mul]
    · intro l _ hl
      rw [show ((x * k : FiniteLocalGL F (r + 1) v) : Matrix (Fin (r + 1)) (Fin (r + 1))
          (FiniteCompletion F v)) (Fin.last r) l = 0 from
        hlow _ _ (lt_of_le_of_ne (Fin.le_last l) hl), zero_mul]
    · intro hl
      exact absurd (Finset.mem_univ _) hl
  refine ⟨fun j => hrow j ▸ hk.2 _ _, ?_⟩
  by_contra hne
  push Not at hne
  have hlt : ∀ j, Valued.v (k⁻¹ (Fin.last r) j * k j (Fin.last r)) < 1 := by
    intro j
    rw [map_mul]
    have h1 : Valued.v (k⁻¹ (Fin.last r) j) < 1 :=
      lt_of_le_of_ne ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
        (hk.2 _ _)) (hrow j ▸ hne j)
    have h2 : Valued.v (k j (Fin.last r)) ≤ 1 :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hk.1 _ _)
    calc Valued.v (k⁻¹ (Fin.last r) j) * Valued.v (k j (Fin.last r))
        ≤ Valued.v (k⁻¹ (Fin.last r) j) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact h1
  have hsum : ∑ j, k⁻¹ (Fin.last r) j * k j (Fin.last r) = 1 := by
    have h := congrArg (fun M : Matrix (Fin (r + 1)) (Fin (r + 1)) (FiniteCompletion F v) =>
      M (Fin.last r) (Fin.last r)) (congrArg Units.val (inv_mul_cancel k))
    simp only [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
    exact h
  have := Valuation.map_sum_lt (v := (Valued.v : Valuation (FiniteCompletion F v) _))
    (s := Finset.univ) one_ne_zero (fun j _ => hlt j)
  rw [hsum, map_one] at this
  exact lt_irrefl _ this

/-- **The Schwartz–Bruhat factor under a one-place torus translation.** Let `Φ` be
`1_(𝒪_w^n)` at every finite place `w ∉ S`, `v ∉ S`, `ϖ ∈ F_v^×` with `|ϖ|_v < 1`, and let
`h` be an adelic point with trivial infinite component, trivial components at the finite
places `w ≠ v`, and component `ϖ^λ = diag(ϖ^(λ_1), …, ϖ^(λ_n))` at `v`. If
`g_v ∈ N_n(F_v) GL_n(𝒪_v)`, then `Φ(e_n h g) = Φ(e_n g)` when `λ_n ≥ 0` and `= 0`
otherwise. -/
theorem apply_lastRow_mul_torus {r : ℕ} {S : Finset (FinitePlace F)}
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : IsStandardOutside F (r + 1) S Φ)
    {v : FinitePlace F} (hvS : v ∉ S) {ϖ : (FiniteCompletion F v)ˣ}
    (hϖ : Valued.v (ϖ : FiniteCompletion F v) < 1) (lam : Fin (r + 1) → ℤ)
    {h : Points F (r + 1)}
    (hinf : AdelicGL.infinite F (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1) h) = 1)
    (hfin : ∀ w, w ≠ v → finiteComponent F (r + 1) w h = 1)
    (hv : finiteComponent F (r + 1) v h = GeneralLinear.Iwasawa.torus ϖ lam)
    {g : Points F (r + 1)} (hg : IsUnipotentIntegral F (r + 1) v (finiteComponent F (r + 1) v g)) :
    Φ (lastRow F r (h * g)) = if 0 ≤ lam (Fin.last r) then Φ (lastRow F r g) else 0 := by
  obtain ⟨hint, j₀, hj₀⟩ := lastRow_integral_primitive hg
  have hval : ∀ j, Valued.v (localCoordinates F (r + 1) v (lastRow F r (h * g)) j) =
      Valued.v (ϖ : FiniteCompletion F v) ^ lam (Fin.last r) *
        Valued.v (finiteComponent F (r + 1) v g (Fin.last r) j) := by
    intro j
    rw [localCoordinates_lastRow_mul_torus hv, map_mul, localCoordinates_lastRow,
      Units.val_zpow_eq_zpow_val, map_zpow₀]
  have hϖpos : 0 < Valued.v (ϖ : FiniteCompletion F v) :=
    (Valuation.pos_iff _).2 ϖ.ne_zero
  split_ifs with hm
  · -- `λ_n ≥ 0`: both points are integral at `v`, and the other coordinates agree.
    have hle : Valued.v (ϖ : FiniteCompletion F v) ^ lam (Fin.last r) ≤ 1 := by
      lift lam (Fin.last r) to ℕ using hm with m
      rw [zpow_natCast]
      exact pow_le_one₀ hϖpos.le hϖ.le
    have hiff : lastRow F r (h * g) ∈ integralOutside F (r + 1) S ↔
        lastRow F r g ∈ integralOutside F (r + 1) S := by
      constructor
      · intro hy w hw j
        by_cases hwv : w = v
        · subst hwv
          rw [localCoordinates_lastRow]
          exact hint j
        · rw [← localCoordinates_lastRow_mul_of_eq_one (hfin w hwv) g]
          exact hy w hw j
      · intro hx w hw j
        by_cases hwv : w = v
        · subst hwv
          rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hval]
          calc Valued.v (ϖ : FiniteCompletion F w) ^ lam (Fin.last r) *
                Valued.v (finiteComponent F (r + 1) w g (Fin.last r) j)
              ≤ 1 * 1 := mul_le_mul' hle
                ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
                  (hint j))
            _ = 1 := one_mul 1
        · rw [localCoordinates_lastRow_mul_of_eq_one (hfin w hwv) g]
          exact hx w hw j
    by_cases hx : lastRow F r g ∈ integralOutside F (r + 1) S
    · exact hΦ.2 _ _ (hiff.2 hx) hx (lastRow_mul_fst hinf g) fun w hw =>
        localCoordinates_lastRow_mul_of_eq_one (hfin w fun hwv => hvS (hwv ▸ hw)) g
    · rw [hΦ.1 _ hx, hΦ.1 _ (fun hy => hx (hiff.1 hy))]
  · -- `λ_n < 0`: the `j₀`-th coordinate of `e_n h g` at `v` is not integral.
    apply hΦ.1
    intro hy
    have hj := hy v hvS j₀
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hval, hj₀,
      mul_one] at hj
    have hgt : 1 < Valued.v (ϖ : FiniteCompletion F v) ^ lam (Fin.last r) := by
      obtain ⟨m, hm'⟩ : ∃ m : ℕ, lam (Fin.last r) = -((m + 1 : ℕ) : ℤ) :=
        ⟨(-lam (Fin.last r) - 1).toNat, by omega⟩
      rw [hm', zpow_neg, zpow_natCast]
      exact one_lt_inv₀ (pow_pos hϖpos _) |>.2 (pow_lt_one₀ hϖpos.le hϖ (Nat.succ_ne_zero m))
    exact absurd hj (not_le.2 hgt)

/-- **The Schwartz–Bruhat factor under `ι_v(ϖ^λ)`.** The form of
`apply_lastRow_mul_torus` for the point `ι_v(ϖ^λ) = localPoint F (r+1) v (torus ϖ lam)` of the
one-place cell decomposition, with `ϖ` a uniformizer of `F_v` for `Valued.v`: if
`g_v ∈ N_n(F_v) GL_n(𝒪_v)`, then `Φ(e_n ι_v(ϖ^λ) g) = Φ(e_n g)` when `λ_n ≥ 0` and `= 0`
otherwise. -/
theorem apply_lastRow_localPoint_torus {r : ℕ} {S : Finset (FinitePlace F)}
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : IsStandardOutside F (r + 1) S Φ)
    {v : FinitePlace F} (hv : v ∉ S) (ϖ : (FiniteCompletion F v)ˣ)
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (Valued.v : Valuation (FiniteCompletion F v) (WithZero (Multiplicative ℤ))) ϖ)
    (lam : Fin (r + 1) → ℤ) (g : Points F (r + 1))
    (hg : IsUnipotentIntegral F (r + 1) v (finiteComponent F (r + 1) v g)) :
    Φ (lastRow F r (localPoint F (r + 1) v (GeneralLinear.Iwasawa.torus ϖ lam) * g)) =
      if 0 ≤ lam (Fin.last r) then Φ (lastRow F r g) else 0 := by
  set x := FiniteAdelicGL.localInclusion F (r + 1) v (GeneralLinear.Iwasawa.torus ϖ lam)
  have hpt : GeneralLinearGroupPoints.adelicEquiv F (r + 1)
      (localPoint F (r + 1) v (GeneralLinear.Iwasawa.torus ϖ lam)) =
      AdelicGL.ofFinite F (r + 1) x := by
    rw [localPoint, MulEquiv.apply_symm_apply]
  have hfin : AdelicGL.finite F (r + 1) (AdelicGL.ofFinite F (r + 1) x) = x := by
    apply Units.ext; rfl
  refine apply_lastRow_mul_torus hΦ hv hϖ.1 lam ?_ ?_ ?_ hg
  · rw [hpt]
    apply Units.ext; rfl
  · intro w hw
    rw [finiteComponent, hpt, hfin,
      FiniteAdelicGL.localProjection_localInclusion_of_ne F (r + 1) v w hw]
  · rw [finiteComponent, hpt, hfin, FiniteAdelicGL.localProjection_localInclusion]

end Langlands.Global.RankinSelbergGlobal.EqualEulerSchwartz
