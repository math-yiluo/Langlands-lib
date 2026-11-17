import Langlands.Global.RankinSelberg.RectangularDiagonalCorrection
import Langlands.Global.RankinSelberg.AdelicSimpleRootGauge

/-! # Finite-place support bounds for actual adelic rectangular charts -/

noncomputable section
universe u v
open NumberField
open scoped NNReal
set_option autoImplicit false

namespace Langlands.GeneralLinear.RectangularIwasawa

section Maps

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    (f : R →+* S) {a d c : ℕ}

theorem map_lowerBlockPair_one
    (g : Langlands.GeneralLinear a R) (x : Matrix (Fin d) (Fin a) R) :
    Matrix.GeneralLinearGroup.map f (lowerBlockPair g x 1) =
      lowerBlockPair (Matrix.GeneralLinearGroup.map f g) (x.map f) 1 := by
  apply Units.ext
  ext i j
  change f (lowerBlockPair g x 1 i j) = _
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => simp
    | right j => simp
  | right i =>
    induction j using Fin.addCases with
    | left j => simp
    | right j => simp [Matrix.one_apply]

theorem map_extendRectangle (x : Matrix (Fin d) (Fin a) R) :
    (extendRectangle c x).map f = extendRectangle c (x.map f) := by
  ext i j
  induction i using Fin.addCases with
  | left i => simp [extendRectangle]
  | right i => simp [extendRectangle]

/-- For a final block of rank one, the association of natural-number
indices is definitionally the standard association. -/
theorem lowerBlockLocalization_one_eq_pair
    (g : Langlands.GeneralLinear a R) (x : Matrix (Fin d) (Fin a) R) :
    lowerBlockLocalization 1 g x 1 = lowerBlockPair g (extendRectangle 1 x) 1 := by
  exact lowerBlockLocalization_reindex (c := 1) g x

theorem map_lowerBlockLocalization_one
    (g : Langlands.GeneralLinear a R) (x : Matrix (Fin d) (Fin a) R) :
    Matrix.GeneralLinearGroup.map f (lowerBlockLocalization 1 g x 1) =
      lowerBlockLocalization 1 (Matrix.GeneralLinearGroup.map f g) (x.map f) 1 := by
  rw [lowerBlockLocalization_one_eq_pair, map_lowerBlockPair_one f g (extendRectangle 1 x),
    map_extendRectangle, lowerBlockLocalization_one_eq_pair]

end Maps

end Langlands.GeneralLinear.RectangularIwasawa

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.GeneralLinear.RectangularIwasawa PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F]

/-- A local radius for the finite projections of an idelic simple-root
tuple, bounded below by one. -/
def finiteSimpleRootRadius (r : ℕ) (c : Fin (r + 1) → Ideles F)
    (v : FinitePlace F) : ℝ :=
  max 1 ‖fun i : Fin r => finiteProjection F v
    ((c i.castSucc / c i.succ : Ideles F) : Adeles F)‖

theorem finiteProjection_norm_le_one_of_standardCompact {n : ℕ}
    (K : AdelicGL F n) (hK : K ∈ standardCompact F n) (v : FinitePlace F)
    (i j : Fin n) :
    ‖finiteProjection F v (K i j)‖ ≤ 1 := by
  have hk := ((mem_standardCompact_iff F n K).mp hK).2
  have hint := ((FiniteAdelicGL.mem_standardIntegral F n _).mp hk).1 i j v
  change finiteProjection F v (K i j) ∈ v.adicCompletionIntegers F at hint
  simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    ← Valued.toNormedField.norm_le_one_iff] using hint

private theorem map_units_div {R : Type*} [CommRing R] {𝕜 : Type*} [Field 𝕜]
    (f : R →+* 𝕜) (b c : Rˣ) :
    f ((b / c : Rˣ) : R) = f (b : R) / f (c : R) := by
  change ((Units.map f.toMonoidHom (b / c) : 𝕜ˣ) : 𝕜) = _
  rw [map_div, Units.val_div_eq_div_val]
  rfl

/-- The finite-place polynomial support bound on the actual adelic
three-block chart. -/
theorem finiteProjection_rectangular_coordinate_le
    {a d : ℕ} (g : AdelicGL F a)
    (x : Matrix (Fin d) (Fin a) (Adeles F))
    (U K : AdelicGL F (a + d + 1)) (c : Fin (a + d + 1) → Ideles F)
    (hU : IsUnitriangular U.val) (hK : K ∈ standardCompact F (a + d + 1))
    (hfac : GeneralLinear.lowerBlockLocalization 1 g x 1 = U * diagonalGL c * K)
    (v : FinitePlace F) (i : Fin d) (j : Fin a) :
    ‖finiteProjection F v (x i j)‖ ≤
      rectangularSupportRadius d (finiteSimpleRootRadius F (a + d) c v) := by
  let f := finiteProjection F v
  let B := Matrix.GeneralLinearGroup.map f (U * diagonalGL c)
  let k := Matrix.GeneralLinearGroup.map f K
  let gx := Matrix.GeneralLinearGroup.map f g
  let xx := x.map f
  have hB : B.val.IsUpperTriangular := by
    change ((U.val * (diagonalGL c).val).map f).IsUpperTriangular
    exact (hU.1.mul (Matrix.blockTriangular_diagonal _)).map f
  have hdiag (q : Fin (a + d + 1)) : B q q = f (c q : Adeles F) := by
    change f ((U.val * (diagonalGL c).val) q q) = _
    rw [diagonalGL, Matrix.mul_diagonal, hU.2 q, one_mul]
  have hk : ∀ p q, ‖k p q‖ ≤ 1 :=
    finiteProjection_norm_le_one_of_standardCompact F K hK v
  have hki : ∀ p q, ‖k⁻¹ p q‖ ≤ 1 := by
    have hh := finiteProjection_norm_le_one_of_standardCompact F K⁻¹
      ((standardCompact F _).inv_mem hK) v
    intro p q
    dsimp only [k]
    rw [← map_inv]
    change ‖f (K⁻¹ p q)‖ ≤ 1
    exact hh p q
  have hlocal :
      GeneralLinear.lowerBlockLocalization 1 gx xx 1 = B * k := by
    have hh := congrArg (Matrix.GeneralLinearGroup.map f) hfac
    rw [map_lowerBlockLocalization_one f, map_mul] at hh
    exact hh
  have hR : 1 ≤ finiteSimpleRootRadius F (a + d) c v := le_max_left _ _
  have hroot (q : Fin d) :
      ‖B (q.castSucc.natAdd a) (q.castSucc.natAdd a) /
        B (q.succ.natAdd a) (q.succ.natAdd a)‖ ≤
          finiteSimpleRootRadius F (a + d) c v := by
    rw [hdiag, hdiag, ← map_units_div]
    have hleft : (q.natAdd a : Fin (a + d)).castSucc = q.castSucc.natAdd a := by
      apply Fin.ext
      rfl
    have hright : (q.natAdd a : Fin (a + d)).succ = q.succ.natAdd a := by
      apply Fin.ext
      simp [Nat.add_assoc]
    have hh := norm_le_pi_norm
      (fun p : Fin (a + d) => f ((c p.castSucc / c p.succ : Ideles F) : Adeles F))
      (q.natAdd a)
    rw [hleft, hright] at hh
    exact hh.trans (le_max_right _ _)
  exact norm_lowerBlockLocalization_coordinate_le_of_roots_ultrametric gx xx B k hB hk hki
    hlocal (finiteSimpleRootRadius F (a + d) c v) hR hroot i j

/-- Integral finite simple roots force integral finite rectangular
coordinates, with no rank-dependent enlargement of the unit ball. -/
theorem finiteProjection_rectangular_coordinate_integral
    {a d : ℕ} (g : AdelicGL F a)
    (x : Matrix (Fin d) (Fin a) (Adeles F))
    (U K : AdelicGL F (a + d + 1)) (c : Fin (a + d + 1) → Ideles F)
    (hU : IsUnitriangular U.val) (hK : K ∈ standardCompact F (a + d + 1))
    (hfac : GeneralLinear.lowerBlockLocalization 1 g x 1 = U * diagonalGL c * K)
    (v : FinitePlace F)
    (hroot : ∀ q : Fin (a + d),
      finiteProjection F v ((c q.castSucc / c q.succ : Ideles F) : Adeles F) ∈
        v.adicCompletionIntegers F) (i : Fin d) (j : Fin a) :
    finiteProjection F v (x i j) ∈ v.adicCompletionIntegers F := by
  have hr : ‖fun q : Fin (a + d) => finiteProjection F v
      ((c q.castSucc / c q.succ : Ideles F) : Adeles F)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro q
    simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff] using hroot q
  have hh := finiteProjection_rectangular_coordinate_le F g x U K c hU hK hfac v i j
  simp only [finiteSimpleRootRadius, max_eq_left hr, rectangularSupportRadius, one_pow] at hh
  simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    ← Valued.toNormedField.norm_le_one_iff] using hh

end Langlands.Global.RankinSelbergGlobal
