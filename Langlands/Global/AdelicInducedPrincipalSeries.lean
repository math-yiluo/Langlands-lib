import Langlands.Global.AdelicBlockParabolicPlaceNorm
import Langlands.Global.AdelicInducedArchimedeanSlice
import Langlands.Representation.Archimedean.BlockPrincipalSeriesNormalization
import Langlands.Group.GL.TriangularParabolic

/-! # Scalar principal-series coordinates of actual local section restrictions -/

noncomputable section

universe uF uV uR

namespace Langlands.Global.AdelicParabolicInduction

open NumberField Langlands.GeneralLinear AdelicBlockParabolic
open Langlands.Archimedean RealLeviChart
open scoped BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {c : ℕ} (size : Fin c → ℕ)
variable (hsize : ∀ i, 0 < size i)

/-- The actual block shape in the ordered sum of its block ranks. -/
abbrev orderedBlockShape : BlockShape (∑ i, size i) :=
  ⟨c, size, hsize, rfl⟩

local notation "B" => orderedBlockShape size hsize

private theorem orderedBlockShape_index (i : Fin c) (j : Fin (size i)) :
    (B).index i j = pos size i j := by
  simp [orderedBlockShape, BlockShape.index, BlockShape.indexEquiv, pos]

section Borel

variable (R : Type uR) [Field R]

private def diagonalParabolic (a : Fin (∑ i, size i) → Rˣ) : (B).parabolic R :=
  ⟨Iwasawa.diagonalUnits a, (B).mem_parabolic_of_isUpperTriangular _ (by
    intro i j hj
    change (Iwasawa.diagonalUnits a).val i j = 0
    rw [Iwasawa.diagonalUnits_val]
    exact Matrix.diagonal_apply_ne _ (ne_of_gt (show j < i from hj)))⟩

private def unipotentParabolic (u : Langlands.GeneralLinear.upperUnipotent (∑ i, size i) R) : (B).parabolic R :=
  ⟨u.val, (B).mem_parabolic_of_isUpperTriangular _ u.property.1⟩

/-- A diagonal element times an upper unipotent lies in the ordered block parabolic. -/
def borelParabolic (a : Fin (∑ i, size i) → Rˣ) (u : Langlands.GeneralLinear.upperUnipotent (∑ i, size i) R) :
    (B).parabolic R :=
  diagonalParabolic size hsize R a * unipotentParabolic size hsize R u

/-- The diagonal blocks of an upper unipotent matrix are upper unipotent. -/
def borelBlockUnipotent (u : Langlands.GeneralLinear.upperUnipotent (∑ i, size i) R) (i : Fin c) :
    Langlands.GeneralLinear.upperUnipotent (size i) R :=
  ⟨(B).leviProjection R (unipotentParabolic size hsize R u) i, by
    constructor
    · intro j k hkj
      rw [BlockShape.leviProjection_apply, orderedBlockShape_index, orderedBlockShape_index]
      change u.val (pos size i j) (pos size i k) = 0
      apply u.property.1
      change (pos size i k : ℕ) < (pos size i j : ℕ)
      rw [val_pos, val_pos]
      exact Nat.add_lt_add_left hkj _
    · intro a
      rw [BlockShape.leviProjection_apply]
      exact u.property.2 _⟩

private theorem leviProjection_diagonalParabolic (a : Fin (∑ i, size i) → Rˣ) (i : Fin c) :
    (B).leviProjection R (diagonalParabolic size hsize R a) i =
      Iwasawa.diagonalUnits (fun j => a (pos size i j)) := by
  apply Units.ext
  ext j k
  rw [BlockShape.leviProjection_apply]
  change (Iwasawa.diagonalUnits a).val ((B).index i j) ((B).index i k) = _
  simp only [Iwasawa.diagonalUnits_val, Matrix.diagonal_apply,
    ((B).index i).injective.eq_iff]
  rfl

theorem leviProjection_borelParabolic
    (a : Fin (∑ i, size i) → Rˣ) (u : Langlands.GeneralLinear.upperUnipotent (∑ i, size i) R) (i : Fin c) :
    (B).leviProjection R (borelParabolic size hsize R a u) i =
      Iwasawa.diagonalUnits (fun j => a (pos size i j)) *
        (borelBlockUnipotent size hsize R u i).val := by
  rw [borelParabolic, map_mul, Pi.mul_apply, leviProjection_diagonalParabolic]
  rfl

private theorem leviProjection_borelParabolic_det
    (a : Fin (∑ i, size i) → Rˣ) (u : Langlands.GeneralLinear.upperUnipotent (∑ i, size i) R) (i : Fin c) :
    ((B).leviProjection R (borelParabolic size hsize R a u) i).val.det =
      (Iwasawa.diagonalUnits (fun j => a (pos size i j))).val.det := by
  let w := borelBlockUnipotent size hsize R u i
  have hw : w.val.val.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular w.property.1]
    simp only [w.property.2, Finset.prod_const_one]
  rw [leviProjection_borelParabolic, Units.val_mul, Matrix.det_mul, hw, mul_one]

end Borel

variable (F : Type uF) [Field F] [NumberField F]
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]

private theorem scalarRestriction_covariance {R : Type uR} [CommRing R] {N : ℕ}
    (S : BlockShape N) (τ : Representation ℂ (FullLevi F S) V)
    (ι : Langlands.GeneralLinear N R →* AdelicGL F N)
    (ιP : S.parabolic R →* Full F S) (hι : ∀ p, (ιP p).val = ι p.val)
    (y : AdelicGL F N) (ℓ : V →L[ℂ] ℂ) (f : SmoothSections F S τ)
    (p : S.parabolic R) (hy : Commute y (ιP p).val) (g : Langlands.GeneralLinear N R) :
    ℓ (evaluate F S τ f.val (y * ι (p.val * g))) =
      (AdelicBlockDeterminantCharacter.parabolicHalfCharacter F S (ιP p) : ℂ) *
        ℓ (τ (S.leviProjection (Adeles F) (ιP p)) (evaluate F S τ f.val (y * ι g))) := by
  have hm : y * ι (p.val * g) = (ιP p).val * (y * ι g) := by
    rw [map_mul, ← mul_assoc, ← hι p, hy.eq, mul_assoc]
  rw [hm, covariance, map_smul, smul_eq_mul]
  rfl

open AdelicBlockDeterminantCharacter

/-- At a real place, a coefficient functional with the inner Borel character
gives a scalar coordinate in the full normalized principal series. -/
theorem realPlaceSlice_mem_principalSeries
    (σ : Representation ℂ (FullLevi F (orderedBlockShape size hsize)) V)
    (v : {w : InfinitePlace F // InfinitePlace.IsReal w}) (y : AdelicGL F (∑ i, size i))
    (hy : ∀ p : (B).parabolic ℝ, Commute y (AdelicBlockParabolic.realPlaceInclusion F B v p).val)
    (χ : ℕ → ℝˣ → ℂ) (χblock : Fin c → ℕ → ℝˣ → ℂ)
    (hχ : ∀ (i : Fin c) (j : Fin (size i)), χ (pos size i j) = χblock i j)
    (ℓ : V →L[ℂ] ℂ)
    (hℓ : ∀ (a : Fin (∑ i, size i) → ℝˣ) (u : Langlands.GeneralLinear.upperUnipotent (∑ i, size i) ℝ) (z : V),
      ℓ (σ (fun i => AdelicGL.realPlaceInclusion F (size i) v
        (Iwasawa.diagonalUnits (fun j => a (pos size i j)) *
          (borelBlockUnipotent size hsize ℝ u i).val)) z) =
        (∏ i : Fin c, principalSeriesCharacter ℝ (size i) (χblock i) (fun j => a (pos size i j))) *
          ℓ z)
    (f : SmoothSections F B σ) :
    realPlaceSlice F B σ v y ℓ f ∈ principalSeries ℝ (∑ i, size i) χ := by
  refine ⟨realPlaceSlice_contMDiff F B σ v y ℓ f, fun a u g => ?_⟩
  let p := borelParabolic size hsize ℝ a u
  have hc := scalarRestriction_covariance F B σ (AdelicGL.realPlaceInclusion F _ v)
    (AdelicBlockParabolic.realPlaceInclusion F B v) (realPlaceInclusion_val F B v) y ℓ f p (hy p) g
  have hm : realPlaceModulusValue B p =
      ∏ i : Fin c, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        blockDiagonalAbs size ℝ a i ^ size j / blockDiagonalAbs size ℝ a j ^ size i := by
    unfold realPlaceModulusValue
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    dsimp only [p]
    rw [leviProjection_borelParabolic_det size hsize ℝ a u i,
      leviProjection_borelParabolic_det size hsize ℝ a u j]
    simp only [blockDiagonalAbs, Module.finrank_self, pow_one, Real.norm_eq_abs]
  change ℓ (evaluate F B σ f.val
    (y * AdelicGL.realPlaceInclusion F _ v (p.val * g))) = _
  rw [hc, coe_parabolicHalfCharacter_realPlace, hm, leviProjection_realPlaceInclusion]
  simp_rw [p, leviProjection_borelParabolic]
  rw [hℓ, principalSeriesCharacter_eq_outerHalf_mul_inner size ℝ χ χblock hχ, mul_assoc]
  rfl

/-- At a complex place the inner Borel character gives the full principal-series
coordinate with the squared local determinant normalization. -/
theorem complexPlaceSlice_mem_principalSeries
    (σ : Representation ℂ (FullLevi F (orderedBlockShape size hsize)) V)
    (v : {w : InfinitePlace F // InfinitePlace.IsComplex w}) (y : AdelicGL F (∑ i, size i))
    (hy : ∀ p : (B).parabolic ℂ, Commute y (AdelicBlockParabolic.complexPlaceInclusion F B v p).val)
    (χ : ℕ → ℂˣ → ℂ) (χblock : Fin c → ℕ → ℂˣ → ℂ)
    (hχ : ∀ (i : Fin c) (j : Fin (size i)), χ (pos size i j) = χblock i j)
    (ℓ : V →L[ℂ] ℂ)
    (hℓ : ∀ (a : Fin (∑ i, size i) → ℂˣ) (u : Langlands.GeneralLinear.upperUnipotent (∑ i, size i) ℂ) (z : V),
      ℓ (σ (fun i => AdelicGL.complexPlaceInclusion F (size i) v
        (Iwasawa.diagonalUnits (fun j => a (pos size i j)) *
          (borelBlockUnipotent size hsize ℂ u i).val)) z) =
        (∏ i : Fin c, principalSeriesCharacter ℂ (size i) (χblock i) (fun j => a (pos size i j))) *
          ℓ z)
    (f : SmoothSections F B σ) :
    complexPlaceSlice F B σ v y ℓ f ∈ principalSeries ℂ (∑ i, size i) χ := by
  refine ⟨complexPlaceSlice_contMDiff F B σ v y ℓ f, fun a u g => ?_⟩
  let p := borelParabolic size hsize ℂ a u
  have hc := scalarRestriction_covariance F B σ (AdelicGL.complexPlaceInclusion F _ v)
    (AdelicBlockParabolic.complexPlaceInclusion F B v) (complexPlaceInclusion_val F B v) y ℓ f p
    (hy p) g
  have hm : complexPlaceModulusValue B p =
      ∏ i : Fin c, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        blockDiagonalAbs size ℂ a i ^ size j / blockDiagonalAbs size ℂ a j ^ size i := by
    unfold complexPlaceModulusValue
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    dsimp only [p]
    rw [leviProjection_borelParabolic_det size hsize ℂ a u i,
      leviProjection_borelParabolic_det size hsize ℂ a u j]
    simp only [blockDiagonalAbs, Complex.finrank_real_complex]
  change ℓ (evaluate F B σ f.val
    (y * AdelicGL.complexPlaceInclusion F _ v (p.val * g))) = _
  rw [hc, coe_parabolicHalfCharacter_complexPlace, hm, leviProjection_complexPlaceInclusion]
  simp_rw [p, leviProjection_borelParabolic]
  rw [hℓ, principalSeriesCharacter_eq_outerHalf_mul_inner size ℂ χ χblock hχ, mul_assoc]
  rfl

end Langlands.Global.AdelicParabolicInduction
