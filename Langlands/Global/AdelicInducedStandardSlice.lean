import Langlands.Global.AdelicInducedPrincipalSeries
import Langlands.Representation.Archimedean.RealStandardCompactBlockSlices

/-! # Standard-module coordinates from block coefficient orbits -/

noncomputable section

universe uF uV uR

namespace Langlands.Global.AdelicParabolicInduction

open NumberField Langlands.GeneralLinear AdelicBlockParabolic AdelicBlockDeterminantCharacter
open Langlands.Archimedean Langlands.LocalFactor.Archimedean RealLeviChart RealLeviSlices
open scoped BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable (F : Type uF) [Field F] [NumberField F]
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]

section BlockOrbit

variable {R : Type uR} [RCLike R] {n : ℕ} (B : BlockShape n)
variable (σ : Representation ℂ (FullLevi F B) V)
variable (ι : ∀ i, Langlands.GeneralLinear (B.size i) R →* AdelicGL F (B.size i))

/-- The single-place homomorphism on the full block Levi acts coordinatewise. -/
private def blockPlaceLevi : B.Levi R →* FullLevi F B :=
  MonoidHom.pi fun i => (ι i).comp (Pi.evalMonoidHom _ i)

/-- Evaluate a scalar coefficient functional along one local diagonal block. -/
def blockCoefficientOrbit (ℓ : V →L[ℂ] ℂ) (i : Fin B.length) (z : V) :
    Langlands.GeneralLinear (B.size i) R → ℂ :=
  fun g => ℓ (σ (blockPlaceLevi F B ι (Pi.mulSingle i g)) z)

private theorem coefficient_product (ℓ : V →L[ℂ] ℂ) (m : B.Levi R)
    (eigenvalue : Fin B.length → ℂ)
    (hm : ∀ i z, blockCoefficientOrbit F B σ ι ℓ i z (m i) = eigenvalue i * ℓ z) (z : V) :
    ℓ (σ (blockPlaceLevi F B ι m) z) = (∏ i, eigenvalue i) * ℓ z := by
  classical
  let restrict (s : Finset (Fin B.length)) : B.Levi R := fun i => if i ∈ s then m i else 1
  have hs (s : Finset (Fin B.length)) (w : V) :
      ℓ (σ (blockPlaceLevi F B ι (restrict s)) w) = (∏ i ∈ s, eigenvalue i) * ℓ w := by
    induction s using Finset.induction_on with
    | empty =>
        have he : restrict ∅ = 1 := by funext i; simp [restrict]
        rw [he, map_one, map_one, Finset.prod_empty, one_mul, Module.End.one_apply]
    | insert i s hi ih =>
        have hi' : restrict (insert i s) = Pi.mulSingle i (m i) * restrict s := by
          funext j
          by_cases hj : j = i
          · subst j
            simp [restrict, hi]
          · simp [restrict, hj]
        rw [hi', map_mul, map_mul, Module.End.mul_apply]
        rw [← blockCoefficientOrbit, hm, ih, Finset.prod_insert hi, mul_assoc]
  have hu : restrict Finset.univ = m := by funext i; simp [restrict]
  simpa only [hu] using hs Finset.univ z

private theorem coefficient_borel
    {c : ℕ} (size : Fin c → ℕ) (hsize : ∀ i, 0 < size i)
    (τ : Representation ℂ (FullLevi F (orderedBlockShape size hsize)) V)
    (jv : ∀ i, Langlands.GeneralLinear (size i) R →* AdelicGL F (size i))
    (ℓ : V →L[ℂ] ℂ) (χ : Fin c → ℕ → Rˣ → ℂ)
    (hℓ : ∀ i z, blockCoefficientOrbit F (orderedBlockShape size hsize) τ jv ℓ i z ∈
      principalSeries R (size i) (χ i))
    (a : Fin (∑ i, size i) → Rˣ)
    (u : Langlands.GeneralLinear.upperUnipotent (∑ i, size i) R) (z : V) :
    ℓ (τ (fun i => jv i (Iwasawa.diagonalUnits (fun j => a (pos size i j)) *
        (borelBlockUnipotent size hsize R u i).val)) z) =
      (∏ i : Fin c, principalSeriesCharacter R (size i) (χ i) (fun j => a (pos size i j))) *
        ℓ z := by
  apply coefficient_product F (orderedBlockShape size hsize) τ jv ℓ
    (fun i => Iwasawa.diagonalUnits (fun j => a (pos size i j)) *
      (borelBlockUnipotent size hsize R u i).val)
  intro i w
  have h := (hℓ i w).2 (fun j => a (pos size i j)) (borelBlockUnipotent size hsize R u i) 1
  simpa only [mul_one, blockCoefficientOrbit, Pi.mulSingle_one, map_one, Module.End.one_apply]
    using h

end BlockOrbit

section Real

variable {c : ℕ} (ds : Fin c → List RealBlock) (hsize : ∀ i, 0 < sz ds i)

local notation "B" => orderedBlockShape (sz ds) hsize
local notation "N" => (∑ i, sz ds i)

private theorem orderedLeviEmbedding_eq (m : (B).Levi ℝ) :
    (B).leviEmbedding ℝ m = blockDiagGL (sz ds) m := by
  apply Units.ext
  refine Matrix.ext fun p q => ?_
  obtain ⟨⟨i, a⟩, rfl⟩ := finSigmaFinEquiv.surjective p
  obtain ⟨⟨j, b⟩, rfl⟩ := finSigmaFinEquiv.surjective q
  change ((B).leviEmbedding ℝ m).val (pos (sz ds) i a) (pos (sz ds) j b) =
    blockDiagHom (sz ds) (fun i => (m i).val) (pos (sz ds) i a) (pos (sz ds) j b)
  change ((B).leviEmbedding ℝ m).val ((B).index i a) ((B).index j b) = _
  by_cases hij : i = j
  · subst j
    rw [BlockShape.leviEmbedding_apply_same, blockDiagHom_pos_pos_self]
  · rw [BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hij, blockDiagHom_pos_pos_of_ne _ _ hij]

/-- If the real local orbits of the coefficient functional are in the block standard
modules, the scalar coordinate of the adelic section is in the concatenated standard
module. -/
theorem realPlaceSlice_mem_standardModule
    (σ : Representation ℂ (FullLevi F (orderedBlockShape (sz ds) hsize)) V)
    (v : {w : InfinitePlace F // InfinitePlace.IsReal w}) (y : AdelicGL F N)
    (hy : ∀ p : (B).parabolic ℝ, Commute y (AdelicBlockParabolic.realPlaceInclusion F B v p).val)
    (ℓ : V →L[ℂ] ℂ)
    (hℓ : ∀ i z, blockCoefficientOrbit F B σ
      (fun i => AdelicGL.realPlaceInclusion F (sz ds i) v) ℓ i z ∈
        realStandardModule (sz ds i) (ds i))
    (f : SmoothSections F B σ) :
    realPlaceSlice F B σ v y ℓ f ∈ realStandardModule N (flat ds) := by
  refine realStandardMembershipFromCompactBlockSlices ds _ ?_ ?_
  · refine realPlaceSlice_mem_principalSeries (sz ds) hsize F σ v y hy
      (realPositionCharacter (flat ds)) (fun i => realPositionCharacter (ds i)) ?_ ℓ ?_ f
    · intro i j
      rw [val_pos]
      exact realPositionCharacter_flat ds i j j.isLt
    · exact coefficient_borel F (sz ds) hsize σ
        (fun i => AdelicGL.realPlaceInclusion F (sz ds i) v) ℓ
        (fun i => realPositionCharacter (ds i)) (fun i z => (hℓ i z).1)
  · intro i g
    let jv (j : Fin c) := AdelicGL.realPlaceInclusion F (sz ds j) v
    let z := evaluate F B σ f.val (y * AdelicGL.realPlaceInclusion F N v g)
    refine ⟨blockCoefficientOrbit F B σ jv ℓ i z, hℓ i z, fun k => ?_⟩
    let m : (B).Levi ℝ := Pi.mulSingle i k.val
    let p := (B).leviInParabolic ℝ m
    have hp : p.val = emb (sz ds) i k.val := by
      rw [show p.val = (B).leviEmbedding ℝ m from rfl, orderedLeviEmbedding_eq, emb_eq]
    have hdet (j : Fin c) : |(m j).val.det| = 1 := by
      by_cases hj : j = i
      · subst j
        simpa only [m, Pi.mulSingle_eq_same] using MaximalParabolicIntegration.abs_det_unitary k
      · simp [m, Pi.mulSingle_eq_of_ne hj]
    have hmod : realPlaceModulusValue B p = 1 := by
      rw [realPlaceModulusValue, show (B).leviProjection ℝ p = m from
        (B).leviProjection_section ℝ m]
      refine Finset.prod_eq_one fun j _ => Finset.prod_eq_one fun l _ => ?_
      simp only [hdet, one_pow, div_one]
    let pv := AdelicBlockParabolic.realPlaceInclusion F B v p
    have hm : y * AdelicGL.realPlaceInclusion F N v (p.val * g) =
        pv.val * (y * AdelicGL.realPlaceInclusion F N v g) := by
      rw [map_mul, ← mul_assoc, ← realPlaceInclusion_val F B v p, (hy p).eq, mul_assoc]
    have hhalf : (parabolicHalfCharacter F B pv : ℂ) = 1 := by
      rw [coe_parabolicHalfCharacter_realPlace, hmod, Real.sqrt_one, Complex.ofReal_one]
    have hlevi : (B).leviProjection (Adeles F) pv = blockPlaceLevi F B jv m := by
      rw [leviProjection_realPlaceInclusion, (B).leviProjection_section ℝ m]
      rfl
    change ℓ (evaluate F B σ f.val
      (y * AdelicGL.realPlaceInclusion F N v (emb (sz ds) i k.val * g))) = _
    rw [← hp, hm, covariance]
    change ℓ ((parabolicHalfCharacter F B pv : ℂ) • σ ((B).leviProjection (Adeles F) pv) z) = _
    rw [hhalf, one_smul, hlevi]
    rfl

end Real

section Complex

private theorem complexPositionCharacter_append_left (xs ys : List ComplexCharacterData)
    (a : ℕ) (ha : a < xs.length) :
    complexPositionCharacter (xs ++ ys) a = complexPositionCharacter xs a := by
  induction xs generalizing a with
  | nil => simp at ha
  | cons d xs ih =>
      cases a with
      | zero => rfl
      | succ a =>
          exact ih a (Nat.lt_of_succ_lt_succ ha)

private theorem complexPositionCharacter_append_right (xs ys : List ComplexCharacterData) (a : ℕ) :
    complexPositionCharacter (xs ++ ys) (xs.length + a) = complexPositionCharacter ys a := by
  induction xs with
  | nil => simp
  | cons d xs ih =>
      simpa only [List.cons_append, List.length_cons, Nat.succ_add, complexPositionCharacter]
        using ih

private theorem complexPositionCharacter_flat : ∀ {c : ℕ}
    (ds : Fin c → List ComplexCharacterData) (i : Fin c) (a : Fin (ds i).length),
    complexPositionCharacter (List.ofFn ds).flatten (pos (fun j => (ds j).length) i a) =
      complexPositionCharacter (ds i) a
  | 0, _, i, _ => i.elim0
  | c + 1, ds, i, a => by
      rw [List.ofFn_succ, List.flatten_cons, val_pos]
      revert a
      induction i using Fin.cases with
      | zero =>
          intro a
          rw [Fin.val_zero, start_zero', zero_add]
          exact complexPositionCharacter_append_left _ _ a a.isLt
      | succ i =>
          intro a
          rw [Fin.val_succ, start_succ', add_assoc, complexPositionCharacter_append_right]
          rw [← val_pos (fun j : Fin c => (ds j.succ).length) i a]
          exact complexPositionCharacter_flat (fun j => ds j.succ) i a

variable {c : ℕ} (ds : Fin c → List ComplexCharacterData) (hsize : ∀ i, 0 < (ds i).length)

local notation "blockSize" => (fun i => List.length (ds i))
local notation "B" => orderedBlockShape blockSize hsize
local notation "N" => (∑ i, blockSize i)

/-- At a complex place the principal-series comparison gives the standard module of
the concatenated block characters. -/
theorem complexPlaceSlice_mem_standardModule
    (σ : Representation ℂ (FullLevi F (orderedBlockShape (fun i => (ds i).length) hsize)) V)
    (v : {w : InfinitePlace F // InfinitePlace.IsComplex w}) (y : AdelicGL F N)
    (hy : ∀ p : (B).parabolic ℂ, Commute y (AdelicBlockParabolic.complexPlaceInclusion F B v p).val)
    (ℓ : V →L[ℂ] ℂ)
    (hℓ : ∀ i z, blockCoefficientOrbit F B σ
      (fun i => AdelicGL.complexPlaceInclusion F (ds i).length v) ℓ i z ∈
        complexStandardModule (ds i).length (ds i))
    (f : SmoothSections F B σ) :
    complexPlaceSlice F B σ v y ℓ f ∈ complexStandardModule N (List.ofFn ds).flatten := by
  refine complexPlaceSlice_mem_principalSeries blockSize hsize F σ v y hy
    (complexPositionCharacter (List.ofFn ds).flatten)
    (fun i => complexPositionCharacter (ds i)) (complexPositionCharacter_flat ds) ℓ ?_ f
  exact coefficient_borel F blockSize hsize σ
    (fun i => AdelicGL.complexPlaceInclusion F (ds i).length v) ℓ
    (fun i => complexPositionCharacter (ds i)) hℓ

end Complex

end Langlands.Global.AdelicParabolicInduction
