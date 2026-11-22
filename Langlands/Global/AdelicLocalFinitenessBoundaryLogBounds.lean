import Langlands.Global.AdelicLocalFinitenessTorusCoordinates
import Langlands.GroupScheme.Rational.ParabolicCharacterLattice
import Mathlib.Analysis.Normed.Group.Constructions

/-! # Root and central log bounds on the polynomial boundary -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory Module Set
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus Langlands.LinearAlgebra.RationalSpan

variable (F : Type u) [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local notation "Δ" => simpleRelativeRoots i ν
local notation "Root" => Subtype (fun χ => χ ∈ simpleRelativeRoots i ν)
local notation "V" => RealCharacterDual F T.toGrp

omit [NumberField F] in
/-- A finite character basis of the ambient group supplies the auxiliary
characters in the relatively cuspidal boundary estimate. -/
theorem exists_finite_ambient_characters_span (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) :
    ∃ Zχ : Set (characterLattice T), Zχ.Finite ∧ Zχ ⊆ range (torusCharacterRestrict i) ∧
      ratSpan (Δ ∪ Zχ) = ⊤ := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨hFree, hFinite⟩ := rationalCharacters_free_finite_of_smooth G
  let : Module.Free ℤ (rationalCharacters G) := hFree
  let : Module.Finite ℤ (rationalCharacters G) := hFinite
  let J := Module.Free.ChooseBasisIndex ℤ (rationalCharacters G)
  let : Fintype J := Fintype.ofFinite J
  let b := Module.Free.chooseBasis ℤ (rationalCharacters G)
  let Zχ := range (fun j : J => torusCharacterRestrict i (b j))
  refine ⟨Zχ, finite_range _, (fun _ ⟨j, hj⟩ => ⟨b j, hj⟩), ?_⟩
  have hspan := simpleRelativeRoots_restrictedCharacters_ratSpan_eq_top F G T i ν hG hi hν
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨χ, hχ | ⟨ξ, rfl⟩, rfl⟩
  · exact toRat_mem_ratSpan (Or.inl hχ)
  · let f := toRat.comp (torusCharacterRestrict i)
    change f ξ ∈ ratSpan (Δ ∪ Zχ)
    have hf := congrArg f (b.sum_repr ξ)
    rw [← hf, map_sum]
    apply Submodule.sum_mem
    intro j _
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
    exact Submodule.smul_mem _ _ (toRat_mem_ratSpan (Or.inr ⟨j, rfl⟩))

/-- Lower root thresholds and upper bounds on the roots outside a given Levi
and on the central coordinates imply all the log bounds of the relative
cuspidal restriction estimate. -/
def AdelicLocalFinitenessBoundaryLogBoundsStatement {r : ℕ}
    (e : V ≃L[ℝ] ((Root → ℝ) × (Fin r → ℝ))) (rate : Root → ℝ) : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
  (∀ α, 0 < rate α) →
  (∀ (h : V) (α : Root), (e h).1 α = h α.val / rate α) →
  (∀ h : V, (e h).2 = 0 → realCharacterDualMap F T.toGrp G i h = 0) →
  ∃ Zχ : Set (characterLattice T), Zχ.Finite ∧ ratSpan (Δ ∪ Zχ) = ⊤ ∧
  ∀ (Pidx : Set (characterLattice T)) (τ κ : Root → ℝ) (m : Fin r → ℝ),
    ∃ (b B : ℝ), 0 ≤ B ∧
    ∀ (h : V) (x : (Root → ℝ) × (Fin r → ℝ)), x = e h →
      (∀ α : Root, τ α ≤ x.1 α) → (∀ α : Root, α.val ∉ Pidx → x.1 α ≤ κ α) →
      (∀ j, |x.2 j| ≤ m j) →
      (∀ α ∈ Δ, b ≤ h α) ∧
      (∀ χ ∈ Zχ, |h χ| ≤ B) ∧
      (∀ α ∈ Δ \ Pidx, |h α| ≤ B)

omit [NumberField F] in
theorem adelicLocalFinitenessBoundaryLogBounds {r : ℕ}
    (e : V ≃L[ℝ] ((Root → ℝ) × (Fin r → ℝ))) (rate : Root → ℝ) :
    AdelicLocalFinitenessBoundaryLogBoundsStatement F i ν e rate := by
  intro hG hi hν hPos hRoot hCenter
  let : Smooth G.X.hom := hG.smooth
  let : Fintype Root := (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).fintype
  obtain ⟨Zχ, hZ, hZamb, hSpan⟩ := exists_finite_ambient_characters_span F i ν hG hi hν
  refine ⟨Zχ, hZ, hSpan, fun Pidx τ κ m => ?_⟩
  let lower : ℝ := -∑ α, |τ α * rate α|
  let box : Set (Fin r → ℝ) := Set.Icc (fun j => -m j) m
  have hBox : IsCompact box := isCompact_Icc
  let s := hZ.toFinset
  let c (y : Fin r → ℝ) : V := e.symm (0, y)
  have hc : Continuous c := e.symm.continuous.comp (continuous_const.prodMk continuous_id)
  let C (y : Fin r → ℝ) : ℝ := ∑ χ ∈ s, |c y χ|
  have hC : Continuous C := continuous_finsetSum _ fun χ _ =>
    ((continuous_dualEval F T.toGrp χ).comp hc).abs
  obtain ⟨M, hM⟩ := (hBox.image hC).bddAbove
  let D : ℝ := ∑ α, (|τ α| + |κ α|) * rate α
  let B := max 0 (max M D)
  refine ⟨lower, B, le_max_left _ _, fun h x hx hLower hUpper hCent => ?_⟩
  have hroot (α : Root) : h α.val = x.1 α * rate α := by
    rw [hx, hRoot]
    exact (div_mul_cancel₀ _ (hPos α).ne').symm
  refine ⟨?_, ?_, ?_⟩
  · intro χ hχ
    let α : Root := ⟨χ, hχ⟩
    calc
      lower ≤ -|τ α * rate α| := neg_le_neg (Finset.single_le_sum (fun i _ => abs_nonneg (τ i * rate i))
        (Finset.mem_univ α))
      _ ≤ τ α * rate α := neg_abs_le _
      _ ≤ x.1 α * rate α := mul_le_mul_of_nonneg_right (hLower α) (hPos α).le
      _ = h χ := (hroot α).symm
  · intro χ hχ
    let y := x.2
    have hy : y ∈ box := ⟨fun j => (abs_le.mp (hCent j)).1, fun j => (abs_le.mp (hCent j)).2⟩
    have he : e (c y) = (0, y) := by simp [c]
    have hker : (e (h - c y)).2 = 0 := by
      rw [map_sub, he, Prod.snd_sub]
      rw [← hx]
      exact sub_self _
    have hzero := hCenter _ hker
    obtain ⟨ξ, rfl⟩ := hZamb hχ
    have hval := DFunLike.congr_fun hzero ξ
    change h (torusCharacterRestrict i ξ) - c y (torusCharacterRestrict i ξ) = 0 at hval
    rw [sub_eq_zero.mp hval]
    have hsmall : |c y (torusCharacterRestrict i ξ)| ≤ C y :=
      Finset.single_le_sum (fun j _ => abs_nonneg (c y j)) (hZ.mem_toFinset.mpr hχ)
    exact hsmall.trans ((hM ⟨y, hy, rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _)))
  · intro χ hχ
    let α : Root := ⟨χ, hχ.1⟩
    have hb : |x.1 α| ≤ |τ α| + |κ α| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (τ α), hLower α, abs_nonneg (κ α)]
      · linarith [le_abs_self (κ α), hUpper α hχ.2, abs_nonneg (τ α)]
    have hsmall := Finset.single_le_sum (fun k _ => mul_nonneg
      (add_nonneg (abs_nonneg (τ k)) (abs_nonneg (κ k))) (hPos k).le) (Finset.mem_univ α)
    rw [show h χ = h α.val from rfl, hroot, abs_mul, abs_of_pos (hPos α)]
    exact (mul_le_mul_of_nonneg_right hb (hPos α).le).trans
      (hsmall.trans ((le_max_right _ _).trans (le_max_right _ _)))

end Langlands.Global.AdelicSiegelFactors
