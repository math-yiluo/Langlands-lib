import Langlands.Global.AdelicSiegelSplitRays

/-! # Complementary simple-root coordinates in a Siegel chamber -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ fam.T)

local notation "Torus" => intrinsicSubgroup F T₀
local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "aG" => positiveMap F G fam.T fam.i T₀ j
local notation "rootLog" => (fun (a : Torus) (β : characterLattice fam.T) =>
  characterLog F T₀.toGrp a.val (j ≫ β))

/-- A split-component translation preserves the Levi simple-root logarithms and puts the
complementary simple-root logarithms in a fixed bounded nonnegative interval. -/
theorem exists_siegelLeviChamberShift
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j)
    (J : StandardIndex F G fam.i fam.ν) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : Torus, ∃ (s : Torus) (b : fam.positiveSplitComponent J),
      map F (fam.P J) G (fam.p J) b.val = aG s ∧
      (∀ β ∈ J.val, rootLog (s * a) β = rootLog a β) ∧
      ∀ β ∈ Δ, β ∉ J.val → 0 ≤ rootLog (s * a) β ∧ rootLog (s * a) β ≤ B := by
  classical
  obtain ⟨r, hOff, hPos, _, hSplit⟩ := fam.exists_siegelFundamentalRays j hsetup
  let D := {α : Δ // α.val ∉ J.val}
  let : Fintype Δ := (fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν).fintype
  let : Fintype D := inferInstanceAs (Fintype {α : Δ // α.val ∉ J.val})
  let step (α : D) : ℝ := rootLog (r α.val) α.val.val
  let B : ℝ := ∑ α : D, step α
  refine ⟨B, Finset.sum_nonneg (fun α _ => (hPos α.val).le), ?_⟩
  intro a
  let exponent (α : D) : ℤ := -⌊rootLog a α.val.val / step α⌋
  let s : Torus := ∏ α : D, r α.val ^ exponent α
  let Pₐ := (fam.positiveSplitComponent J).map (map F (fam.P J) G (fam.p J)).toMonoidHom
  have hs : s ∈ Pₐ.comap (aG : Torus →ₜ* AdelicGroupPoints F G).toMonoidHom := by
    apply Subgroup.prod_mem
    intro α _
    apply Subgroup.zpow_mem
    obtain ⟨b, hb⟩ := hSplit J α.val α.property
    exact ⟨b.val, b.property, hb⟩
  change aG s ∈ Pₐ at hs
  obtain ⟨b, hb, hImage⟩ := hs
  have hLog (β : characterLattice fam.T) :
      rootLog (s * a) β = (∑ α : D, (exponent α : ℝ) * rootLog (r α.val) β) + rootLog a β := by
    let L : Torus →* Multiplicative ℝ :=
      { toFun := fun x => Multiplicative.ofAdd (rootLog x β)
        map_one' := by
          change characterLog F T₀.toGrp 1 (j ≫ β) = 0
          rw [characterLog_one]
          rfl
        map_mul' := fun x y => by
          change characterLog F T₀.toGrp (x.val * y.val) (j ≫ β) = rootLog x β + rootLog y β
          rw [characterLog_mul]
          rfl }
    change (L (s * a)).toAdd = _
    rw [map_mul, toAdd_mul]
    congr 1
    dsimp only [s]
    rw [map_prod, toAdd_prod]
    apply Finset.sum_congr rfl
    intro α _
    rw [map_zpow, toAdd_zpow, zsmul_eq_mul]
    rfl
  refine ⟨s, ⟨b, hb⟩, hImage, ?_, ?_⟩
  · intro β hβ
    rw [hLog, Finset.sum_eq_zero, zero_add]
    intro α _
    have hne : (⟨β, J.property hβ⟩ : Δ) ≠ α.val :=
      fun h => α.property (congrArg Subtype.val h ▸ hβ)
    have hz : rootLog (r α.val) β = 0 := hOff α.val ⟨β, J.property hβ⟩ hne
    rw [hz, mul_zero]
  · intro β hβ hExcluded
    let δ : D := ⟨⟨β, hβ⟩, hExcluded⟩
    have hStep : 0 < step δ := hPos δ.val
    have hB : step δ ≤ B := Finset.single_le_sum (fun α _ => (hPos α.val).le) (Finset.mem_univ δ)
    have hFloor : (↑⌊rootLog a β / step δ⌋ : ℝ) * step δ ≤ rootLog a β :=
      (le_div_iff₀ hStep).mp (Int.floor_le _)
    have hCeil : rootLog a β < ((↑⌊rootLog a β / step δ⌋ : ℝ) + 1) * step δ :=
      (div_lt_iff₀ hStep).mp (Int.lt_floor_add_one _)
    rw [hLog, Finset.sum_eq_single δ]
    · change 0 ≤ ((-⌊rootLog a β / step δ⌋ : ℤ) : ℝ) * step δ + rootLog a β ∧
        ((-⌊rootLog a β / step δ⌋ : ℤ) : ℝ) * step δ + rootLog a β ≤ B
      push_cast
      constructor <;> nlinarith
    · intro α _ hne
      have hne' : δ.val ≠ α.val := fun h => hne (Subtype.ext h.symm)
      have hz : rootLog (r α.val) β = 0 := hOff α.val δ.val hne'
      rw [hz, mul_zero]
    · simp

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

/-- In a fixed Siegel torus, the complementary root logarithms can be bounded uniformly
by a positive split-component translation that preserves the Levi root logarithms. -/
def AdelicSiegelLeviChamberShiftStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
    (j : T₀ ⟶ fam.T), IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j →
    ∀ (J : StandardIndex F G fam.i fam.ν),
    let L := fun (a : intrinsicSubgroup F T₀) (β : characterLattice fam.T) =>
      characterLog F T₀.toGrp a.val (j ≫ β)
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : intrinsicSubgroup F T₀,
      ∃ (s : intrinsicSubgroup F T₀) (b : fam.positiveSplitComponent J),
        map F (fam.P J) G (fam.p J) b.val = positiveMap F G fam.T fam.i T₀ j s ∧
        (∀ β ∈ J.val, L (s * a) β = L a β) ∧
        ∀ β ∈ simpleRelativeRoots fam.i fam.ν, β ∉ J.val → 0 ≤ L (s * a) β ∧ L (s * a) β ≤ B

theorem adelicSiegelLeviChamberShift : AdelicSiegelLeviChamberShiftStatement := by
  intro F _ _ G _ _ _ fam T₀ j hsetup J
  exact fam.exists_siegelLeviChamberShift j hsetup J

end Langlands.Global
