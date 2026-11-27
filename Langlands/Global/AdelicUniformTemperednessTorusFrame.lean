import Langlands.Global.AdelicLocalFinitenessTorusCoordinates
import Langlands.Global.AdelicLocalFinitenessGroupData
import Langlands.Global.AdelicPositiveTorusSplitComponentProof
import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Simple-root and central coordinates on the positive maximal split torus

For a standard parabolic family `𝓕` of a connected reductive group over a number field, the
normalized logarithm identifies the positive real points `A_T` of the maximal split torus with
the real character dual `𝔞_T`, and the simple roots together with finitely many central
directions give linear coordinates on `𝔞_T`. This module packages these coordinates and the
splitting of a positive point along a set `J` of simple roots used in the proof of the uniform
temperedness criterion. -/

noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν
local notation "V" => RealCharacterDual F 𝓕.T.toGrp

/-- Linear coordinates on the real character dual of the maximal split torus: one coordinate
`ℓ(α) / step α` for every simple root `α`, and finitely many coordinates whose joint vanishing
is the vanishing of the restriction to the characters of `G`. -/
structure TorusFrame where
  /-- The number of central coordinates. -/
  r : ℕ
  /-- The coordinate map. -/
  e : V ≃L[ℝ] ((Δ → ℝ) × (Fin r → ℝ))
  /-- The positive scale of each root coordinate. -/
  step : Δ → ℝ
  step_pos : ∀ α, 0 < step α
  root : ∀ ℓ α, (e ℓ).1 α = ℓ α.val / step α
  central : ∀ ℓ, (e ℓ).2 = 0 ↔ realCharacterDualMap F 𝓕.T.toGrp G 𝓕.i ℓ = 0

/-- Coordinates exist, from the group data of `Ξ_main` and their torus coordinates. -/
theorem TorusFrame.nonempty : Nonempty (TorusFrame 𝓕) := by
  obtain ⟨Ua, _, u, _, t, r, z, hData⟩ :=
    exists_isLocalFinitenessGroupData 𝓕.connectedReductive 𝓕.maximalSplit 𝓕.generic
  obtain ⟨e, hroot, hcent, hstep, -⟩ := localFinitenessTorusCoordinates 𝓕.i 𝓕.ν
    𝓕.connectedReductive 𝓕.maximalSplit 𝓕.generic u t z hData
  exact ⟨⟨r, e, localFinitenessRootStep 𝓕.i 𝓕.ν t, fun α => (hstep α).1, hroot, hcent⟩⟩

omit [NumberField F] in
theorem isSplitTorus_T : IsSplitTorus 𝓕.T.toGrp := 𝓕.maximalSplit.isSplitSubtorus.1

/-- Positive points are determined by their logarithms. -/
theorem eq_of_characterLog_eq' {x y : AdelicGroupPoints F 𝓕.T.toGrp}
    (hx : x ∈ intrinsicSubgroup F 𝓕.T) (hy : y ∈ intrinsicSubgroup F 𝓕.T)
    (h : characterLog F 𝓕.T.toGrp x = characterLog F 𝓕.T.toGrp y) : x = y :=
  PositiveRealTorus.eq_of_characterLog_eq 𝓕.isSplitTorus_T hx hy h

/-- Every functional is the logarithm of a positive point. -/
theorem exists_characterLog_eq' (ℓ : V) :
    ∃ x ∈ intrinsicSubgroup F 𝓕.T, characterLog F 𝓕.T.toGrp x = ℓ :=
  PositiveRealTorus.exists_characterLog_eq 𝓕.isSplitTorus_T ℓ

/-- On a positive point, a character with logarithm zero takes the value one. -/
theorem characterValue_eq_one_of_characterLog_eq_zero {x : AdelicGroupPoints F 𝓕.T.toGrp}
    (hx : x ∈ intrinsicSubgroup F 𝓕.T) {χ : characterLattice 𝓕.T}
    (h : characterLog F 𝓕.T.toGrp x χ = 0) : Lie.characterValue χ x = 1 := by
  obtain ⟨y, hy⟩ := (mem_intrinsicSubgroup_iff F 𝓕.T x).mp hx χ
  rw [characterLog_eq_log_characterValue, ← hy, PositiveRealIdeles.absoluteValue_full,
    Units.val_pow_eq_pow_val, NNReal.coe_pow, Real.log_pow] at h
  have hd : (Module.finrank ℚ F : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have hlog : Real.log ((y : ℝ≥0) : ℝ) = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hd
    · exact h
  have hpos : (0 : ℝ) < ((y : ℝ≥0) : ℝ) := by
    exact_mod_cast pos_iff_ne_zero.mpr y.ne_zero
  have hy1 : ((y : ℝ≥0) : ℝ) = 1 := Real.eq_one_of_pos_of_log_eq_zero hpos hlog
  have hy1' : y = 1 := by
    have h' : (y : ℝ≥0) = 1 := by exact_mod_cast hy1
    exact Units.ext h'
  rw [← hy, hy1', map_one]

/-- The adelic point map of the maximal split torus is injective. -/
theorem map_i_injective : Function.Injective (map F 𝓕.T.toGrp G 𝓕.i) := by
  intro x y h
  simp only [map_apply, GroupScheme.affinePointsTarget_apply] at h
  have : Mono 𝓕.i.hom.hom := Over.mono_of_mono_left _
  exact (cancel_mono 𝓕.i.hom.hom).mp h

/-- The image of a positive point of `A_J` in `G(𝔸)` is the image of its image in `T`. -/
theorem map_p_positivePointMap (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (s : intrinsicSubgroup F (𝓕.A J)) :
    map F (𝓕.P J) G (𝓕.p J) (positivePointMap F (𝓕.P J) (𝓕.A J) (𝓕.a J ≫ 𝓕.l J) s) =
      map F 𝓕.T.toGrp G 𝓕.i
        (map F (𝓕.A J).toGrp 𝓕.T.toGrp (CommGroupScheme.groupHom (𝓕.f J)) s.val) := by
  have h := (𝓕.isCompatible J).factor_comp
  have h' := congrArg (fun z : (𝓕.A J).toGrp ⟶ G => z.hom.hom) h
  simp only [Grp.comp_hom_hom] at h'
  simp only [positivePointMap_apply, map_apply, GroupScheme.affinePointsTarget_apply,
    Grp.comp_hom_hom, Category.assoc]
  rw [← h']

/-- **Lifting to the split component.** A positive point of `T` on which the simple roots in
`J` are trivial is the image of a positive point of `A_J`. -/
theorem exists_splitPoint (J : StandardIndex F G 𝓕.i 𝓕.ν) {x : AdelicGroupPoints F 𝓕.T.toGrp}
    (hx : x ∈ intrinsicSubgroup F 𝓕.T) (hJ : ∀ β ∈ J.1, Lie.characterValue β x = 1) :
    ∃ s : intrinsicSubgroup F (𝓕.A J),
      map F (𝓕.A J).toGrp 𝓕.T.toGrp (CommGroupScheme.groupHom (𝓕.f J)) s.val = x := by
  obtain ⟨a, ⟨s, hs, rfl⟩, ha⟩ := positiveTorusSplitComponent F G 𝓕 J x hx hJ
  refine ⟨⟨s, hs⟩, 𝓕.map_i_injective ?_⟩
  rw [← ha, ← 𝓕.map_p_positivePointMap J ⟨s, hs⟩]
  rfl

/-- The value of a restricted character at a point of `A_J` is its value at the image in `T`. -/
theorem normCharacter_splitPoint (J : StandardIndex F G 𝓕.i 𝓕.ν)
    (s : intrinsicSubgroup F (𝓕.A J)) (χ : characterLattice 𝓕.T) :
    normCharacter F (𝓕.A J) (𝓕.f J ≫ χ) s =
      normCharacter F 𝓕.T χ
        (map F (𝓕.A J).toGrp 𝓕.T.toGrp (CommGroupScheme.groupHom (𝓕.f J)) s.val) := by
  rw [normCharacter_pullback]
  rfl

variable {𝓕}

/-- The coordinates of a point of `T(𝔸)`. -/
def TorusFrame.crd (Fr : TorusFrame 𝓕) (x : AdelicGroupPoints F 𝓕.T.toGrp) :
    (Δ → ℝ) × (Fin Fr.r → ℝ) :=
  Fr.e (characterLog F 𝓕.T.toGrp x)

theorem TorusFrame.crd_mul (Fr : TorusFrame 𝓕) (x y : AdelicGroupPoints F 𝓕.T.toGrp) :
    Fr.crd (x * y) = Fr.crd x + Fr.crd y := by
  simp only [TorusFrame.crd, characterLog_mul, map_add]

theorem TorusFrame.characterLog_root (Fr : TorusFrame 𝓕) (x : AdelicGroupPoints F 𝓕.T.toGrp)
    (α : Δ) : characterLog F 𝓕.T.toGrp x α.val = Fr.step α * (Fr.crd x).1 α := by
  rw [TorusFrame.crd, Fr.root, mul_div_cancel₀ _ (Fr.step_pos α).ne']

/-- Every pair of coordinates is attained by a positive point. -/
theorem TorusFrame.exists_crd_eq (Fr : TorusFrame 𝓕) (v : (Δ → ℝ) × (Fin Fr.r → ℝ)) :
    ∃ x ∈ intrinsicSubgroup F 𝓕.T, Fr.crd x = v := by
  obtain ⟨x, hx, hlog⟩ := 𝓕.exists_characterLog_eq' (Fr.e.symm v)
  exact ⟨x, hx, by rw [TorusFrame.crd, hlog, ContinuousLinearEquiv.apply_symm_apply]⟩

/-- Positive points with the same coordinates are equal. -/
theorem TorusFrame.eq_of_crd_eq (Fr : TorusFrame 𝓕) {x y : AdelicGroupPoints F 𝓕.T.toGrp}
    (hx : x ∈ intrinsicSubgroup F 𝓕.T) (hy : y ∈ intrinsicSubgroup F 𝓕.T)
    (h : Fr.crd x = Fr.crd y) : x = y :=
  𝓕.eq_of_characterLog_eq' hx hy (Fr.e.injective h)

open Classical in
/-- **Splitting along `J`.** A positive point `x` is a product `x₁ x₀ x_c` of positive points
whose root coordinates are, at `α ∈ J`, `0`, `0` and the coordinate of `x`, and at `α ∉ J`,
the positive part, the negative part and `0`; the central coordinates of `x₀` and `x_c` vanish. -/
theorem TorusFrame.exists_split (Fr : TorusFrame 𝓕) (J : Set (characterLattice 𝓕.T))
    {x : AdelicGroupPoints F 𝓕.T.toGrp} (hx : x ∈ intrinsicSubgroup F 𝓕.T) :
    ∃ x₁ ∈ intrinsicSubgroup F 𝓕.T, ∃ x₀ ∈ intrinsicSubgroup F 𝓕.T,
      ∃ xc ∈ intrinsicSubgroup F 𝓕.T, x = x₁ * x₀ * xc ∧
      Fr.crd x₁ = (fun α => if α.val ∈ J then 0 else max ((Fr.crd x).1 α) 0, (Fr.crd x).2) ∧
      Fr.crd x₀ = (fun α => if α.val ∈ J then 0 else min ((Fr.crd x).1 α) 0, 0) ∧
      Fr.crd xc = (fun α => if α.val ∈ J then (Fr.crd x).1 α else 0, 0) := by
  obtain ⟨x₁, hx₁, h₁⟩ := Fr.exists_crd_eq
    (fun α => if α.val ∈ J then 0 else max ((Fr.crd x).1 α) 0, (Fr.crd x).2)
  obtain ⟨x₀, hx₀, h₀⟩ := Fr.exists_crd_eq
    (fun α => if α.val ∈ J then 0 else min ((Fr.crd x).1 α) 0, 0)
  obtain ⟨xc, hxc, hc⟩ := Fr.exists_crd_eq (fun α => if α.val ∈ J then (Fr.crd x).1 α else 0, 0)
  refine ⟨x₁, hx₁, x₀, hx₀, xc, hxc, ?_, h₁, h₀, hc⟩
  apply Fr.eq_of_crd_eq hx
  · exact mul_mem (mul_mem hx₁ hx₀) hxc
  rw [Fr.crd_mul, Fr.crd_mul, h₁, h₀, hc]
  refine Prod.ext (funext fun α => ?_) (by simp)
  simp only [Prod.fst_add, Pi.add_apply]
  split_ifs <;> simp [max_add_min]

theorem TorusFrame.crd_pow (Fr : TorusFrame 𝓕) (y : AdelicGroupPoints F 𝓕.T.toGrp) (n : ℕ) :
    Fr.crd (y ^ n) = (n : ℝ) • Fr.crd y := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_smul, TorusFrame.crd, characterLog_one, map_zero]
  | succ n ih => rw [pow_succ, Fr.crd_mul, ih, Nat.cast_succ, add_smul, one_smul]

/-- **Roots.** For every positive point `x` and integer `N ≥ 1` there is a positive point `y`
with `y ^ N = x` and coordinates `N⁻¹` times those of `x`. -/
theorem TorusFrame.exists_pow_eq (Fr : TorusFrame 𝓕) {x : AdelicGroupPoints F 𝓕.T.toGrp}
    (hx : x ∈ intrinsicSubgroup F 𝓕.T) {N : ℕ} (hN : 0 < N) :
    ∃ y ∈ intrinsicSubgroup F 𝓕.T, y ^ N = x ∧ Fr.crd y = (N : ℝ)⁻¹ • Fr.crd x := by
  obtain ⟨y, hy, hcy⟩ := Fr.exists_crd_eq ((N : ℝ)⁻¹ • Fr.crd x)
  refine ⟨y, hy, ?_, hcy⟩
  apply Fr.eq_of_crd_eq (pow_mem hy N) hx
  rw [Fr.crd_pow, hcy, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hN.ne'), one_smul]

/-- On a positive point whose root coordinate at `β` vanishes, `β` takes the value one. -/
theorem TorusFrame.characterValue_eq_one (Fr : TorusFrame 𝓕) {x : AdelicGroupPoints F 𝓕.T.toGrp}
    (hx : x ∈ intrinsicSubgroup F 𝓕.T) {β : Δ} (h : (Fr.crd x).1 β = 0) :
    Lie.characterValue β.val x = 1 :=
  𝓕.characterValue_eq_one_of_characterLog_eq_zero hx (by rw [Fr.characterLog_root, h, mul_zero])

end Langlands.Global.StandardParabolicFamily
