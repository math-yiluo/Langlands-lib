import Langlands.Global.AdelicNormalizerConjugation
import Langlands.Global.AdelicLineCharacterHeight
import Langlands.Global.AdelicOrbitHeightCompactBounds
import Langlands.Global.AdelicOrbitHeightMinimum
import Langlands.Global.PrimitiveAdelicMinimum
import Langlands.Global.AdelicSplitMinimalParabolicCompactCover
import Langlands.GroupScheme.Rational.RankOneParabolicLineCharacter

/-! # A height comparison for two Siegel factorizations in Bruhat position -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite Topology
open scoped CategoryTheory.MonObj NNReal Matrix

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- The principal adelic point of a base point of a subgroup is the image of a rational
norm-one point of that subgroup. -/
theorem rational_basePointEquiv_comp {H : GroupScheme (Spec (CommRingCat.of F))} (z : H ⟶ G)
    (c : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ H.X) :
    rational F G (basePointEquiv (c ≫ z.hom.hom)) =
      map F H G z (rationalNormOne F H (basePointEquiv c) : AdelicGroupPoints F H) := by
  rw [basePointEquiv_comp, rationalNormOne_val, map_apply]
  exact DFunLike.congr_fun (rational_naturality F H z) (basePointEquiv c)

/-- The normalized norm of the torus line character is the torus norm of the corresponding
character-lattice element. -/
theorem lineCharacterNorm_eq_normCharacter (i : T.toGrp ⟶ G) {m : ℕ}
    (ρ : MatrixRepresentation G (Fin m)) (j : Fin m)
    (hT : (ρ.restrict i).PreservesCoordinateLine j) (t : AdelicGroupPoints F T.toGrp) :
    lineCharacterNorm F G T.toGrp i ρ j hT t =
      PositiveRealTorus.normCharacter F T (ρ.torusCoordinateLineCharacter i j hT) t :=
  rfl

section Factor

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The ambient torus factors through the minimal standard parabolic. -/
def torusEmptyParabolicFactor : T.toGrp ⟶ Standard.parabolicScheme i ν ∅ :=
  (Standard.isRepresentedBy_parabolicHom i ν ∅).factorHom i
    ((range_le_standardLevi i ν ∅).trans (standardLevi_le_standardParabolic i ν ∅))

omit [NumberField F] in
theorem torusEmptyParabolicFactor_comp :
    torusEmptyParabolicFactor i ν ≫ Standard.parabolicHom i ν ∅ = i :=
  (Standard.isRepresentedBy_parabolicHom i ν ∅).factorHom_comp _ _

theorem map_torusEmptyParabolicFactor (t : AdelicGroupPoints F T.toGrp) :
    map F _ G (Standard.parabolicHom i ν ∅)
        (map F T.toGrp _ (torusEmptyParabolicFactor i ν) t) =
      map F T.toGrp G i t := by
  simp only [map_apply, affinePointsTarget_apply, Category.assoc]
  rw [← Grp.comp_hom_hom, torusEmptyParabolicFactor_comp]

end Factor

variable [IsAffineHom G.X.hom]

set_option maxHeartbeats 1600000 in
/-- **Height comparison in Bruhat position** (the first half of Springer's proof of
Proposition 2.6). Let `ρ` be a representation with a coordinate line preserved by the
minimal standard parabolic, with torus character `ψ`. For a compact set `C` there is a
constant `D` such that whenever `x i(s) p = x' i(s') p' γ` with `x, x' ∈ C`, norm-one
minimal-parabolic factors `p, p'` and a rational point `γ = b₁ n b₂` with `b₁, b₂` in the
minimal standard parabolic and `n` normalizing the torus, the Weyl translate `n · ψ` at `s'`
is at most `D` times `ψ` at `s`. -/
theorem exists_bruhat_height_bound (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    [Mono i.hom.hom.left] (ν : cocharacterLattice T) (hi : IsMaximalSplitTorus i)
    (hmax : IsMaximalTorus i) (hν : IsGenericCocharacter i ν)
    {m : ℕ} (ρ : MatrixRepresentation G (Fin m)) (j : Fin m)
    (hP : (ρ.restrict (Standard.parabolicHom i ν ∅)).PreservesCoordinateLine j)
    (hT : (ρ.restrict i).PreservesCoordinateLine j)
    {C : Set (AdelicGroupPoints F G)} (hC : IsCompact C) :
    ∃ D : ℝ, 0 < D ∧ ∀ x ∈ C, ∀ x' ∈ C, ∀ (s s' : AdelicGroupPoints F T.toGrp)
      (p p' : normOneSubgroup F (Standard.parabolicScheme i ν ∅))
      (n : normalizerPoints i) (b₁ b₂ : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X),
      b₁ ∈ standardParabolicPoints i ν ∅ → b₂ ∈ standardParabolicPoints i ν ∅ →
      x * map F T.toGrp G i s * map F _ G (Standard.parabolicHom i ν ∅) p =
        x' * map F T.toGrp G i s' * map F _ G (Standard.parabolicHom i ν ∅) p' *
          rational F G (basePointEquiv (b₁ * (n : Over.mk _ ⟶ G.X) * b₂)) →
      ((PositiveRealTorus.normCharacter F T
          (weylAction i n (ρ.torusCoordinateLineCharacter i j hT)) s' : ℝ≥0) : ℝ) ≤
        D * ((PositiveRealTorus.normCharacter F T
          (ρ.torusCoordinateLineCharacter i j hT) s : ℝ≥0) : ℝ) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  set P := Standard.parabolicScheme i ν ∅
  set incl := Standard.parabolicHom i ν ∅
  set e : Fin m → F := Pi.single j 1 with he_def
  have he : e ≠ 0 := by
    intro h
    have hj := congrFun h j
    simp [e] at hj
  set ψ := ρ.torusCoordinateLineCharacter i j hT
  obtain ⟨B₁, hB₁, hb₁⟩ := exists_pos_orbitHeight_bounds_of_isCompact F G ρ hm hC
  obtain ⟨Ω, hΩ, hcover⟩ :=
    hasCompactNormOneRationalCover_emptyParabolic_of_maximalTorus i ν hG hi hν hmax
  set K : Set (AdelicGroupPoints F G) :=
    (fun z : AdelicGroupPoints F G × normOneSubgroup F P =>
      z.1 * (map F P G incl (z.2 : AdelicGroupPoints F P))⁻¹) '' (C ×ˢ Ω) with hK_def
  have hK : IsCompact K := by
    apply (hC.prod hΩ).image
    exact continuous_fst.mul
      (((map F P G incl).continuous.comp (continuous_subtype_val.comp continuous_snd)).inv)
  obtain ⟨B₂, hB₂, hb₂⟩ := exists_pos_orbitHeight_bounds_of_isCompact F G ρ hm hK
  obtain ⟨h₀, hh₀, hmin⟩ :=
    PrimitiveAdelicHeight.exists_pos_le_rationalHeight F m (adelicMatrix F G ρ 1)
  set H₁ := orbitHeight F G ρ e 1
  have hH₁ : 0 < H₁ := orbitHeight_pos F G ρ he 1
  refine ⟨B₁ * B₂ * H₁ / h₀, by positivity, ?_⟩
  intro x hx x' hx' s s' p p' n b₁ b₂ hb₁m hb₂m heq
  have hrep := Standard.isRepresentedBy_parabolicHom i ν ∅
  obtain ⟨c₁, hc₁⟩ : ∃ c, c ≫ incl.hom.hom = b₁ := by
    have h : b₁ ∈ (SubgroupFunctor.range incl).carrier _ := by
      rw [hrep.2]
      exact hb₁m
    exact h
  obtain ⟨c₂, hc₂⟩ : ∃ c, c ≫ incl.hom.hom = b₂ := by
    have h : b₂ ∈ (SubgroupFunctor.range incl).carrier _ := by
      rw [hrep.2]
      exact hb₂m
    exact h
  -- Move the torus factor past the normalizing point.
  obtain ⟨t', ht'eq, ht'norm⟩ := exists_map_mul_rational_normalizer i n s'
  -- Conjugate the parabolic factor by the torus and choose compact representatives.
  set sP : AdelicGroupPoints F P := map F T.toGrp P (torusEmptyParabolicFactor i ν) s'
  set p₁ : normOneSubgroup F P := p' * rationalNormOne F P (basePointEquiv c₁)
  have hy : sP * (p₁ : AdelicGroupPoints F P) * sP⁻¹ ∈ normOneSubgroup F P :=
    (normOneSubgroup_normal F P).conj_mem _ p₁.property sP
  set y : normOneSubgroup F P := ⟨_, hy⟩
  obtain ⟨r, hr⟩ := hcover y⁻¹
  set ω : normOneSubgroup F P := rationalNormOne F P r * y⁻¹ with hω
  have hsp : sP * (p₁ : AdelicGroupPoints F P) =
      (ω : AdelicGroupPoints F P)⁻¹ * rational F P r * sP := by
    simp only [hω, Subgroup.coe_mul, Subgroup.coe_inv, rationalNormOne_val, y]
    group
  -- The right-hand side in its new form.
  set g : RationalGroupPoints F G :=
    P.affinePointsTarget incl (CommAlgCat.of F F) r * basePointEquiv (n : Over.mk _ ⟶ G.X)
  set k : AdelicGroupPoints F G := x' * (map F P G incl (ω : AdelicGroupPoints F P))⁻¹
  have hk : k ∈ K := ⟨(x', ω), ⟨hx', hr⟩, rfl⟩
  have hRHS : x' * map F T.toGrp G i s' * map F P G incl p' *
        rational F G (basePointEquiv (b₁ * (n : Over.mk _ ⟶ G.X) * b₂)) =
      k * rational F G g * map F T.toGrp G i t' *
        map F P G incl (rationalNormOne F P (basePointEquiv c₂) : AdelicGroupPoints F P) := by
    have h1 : rational F G (basePointEquiv (b₁ * (n : Over.mk _ ⟶ G.X) * b₂)) =
        map F P G incl (rationalNormOne F P (basePointEquiv c₁) : AdelicGroupPoints F P) *
          rational F G (basePointEquiv (n : Over.mk _ ⟶ G.X)) *
          map F P G incl (rationalNormOne F P (basePointEquiv c₂) : AdelicGroupPoints F P) := by
      rw [map_mul, map_mul, map_mul, map_mul, ← hc₁, ← hc₂, rational_basePointEquiv_comp,
        rational_basePointEquiv_comp]
    have h2 : map F T.toGrp G i s' = map F P G incl sP :=
      (map_torusEmptyParabolicFactor i ν s').symm
    have h3 : map F P G incl sP * map F P G incl p' *
        map F P G incl (rationalNormOne F P (basePointEquiv c₁) : AdelicGroupPoints F P) =
        (map F P G incl (ω : AdelicGroupPoints F P))⁻¹ * rational F G
          (P.affinePointsTarget incl (CommAlgCat.of F F) r) * map F T.toGrp G i s' := by
      rw [h2, ← map_mul, ← map_mul, ← map_inv]
      have h4 : rational F G (P.affinePointsTarget incl (CommAlgCat.of F F) r) =
          map F P G incl (rational F P r) :=
        DFunLike.congr_fun (rational_naturality F P incl) r
      rw [h4, ← map_mul, ← map_mul]
      congr 1
      rw [mul_assoc, ← Subgroup.coe_mul]
      exact hsp
    have h5 : rational F G g = rational F G (P.affinePointsTarget incl (CommAlgCat.of F F) r) *
        rational F G (basePointEquiv (n : Over.mk _ ⟶ G.X)) := map_mul _ _ _
    calc x' * map F T.toGrp G i s' * map F P G incl p' *
          rational F G (basePointEquiv (b₁ * (n : Over.mk _ ⟶ G.X) * b₂))
        = x' * (map F P G incl sP * map F P G incl p' *
            map F P G incl (rationalNormOne F P (basePointEquiv c₁) : AdelicGroupPoints F P)) *
            rational F G (basePointEquiv (n : Over.mk _ ⟶ G.X)) *
            map F P G incl (rationalNormOne F P (basePointEquiv c₂) :
              AdelicGroupPoints F P) := by
          rw [h1, h2]
          group
      _ = x' * (map F P G incl (ω : AdelicGroupPoints F P))⁻¹ *
            rational F G (P.affinePointsTarget incl (CommAlgCat.of F F) r) *
            (map F T.toGrp G i s' * rational F G (basePointEquiv (n : Over.mk _ ⟶ G.X))) *
            map F P G incl (rationalNormOne F P (basePointEquiv c₂) :
              AdelicGroupPoints F P) := by
          rw [h3]
          group
      _ = k * rational F G g * map F T.toGrp G i t' *
            map F P G incl (rationalNormOne F P (basePointEquiv c₂) :
              AdelicGroupPoints F P) := by
          rw [ht'eq, h5]
          simp only [k]
          group
  -- Heights of both sides.
  have hL : orbitHeight F G ρ e (x * map F T.toGrp G i s * map F P G incl p) =
      ((PositiveRealTorus.normCharacter F T ψ s : ℝ≥0) : ℝ) * orbitHeight F G ρ e x := by
    rw [orbitHeight_mul_map_normOne F G P incl ρ j hP,
      orbitHeight_mul_map_eq_lineCharacterNorm F G T.toGrp i ρ j hT,
      lineCharacterNorm_eq_normCharacter]
  set v : Fin m → F := (rationalMatrix F G ρ g).val *ᵥ e
  have hv : v ≠ 0 := by
    intro hv0
    apply he
    have h := congrArg (fun w => (rationalMatrix F G ρ g)⁻¹.val *ᵥ w) hv0
    simpa only [v, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec,
      Matrix.mulVec_zero] using h
  have hR : orbitHeight F G ρ e (k * rational F G g * map F T.toGrp G i t' *
        map F P G incl (rationalNormOne F P (basePointEquiv c₂) : AdelicGroupPoints F P)) =
      ((PositiveRealTorus.normCharacter F T (weylAction i n ψ) s' : ℝ≥0) : ℝ) *
        orbitHeight F G ρ v k := by
    rw [orbitHeight_mul_map_normOne F G P incl ρ j hP,
      orbitHeight_mul_map_eq_lineCharacterNorm F G T.toGrp i ρ j hT,
      lineCharacterNorm_eq_normCharacter, orbitHeight_mul_rational, ht'norm ψ]
  have hxB : orbitHeight F G ρ e x ≤ B₁ * H₁ := by
    simpa only [mul_one] using (hb₁ x hx 1 e he).1
  have hkB : h₀ ≤ B₂ * orbitHeight F G ρ v k := by
    have h1 := (hb₂ k hk 1 v hv).2
    rw [mul_one] at h1
    exact (hmin v hv).trans h1
  have hEq : ((PositiveRealTorus.normCharacter F T (weylAction i n ψ) s' : ℝ≥0) : ℝ) *
        orbitHeight F G ρ v k =
      ((PositiveRealTorus.normCharacter F T ψ s : ℝ≥0) : ℝ) * orbitHeight F G ρ e x := by
    rw [← hL, ← hR, ← hRHS, heq]
  have hψs : 0 ≤ ((PositiveRealTorus.normCharacter F T ψ s : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hwψ : 0 ≤ ((PositiveRealTorus.normCharacter F T (weylAction i n ψ) s' : ℝ≥0) : ℝ) :=
    NNReal.coe_nonneg _
  rw [div_mul_eq_mul_div, le_div_iff₀ hh₀]
  calc ((PositiveRealTorus.normCharacter F T (weylAction i n ψ) s' : ℝ≥0) : ℝ) * h₀
      ≤ ((PositiveRealTorus.normCharacter F T (weylAction i n ψ) s' : ℝ≥0) : ℝ) *
          (B₂ * orbitHeight F G ρ v k) := mul_le_mul_of_nonneg_left hkB hwψ
    _ = B₂ * (((PositiveRealTorus.normCharacter F T ψ s : ℝ≥0) : ℝ) *
          orbitHeight F G ρ e x) := by rw [← hEq]; ring
    _ ≤ B₂ * (((PositiveRealTorus.normCharacter F T ψ s : ℝ≥0) : ℝ) * (B₁ * H₁)) := by
          gcongr
    _ = B₁ * B₂ * H₁ * ((PositiveRealTorus.normCharacter F T ψ s : ℝ≥0) : ℝ) := by ring

end Langlands.Global.AdelicSiegelFactors
