import Langlands.GroupScheme.Rational.RankOneParabolicLineCharacter
import Langlands.Global.AdelicCharacterLog
import Langlands.Global.AdelicLineCharacterHeight
import Langlands.Global.RelativeRootChamber

/-! # Normalized adelic bounds from positive integral root-character relations -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix NNReal

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))

namespace AdelicGroupPoints

/-- Actual normalized character norms send positive character multiples to powers. -/
theorem characterNorm_nsmul (ψ : rationalCharacters G) (d : ℕ)
    (x : AdelicGroupPoints F G) :
    characterNorm F G (d • ψ).toMul x = characterNorm F G ψ.toMul x ^ d := by
  induction d with
  | zero => rw [zero_nsmul, characterNorm_zero, pow_zero]
  | succ d hd =>
    rw [succ_nsmul, characterNorm_add, hd, pow_succ]

end AdelicGroupPoints

namespace PositiveRealTorus

/-- A uniform upper bound on the normalized norm of one actual torus character. -/
def HasUniformCharacterBound (ψ : characterLattice T)
    (S : Set (AdelicGroupPoints F T.toGrp)) : Prop :=
  ∃ C : ℝ≥0ˣ, ∀ s ∈ S, normCharacter F T ψ s ≤ C

/-- On the ambient norm kernel, the ambient term in the integral relation
vanishes exactly, leaving equality of positive powers. -/
theorem normCharacter_pow_eq_of_integral_relation
    (i : T.toGrp ⟶ G) {α ψ : characterLattice T} {d b : ℕ}
    (eta : rationalCharacters G)
    (hrel : d • ψ = torusCharacterRestrict i eta + b • α)
    (s : AdelicGroupPoints F T.toGrp)
    (hs : map F T.toGrp G i s ∈ normOneSubgroup F G) :
    normCharacter F T ψ s ^ d = normCharacter F T α s ^ b := by
  have he := congrArg
    (fun χ : characterLattice T => characterNorm F T.toGrp χ.toMul s) hrel
  rw [characterNorm_nsmul, characterNorm_add, characterNorm_nsmul,
    show (torusCharacterRestrict i eta).toMul = i ≫ eta.toMul from rfl,
    characterNorm_comp, (mem_normOneSubgroup F G _).mp hs eta.toMul, one_mul] at he
  exact he

omit [NumberField F] in
private theorem le_max_pow_of_positive_power_relation
    {x y C : ℝ≥0ˣ} {d b : ℕ} (hb : 0 < b)
    (hpow : x ^ d = y ^ b) (hx : x ≤ C) :
    y ≤ max (C ^ d) 1 := by
  by_cases hy : y ≤ 1
  · exact hy.trans (le_max_right _ _)
  · calc
      y ≤ y ^ b := le_self_pow (le_of_not_ge hy) hb.ne'
      _ = x ^ d := hpow.symm
      _ ≤ C ^ d := pow_le_pow_left' hx d
      _ ≤ max (C ^ d) 1 := le_max_left _ _

/-- Under an actual positive integral relation and ambient norm-one condition,
a uniform line-character bound gives a uniform root bound. -/
theorem hasUniformCharacterBound_of_positiveIntegralRootRelation
    (i : T.toGrp ⟶ G) {α ψ : characterLattice T}
    (hrel : HasPositiveIntegralRootCharacterRelation i α ψ)
    (S : Set (AdelicGroupPoints F T.toGrp))
    (hS : ∀ s ∈ S, map F T.toGrp G i s ∈ normOneSubgroup F G)
    (hbound : HasUniformCharacterBound F T ψ S) :
    HasUniformCharacterBound F T α S := by
  obtain ⟨d, b, hd, hb, eta, hrel⟩ := hrel
  obtain ⟨C, hC⟩ := hbound
  refine ⟨max (C ^ d) 1, ?_⟩
  intro s hs
  exact le_max_pow_of_positive_power_relation hb
    (normCharacter_pow_eq_of_integral_relation F G T i eta hrel s (hS s hs)) (hC s hs)

/-- Inverting a uniformly bounded torus family gives the weak lower root bound
used by the left-action chamber convention. -/
theorem exists_lower_normCharacter_inv_of_uniformBound
    (α : characterLattice T) (S : Set (AdelicGroupPoints F T.toGrp))
    (hbound : HasUniformCharacterBound F T α S) :
    ∃ t : ℝ≥0ˣ, ∀ s ∈ S, t ≤ normCharacter F T α s⁻¹ := by
  obtain ⟨C, hC⟩ := hbound
  refine ⟨C⁻¹, ?_⟩
  intro s hs
  rw [map_inv]
  exact inv_le_inv_iff.mpr (hC s hs)

end PositiveRealTorus

namespace RepresentationGrowth

variable {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
  (i : T.toGrp ⟶ G) (hline : (ρ.restrict i).PreservesCoordinateLine j)

/-- A uniform upper bound on the actual selected-vector height on the torus image. -/
def HasUniformTorusLineHeightBound (S : Set (AdelicGroupPoints F T.toGrp)) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ s ∈ S,
    orbitHeight F G ρ (Pi.single j 1) (map F T.toGrp G i s) ≤ C

include hline in
/-- The fixed positive identity height converts the actual vector-height bound
into the normalized actual line-character bound. -/
theorem hasUniformCharacterBound_of_torusLineHeightBound
    (S : Set (AdelicGroupPoints F T.toGrp))
    (hbound : HasUniformTorusLineHeightBound F G T ρ j i S) :
    PositiveRealTorus.HasUniformCharacterBound F T
      (ρ.torusCoordinateLineCharacter i j hline) S := by
  have hv : (Pi.single j (1 : F) : Fin n → F) ≠ 0 := by
    intro h
    have hj := congrFun h j
    simp at hj
  let H := orbitHeight F G ρ (Pi.single j 1) 1
  have hH : 0 < H := orbitHeight_pos F G ρ hv 1
  obtain ⟨C, hC, hbound⟩ := hbound
  let q : ℝ≥0 := ⟨C / H, (div_pos hC hH).le⟩
  have hq : q ≠ 0 := by
    intro h
    have hz := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    exact (ne_of_gt (div_pos hC hH)) hz
  refine ⟨Units.mk0 q hq, ?_⟩
  intro s hs
  have he := orbitHeight_mul_map_eq_lineCharacterNorm F G T.toGrp i ρ j hline 1 s
  simp only [one_mul] at he
  have hb := hbound s hs
  rw [he] at hb
  change ((PositiveRealTorus.normCharacter F T
    (ρ.torusCoordinateLineCharacter i j hline) s : ℝ≥0) : ℝ) ≤ C / H
  exact (le_div_iff₀ hH).mpr hb

include hline in
/-- The actual line-height bound and positive integral relation give a
uniform weak root bound after inversion, with all assumptions explicit. -/
theorem exists_lower_rootNorm_inv_of_torusLineHeightBound
    (α : characterLattice T)
    (hrel : HasPositiveIntegralRootCharacterRelation i α
      (ρ.torusCoordinateLineCharacter i j hline))
    (S : Set (AdelicGroupPoints F T.toGrp))
    (hS : ∀ s ∈ S, map F T.toGrp G i s ∈ normOneSubgroup F G)
    (hbound : HasUniformTorusLineHeightBound F G T ρ j i S) :
    ∃ t : ℝ≥0ˣ, ∀ s ∈ S, t ≤ PositiveRealTorus.normCharacter F T α s⁻¹ := by
  apply PositiveRealTorus.exists_lower_normCharacter_inv_of_uniformBound
  exact PositiveRealTorus.hasUniformCharacterBound_of_positiveIntegralRootRelation
    F G T i hrel S hS
    (hasUniformCharacterBound_of_torusLineHeightBound F G T ρ j i hline S hbound)

end RepresentationGrowth
end Langlands.Global
