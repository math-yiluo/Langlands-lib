import Langlands.Representation.Exponents.RadicalWeightTransfer

/-! # Restriction preserves nonzero vectors in the nonnegative cone of `P'`

For intersection data `D` of a double coset `P z Q`, restriction along `τ : A_L → A'`
sends the intrinsic positive roots of the parabolic `P'` of `M` to intrinsic positive
roots of `Q`. These pair strictly positively with the defining split-component cocharacter
of a presentation of `Q`. Hence a nonzero vector of the nonnegative cone of `P'` has a
nonzero restriction to `A_L`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RelativeRoot RealTorusSpace

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
  [IsAffineHom G.X.hom] [IsAffineHom M.X.hom] [Smooth G.X.hom] [Smooth M.X.hom]
  [LocallyOfFiniteType M.X.hom]
  {A A' : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ L} {a' : A'.toGrp ⟶ D.L'}

/-- Pairing the restriction of a vector of the cone of `P'` with the defining
cocharacter of a presentation of `Q` is nonnegative, and it vanishes only at zero. -/
theorem pair_restrictReal_nonneg_and_eq_zero (τ : A ⟶ A')
    (hτ : CommGroupScheme.groupHom τ ≫ a' ≫ D.lQ' ≫ D.q' = a)
    (presQ : ParabolicRootPresentation q lQ a)
    (presM : ParabolicRootPresentation D.p' D.l' (a' ≫ D.φ.hom))
    {x : Vstar A'} (hx : x ∈ presM.nonnegCone) :
    0 ≤ pair A (rationalCharacterRestrictReal (CommGroupScheme.groupHom τ) x)
        ((1 : ℝ) ⊗ₜ[ℤ] presQ.splitComponentCocharacter) ∧
      (pair A (rationalCharacterRestrictReal (CommGroupScheme.groupHom τ) x)
        ((1 : ℝ) ⊗ₜ[ℤ] presQ.splitComponentCocharacter) = 0 → x = 0) := by
  change x ∈ restrictedRootNonnegCone _ _ _ _ _ at hx
  rw [restrictedRootNonnegCone_eq_hull, SetLike.mem_coe] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨β, hβ, rfl⟩ := presM.restrictedRoots_subset_image_intrinsicPositiveRoots hy
    have hβ' := D.comp_mem_intrinsicPositiveRoots τ hτ presQ presM hβ
    rw [rationalCharacterRestrictReal_tmul, pair_tmul_tmul, one_mul, one_mul]
    have hpos : (0 : ℝ) < (latticePairing A (characterRestrict
        (CommGroupScheme.groupHom τ) β) presQ.splitComponentCocharacter : ℝ) := by
      exact_mod_cast hβ'.2
    exact ⟨hpos.le, fun h => absurd h hpos.ne'⟩
  | zero =>
    rw [map_zero, map_zero, LinearMap.zero_apply]
    exact ⟨le_rfl, fun _ => rfl⟩
  | add y w _ _ hy hw =>
    rw [map_add, map_add, LinearMap.add_apply]
    refine ⟨add_nonneg hy.1 hw.1, fun h => ?_⟩
    have hy0 := le_antisymm (by linarith [hw.1]) hy.1
    have hw0 := le_antisymm (by linarith [hy.1]) hw.1
    rw [hy.2 hy0, hw.2 hw0, add_zero]
  | smul c y _ hy =>
    rw [show c • y = (c : ℝ) • y from rfl, map_smul, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    refine ⟨mul_nonneg c.2 hy.1, fun h => ?_⟩
    rcases mul_eq_zero.mp h with hc | hy0
    · rw [hc, zero_smul]
    · rw [hy.2 hy0, smul_zero]

/-- A nonzero vector of the nonnegative cone of `P'`, for the split component `a' ≫ φ`
of `M'`, restricts along `τ : A ⟶ A'` to a nonzero vector, whenever `Q` has a compatible
root presentation for `a`. -/
theorem restrictReal_ne_zero_of_mem_nonnegCone (τ : A ⟶ A')
    (hτ : CommGroupScheme.groupHom τ ≫ a' ≫ D.lQ' ≫ D.q' = a)
    (presQ : ParabolicRootPresentation q lQ a)
    (presM : ParabolicRootPresentation D.p' D.l' (a' ≫ D.φ.hom))
    {x : Vstar A'} (hx : x ∈ presM.nonnegCone) (hx0 : x ≠ 0) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom τ) x ≠ 0 := by
  intro h
  apply hx0
  refine (D.pair_restrictReal_nonneg_and_eq_zero τ hτ presQ presM hx).2 ?_
  rw [h, map_zero, LinearMap.zero_apply]

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
