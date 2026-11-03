import Langlands.GroupScheme.Rational.SemigroupWeightSupport

/-! # Intrinsic action weights under cocharacter restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    (b : AutomorphicAction S.toGrp G)

/-- Restricting the acting torus restricts each intrinsic character weight. -/
theorem actionWeightSpace_le_restrict (f : T ⟶ S) (χ : characterLattice S) :
    actionWeightSpace b χ ≤
      actionWeightSpace (b.restrict (CommGroupScheme.groupHom f)) (f ≫ χ) := by
  rw [actionWeightSpace_eq_lieWeightSpace, actionWeightSpace_eq_lieWeightSpace,
    AutomorphicAction.lieWeightSpace_restrict, Category.id_comp]
  intro X hX A _ _ t
  have h := hX A (t ≫ (CommGroupScheme.groupHom f).hom.hom)
  simpa only [Grp.id_hom_hom, Category.comp_id, Lie.characterValue_comp] using h

/-- The canonical linear inclusion of a weight space into its restricted weight. -/
abbrev actionWeightSpaceRestrictMap (f : T ⟶ S) (χ : characterLattice S) :
    actionWeightSpace b χ →ₗ[k]
      actionWeightSpace (b.restrict (CommGroupScheme.groupHom f)) (f ≫ χ) :=
  Submodule.inclusion (actionWeightSpace_le_restrict b f χ)

@[simp] theorem actionWeightSpaceRestrictMap_apply_coe
    (f : T ⟶ S) (χ : characterLattice S) (X : actionWeightSpace b χ) :
    (actionWeightSpaceRestrictMap b f χ X : Additive (lieKernel G k)) = X := rfl

variable [LocallyOfFiniteType G.X.hom]

/-- For split source and target tori, a restricted weight space is exactly the
sum of the original weight spaces with that restricted character. -/
theorem actionWeightSpace_restrict_eq_iSup
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : T ⟶ S) (ψ : characterLattice T) :
    actionWeightSpace (b.restrict (CommGroupScheme.groupHom f)) ψ =
      ⨆ χ : characterLattice S, ⨆ (_ : f ≫ χ = ψ), actionWeightSpace b χ := by
  classical
  let p := fun ψ : characterLattice T =>
    ⨆ χ : characterLattice S, ⨆ (_ : f ≫ χ = ψ), actionWeightSpace b χ
  have hp : (⨆ ψ, p ψ) = ⊤ := by
    apply top_unique
    rw [← iSup_actionWeightSpace_eq_top b hS]
    refine iSup_le fun χ => ?_
    exact le_iSup_of_le (f ≫ χ)
      (le_iSup_of_le χ (le_iSup_of_le rfl le_rfl))
  have hle : p ≤ actionWeightSpace (b.restrict (CommGroupScheme.groupHom f)) := by
    intro ψ
    refine iSup_le fun χ => iSup_le fun hχ => ?_
    simpa only [← hχ] using actionWeightSpace_le_restrict b f χ
  have heq := ((iSupIndep_actionWeightSpace
    (b.restrict (CommGroupScheme.groupHom f)) hT).le_iff_eq_of_iSup_eq_top hp).mp hle
  exact (congrFun heq ψ).symm

/-- A cocharacter weight is the sum of the torus character weights with that
integer pairing, for an arbitrary actual automorphic action. -/
theorem actionWeightSpace_cocharacter_eq_iSup
    (hS : IsSplitTorus S.toGrp) (ν : cocharacterLattice S) (m : ℤ) :
    actionWeightSpace (b.restrict (CommGroupScheme.groupHom ν)) (Gm.powerHom _ m) =
      ⨆ χ : characterLattice S, ⨆ (_ : latticePairing S χ ν = m),
        actionWeightSpace b χ := by
  have hpair (χ : characterLattice S) :
      (ν ≫ χ = Gm.powerHom _ m) ↔ latticePairing S χ ν = m := by
    rw [← (gmEndEquiv k).injective.eq_iff, Gm.powerHom_apply, gmEndEquiv_zsmul_id]
    rfl
  simpa only [hpair] using
    actionWeightSpace_restrict_eq_iSup b hS isSplitTorus_gm ν (Gm.powerHom _ m)

/-- The positive pairing region selects exactly the strictly positive weights
of the cocharacter-restricted action. -/
theorem semigroupWeightSpan_positive_eq_restrict
    (hS : IsSplitTorus S.toGrp) (ν : cocharacterLattice S) :
    semigroupWeightSpan b (positiveSemigroup ν) =
      ⨆ n : ℕ, actionWeightSpace (b.restrict (CommGroupScheme.groupHom ν))
        (Gm.powerHom _ (n + 1)) := by
  unfold semigroupWeightSpan
  apply le_antisymm
  · refine iSup_le fun χ => ?_
    have hχ : 0 < latticePairing S χ.val ν := χ.property
    let n : ℕ := (latticePairing S χ.val ν - 1).toNat
    have he : latticePairing S χ.val ν = (n : ℤ) + 1 := by
      dsimp [n]
      omega
    refine le_iSup_of_le n ?_
    rw [actionWeightSpace_cocharacter_eq_iSup b hS ν]
    exact le_iSup_of_le χ.val (le_iSup_of_le he le_rfl)
  · refine iSup_le fun n => ?_
    rw [actionWeightSpace_cocharacter_eq_iSup b hS ν]
    refine iSup_le fun χ => iSup_le fun he => ?_
    have hχ : χ ∈ positiveSemigroup ν := by
      change 0 < latticePairing S χ ν
      rw [he]
      omega
    exact le_iSup_of_le ⟨χ, hχ⟩ le_rfl

/-- A positive cyclic tail lies in the positive pairing halfspace whenever
its generating character pairs positively with the cocharacter. -/
theorem cyclicTail_le_positiveSemigroup
    {a : characterLattice S} (ν : cocharacterLattice S)
    (ha : 0 < latticePairing S a ν) (r : ℕ) :
    cyclicTail a r ≤ positiveSemigroup ν := by
  rintro χ ⟨n, _, hn, rfl⟩
  change 0 < latticePairing S (n • a) ν
  rw [map_nsmul]
  change 0 < n • latticePairing S a ν
  rw [nsmul_eq_mul]
  exact mul_pos (by exact_mod_cast hn) ha

end Langlands.GroupScheme.RelativeRoot
