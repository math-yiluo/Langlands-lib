import Langlands.GroupScheme.Rational.ActionCocharacterWeights
import Langlands.GroupScheme.Rational.CharacterFpqcProof
import Langlands.GroupScheme.Dynamic.ActionLieCriterion
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Intrinsic weights of actions descended through a character -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Restriction is exact on each weight when it is injective on characters. -/
theorem actionWeightSpace_restrict_eq_of_injective
    (b : AutomorphicAction S.toGrp G)
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : T ⟶ S) (hf : Function.Injective (fun χ : characterLattice S => f ≫ χ))
    (χ : characterLattice S) :
    actionWeightSpace (b.restrict (CommGroupScheme.groupHom f)) (f ≫ χ) =
      actionWeightSpace b χ := by
  rw [actionWeightSpace_restrict_eq_iSup b hS hT f]
  apply le_antisymm
  · refine iSup_le fun ψ => iSup_le fun hψ => ?_
    rw [hf hψ]
  · exact le_iSup_of_le χ (le_iSup_of_le rfl le_rfl)

/-- The unchanged-vector linear equivalence supplied by faithful restriction
on characters of split acting tori. -/
def actionWeightSpaceRestrictEquiv
    (b : AutomorphicAction S.toGrp G)
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : T ⟶ S) (hf : Function.Injective (fun χ : characterLattice S => f ≫ χ))
    (χ : characterLattice S) :
    actionWeightSpace b χ ≃ₗ[k]
      actionWeightSpace (b.restrict (CommGroupScheme.groupHom f)) (f ≫ χ) :=
  LinearEquiv.ofEq _ _ (actionWeightSpace_restrict_eq_of_injective b hS hT f hf χ).symm

@[simp] theorem actionWeightSpaceRestrictEquiv_apply_coe
    (b : AutomorphicAction S.toGrp G)
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (f : T ⟶ S) (hf : Function.Injective (fun χ : characterLattice S => f ≫ χ))
    (χ : characterLattice S) (X : actionWeightSpace b χ) :
    (actionWeightSpaceRestrictEquiv b hS hT f hf χ X :
      Additive (lieKernel G k)) = X := rfl

private theorem character_comp_injective_of_epi (f : T ⟶ S)
    [Epi (CommGroupScheme.groupHom f).hom.hom.left] :
    Function.Injective (fun χ : characterLattice S => f ≫ χ) := by
  intro χ ψ h
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact (cancel_epi (CommGroupScheme.groupHom f).hom.hom.left).mp
    (congrArg (fun z : characterLattice T =>
      (CommGroupScheme.groupHom z).hom.hom.left) h)

variable (e : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G)
    (hS : IsSplitTorus S.toGrp) (a : characterLattice S) (ha : a ≠ 0)

include hS ha

/-- A nonzero character preserves exactly the weight corresponding to each
natural multiple, including zero. -/
theorem actionWeightSpace_restrict_character (n : ℕ) :
    actionWeightSpace (e.restrict (CommGroupScheme.groupHom a)) (n • a) =
      actionWeightSpace e (Gm.powerHom _ (n : ℤ)) := by
  obtain ⟨hqc, hflat, hsurj⟩ := characterFpqc k S hS a ha
  let := hflat
  let := hsurj
  let := Flat.epi_of_flat_of_surjective (CommGroupScheme.groupHom a).hom.hom.left
  have hpower : a ≫ Gm.powerHom _ (n : ℤ) = n • a := by
    rw [Gm.powerHom_apply, Preadditive.comp_zsmul, Category.comp_id, natCast_zsmul]
  simpa only [hpower] using
    actionWeightSpace_restrict_eq_of_injective e isSplitTorus_gm hS a
      (character_comp_injective_of_epi a) (Gm.powerHom _ (n : ℤ))

/-- Under a nonzero character, the cyclic positive span is exactly the
positive span of the descended multiplicative-group action. -/
theorem semigroupWeightSpan_restrict_character_cyclicTail :
    semigroupWeightSpan (e.restrict (CommGroupScheme.groupHom a)) (cyclicTail a 1) =
      e.positiveWeightSpan := by
  unfold semigroupWeightSpan AutomorphicAction.positiveWeightSpan
  apply le_antisymm
  · refine iSup_le fun χ => ?_
    rcases χ with ⟨χ, n, _, hn, rfl⟩
    rw [actionWeightSpace_restrict_character e hS a ha n]
    have hn' : n = (n - 1) + 1 := by omega
    rw [hn']
    simpa only [Nat.cast_add, Nat.cast_one] using
      (le_iSup (fun m : ℕ => actionWeightSpace e (Gm.powerHom _ (m + 1))) (n - 1))
  · refine iSup_le fun n => ?_
    have hmem : (n + 1) • a ∈ cyclicTail a 1 :=
      ⟨n + 1, by omega, by omega, rfl⟩
    refine le_iSup_of_le ⟨(n + 1) • a, hmem⟩ ?_
    rw [actionWeightSpace_restrict_character e hS a ha (n + 1)]
    simp only [Nat.cast_add, Nat.cast_one, le_refl]

/-- Full positive cyclic support forces the descended action to have full
strictly positive Lie span. -/
theorem positiveWeightSpan_eq_top_of_restrict_character
    (hfull : semigroupWeightSpan (e.restrict (CommGroupScheme.groupHom a))
      (cyclicTail a 1) = ⊤) :
    e.positiveWeightSpan = ⊤ := by
  rw [← semigroupWeightSpan_restrict_character_cyclicTail e hS a ha]
  exact hfull

end Langlands.GroupScheme.RelativeRoot
