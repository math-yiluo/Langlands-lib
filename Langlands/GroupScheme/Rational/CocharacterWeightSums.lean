import Langlands.GroupScheme.Rational.GenericLieWeights
import Langlands.GroupScheme.Rational.ActionWeightComparisonProof

/-! # Cocharacter weight sums and character-pairing regions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem submodule_eq_iSup_of_weight_restriction
    {K V I J : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq J]
    (p : I → Submodule K V) (q : J → Submodule K V)
    (hp : iSup p = ⊤) (hq : DirectSum.IsInternal q)
    (f : I → J) (hf : ∀ i, p i ≤ q (f i)) (j₀ : J) :
    q j₀ = ⨆ i, ⨆ (_ : f i = j₀), p i := by
  classical
  let π := weightComponentProjection q hq j₀
  let P : Submodule K V := ⨆ i, ⨆ (_ : f i = j₀), p i
  have hπ_same {x : V} (hx : x ∈ q j₀) : π x = x :=
    weightComponentProjection_of_mem q hq j₀ hx
  have hπ_other {j : J} {x : V} (hx : x ∈ q j) (hj : j ≠ j₀) :
      π x = 0 :=
    weightComponentProjection_of_mem_ne q hq j₀ hx hj
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ iSup p := by rw [hp]; trivial
    have hπ : π x ∈ P := by
      refine Submodule.iSup_induction p (motive := fun y => π y ∈ P) hx' ?_ ?_ ?_
      · intro i y hy
        by_cases hi : f i = j₀
        · rw [hπ_same (hi ▸ hf i hy)]
          have hle : p i ≤ P := le_iSup_of_le i (le_iSup_of_le hi le_rfl)
          exact hle hy
        · rw [hπ_other (hf i hy) hi]
          exact P.zero_mem
      · simpa only [map_zero] using P.zero_mem
      · intro x y hx hy
        simpa only [map_add] using P.add_mem hx hy
    rwa [hπ_same hx] at hπ
  · refine iSup_le fun i => iSup_le fun hi => ?_
    simpa only [hi] using hf i

section Cocharacter

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Each cocharacter weight space is the sum of all torus character weight
spaces whose pairing is that weight. No genericity hypothesis is needed. -/
theorem weightSpace_cocharacter_eq_iSup (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (m : ℤ) :
    weightSpace (CommGroupScheme.groupHom ν ≫ i) (Gm.powerHom _ m) =
      ⨆ χ : characterLattice S, ⨆ (_ : latticePairing S χ ν = m), weightSpace i χ := by
  classical
  have h := submodule_eq_iSup_of_weight_restriction (weightSpace i)
    (weightSpace (CommGroupScheme.groupHom ν ≫ i))
    (isInternal_weightSpace_of_isSplitTorus k G S hS i).submodule_iSup_eq_top
    (isInternal_weightSpace_of_isSplitTorus k G _ isSplitTorus_gm _)
    (fun χ => ν ≫ χ) (weightSpace_le_comp ν i) (Gm.powerHom _ m)
  have hpair (χ : characterLattice S) :
      (ν ≫ χ = Gm.powerHom _ m) ↔ latticePairing S χ ν = m := by
    rw [← (gmEndEquiv k).injective.eq_iff, Gm.powerHom_apply, gmEndEquiv_zsmul_id]
    rfl
  simpa only [hpair] using h

end Cocharacter

namespace RelativeRoot

section ActionComparison

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]

/-- The span of the adjoint weight spaces selected by a character semigroup. -/
def adjointSemigroupWeightSpan (i : S.toGrp ⟶ G)
    (A : AddSubsemigroup (characterLattice S)) :
    Submodule k (Additive (lieKernel G k)) :=
  ⨆ χ : A, weightSpace i χ.val

/-- For conjugation, the intrinsic semigroup weight span is the adjoint span. -/
theorem semigroupWeightSpan_conjugation (i : S.toGrp ⟶ G)
    (A : AddSubsemigroup (characterLattice S)) :
    semigroupWeightSpan (AutomorphicAction.conjugation i) A =
      adjointSemigroupWeightSpan i A := by
  unfold semigroupWeightSpan adjointSemigroupWeightSpan
  apply iSup_congr
  intro χ
  exact actionWeightSpace_conjugation i χ.val

variable [LocallyOfFiniteType G.X.hom]

/-- Nonnegative cocharacter weights are precisely the torus weights in the
nonnegative pairing region. -/
theorem semigroupWeightSpan_conjugation_nonnegative
    (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    semigroupWeightSpan (AutomorphicAction.conjugation i) (nonnegativeSemigroup ν) =
      ⨆ n : ℕ, weightSpace (CommGroupScheme.groupHom ν ≫ i) (Gm.powerHom _ n) := by
  rw [semigroupWeightSpan_conjugation, adjointSemigroupWeightSpan]
  apply le_antisymm
  · refine iSup_le fun χ => ?_
    have hχ : 0 ≤ latticePairing S χ.val ν := χ.property
    have he : latticePairing S χ.val ν = ((latticePairing S χ.val ν).toNat : ℤ) :=
      (Int.toNat_of_nonneg hχ).symm
    refine le_iSup_of_le (latticePairing S χ.val ν).toNat ?_
    rw [weightSpace_cocharacter_eq_iSup hS i ν]
    refine le_iSup_of_le χ.val ?_
    exact le_iSup_of_le he le_rfl
  · refine iSup_le fun n => ?_
    rw [weightSpace_cocharacter_eq_iSup hS i ν]
    refine iSup_le fun χ => iSup_le fun he => ?_
    have hχ : χ ∈ nonnegativeSemigroup ν := by
      change 0 ≤ latticePairing S χ ν
      rw [he]
      exact Int.natCast_nonneg n
    exact le_iSup_of_le ⟨χ, hχ⟩ le_rfl

/-- Zero cocharacter weight is the span of the torus weights in the zero pairing
region. -/
theorem semigroupWeightSpan_conjugation_zero
    (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    semigroupWeightSpan (AutomorphicAction.conjugation i) (zeroSemigroup ν) =
      weightSpace (CommGroupScheme.groupHom ν ≫ i) (Gm.powerHom _ 0) := by
  rw [semigroupWeightSpan_conjugation, adjointSemigroupWeightSpan,
    weightSpace_cocharacter_eq_iSup hS i ν]
  exact iSup_subtype

/-- Strictly positive cocharacter weights are precisely the torus weights in the
positive pairing region. -/
theorem semigroupWeightSpan_conjugation_positive
    (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    semigroupWeightSpan (AutomorphicAction.conjugation i) (positiveSemigroup ν) =
      ⨆ n : ℕ, weightSpace (CommGroupScheme.groupHom ν ≫ i) (Gm.powerHom _ (n + 1)) := by
  rw [semigroupWeightSpan_conjugation, adjointSemigroupWeightSpan]
  apply le_antisymm
  · refine iSup_le fun χ => ?_
    have hχ : 0 < latticePairing S χ.val ν := χ.property
    let n : ℕ := (latticePairing S χ.val ν - 1).toNat
    have he : latticePairing S χ.val ν = (n : ℤ) + 1 := by
      dsimp [n]
      omega
    refine le_iSup_of_le n ?_
    rw [weightSpace_cocharacter_eq_iSup hS i ν]
    refine le_iSup_of_le χ.val ?_
    exact le_iSup_of_le he le_rfl
  · refine iSup_le fun n => ?_
    rw [weightSpace_cocharacter_eq_iSup hS i ν]
    refine iSup_le fun χ => iSup_le fun he => ?_
    have hχ : χ ∈ positiveSemigroup ν := by
      change 0 < latticePairing S χ ν
      rw [he]
      omega
    exact le_iSup_of_le ⟨χ, hχ⟩ le_rfl

end ActionComparison

end RelativeRoot

end Langlands.GroupScheme
