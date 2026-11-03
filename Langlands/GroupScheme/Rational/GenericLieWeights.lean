import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.Torus.WeightDecomposition
import Mathlib.Algebra.DirectSum.Decomposition

/-! # Zero adjoint weight spaces of generic cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section Restriction

variable {R : CommRingCat.{u}} {T T' : CommGroupScheme (Spec R)}
  {G : GroupScheme (Spec R)} [IsAffineHom G.X.hom]

/-- Restricting the acting group restricts each character weight. -/
theorem weightSpace_le_comp (f : T' ⟶ T) (i : T.toGrp ⟶ G)
    (χ : characterLattice T) :
    weightSpace i χ ≤ weightSpace (CommGroupScheme.groupHom f ≫ i) (f ≫ χ) := by
  intro X hX A _ _ t
  rw [Lie.characterValue_comp]
  change adjoint G A ((t ≫ (CommGroupScheme.groupHom f).hom.hom) ≫ i.hom.hom) _ = _
  exact hX A (t ≫ (CommGroupScheme.groupHom f).hom.hom)

end Restriction

/-- The linear projection onto one summand of an internal submodule decomposition. -/
def weightComponentProjection
    {K V J : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq J]
    (q : J → Submodule K V) (hq : DirectSum.IsInternal q) (j : J) : V →ₗ[K] V :=
  let := hq.chooseDecomposition
  (q j).subtype ∘ₗ DirectSum.component K J (fun j => q j) j ∘ₗ
    (DirectSum.decomposeLinearEquiv q).toLinearMap

theorem weightComponentProjection_of_mem
    {K V J : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq J]
    (q : J → Submodule K V) (hq : DirectSum.IsInternal q) (j : J)
    {x : V} (hx : x ∈ q j) : weightComponentProjection q hq j x = x := by
  let := hq.chooseDecomposition
  exact DirectSum.decompose_of_mem_same q hx

theorem weightComponentProjection_of_mem_ne
    {K V J : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq J]
    (q : J → Submodule K V) (hq : DirectSum.IsInternal q) (j : J)
    {j' : J} {x : V} (hx : x ∈ q j') (hj : j' ≠ j) :
    weightComponentProjection q hq j x = 0 := by
  let := hq.chooseDecomposition
  exact DirectSum.decompose_of_mem_ne q hx hj

private theorem submodule_eq_of_weight_restriction
    {K V I J : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq J]
    (p : I → Submodule K V) (q : J → Submodule K V)
    (hp : iSup p = ⊤) (hq : DirectSum.IsInternal q)
    (f : I → J) (hf : ∀ i, p i ≤ q (f i)) (i₀ : I) (j₀ : J)
    (h₀ : f i₀ = j₀) (h : ∀ i, f i = j₀ → p i ≤ p i₀) :
    q j₀ = p i₀ := by
  classical
  let π := weightComponentProjection q hq j₀
  have hπ_same {x : V} (hx : x ∈ q j₀) : π x = x := by
    exact weightComponentProjection_of_mem q hq j₀ hx
  have hπ_other {j : J} {x : V} (hx : x ∈ q j) (hj : j ≠ j₀) :
      π x = 0 := by
    exact weightComponentProjection_of_mem_ne q hq j₀ hx hj
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ iSup p := by rw [hp]; trivial
    have hπ : π x ∈ p i₀ := by
      refine Submodule.iSup_induction p (motive := fun y => π y ∈ p i₀) hx' ?_ ?_ ?_
      · intro i y hy
        by_cases hi : f i = j₀
        · rw [hπ_same (hi ▸ hf i hy)]
          exact h i hi hy
        · rw [hπ_other (hf i hy) hi]
          exact (p i₀).zero_mem
      · simpa only [map_zero] using (p i₀).zero_mem
      · intro x y hx hy
        simpa only [map_add] using (p i₀).add_mem hx hy
    rwa [hπ_same hx] at hπ
  · simpa only [h₀] using hf i₀

section Generic

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Projection onto an actual adjoint character weight space of a split torus. -/
def weightSpaceProjection (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (χ : characterLattice T) :
    Additive (lieKernel G k) →ₗ[k] Additive (lieKernel G k) := by
  classical
  exact weightComponentProjection (weightSpace i)
    (isInternal_weightSpace_of_isSplitTorus k G T hT i) χ

theorem weightSpaceProjection_of_mem (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (χ : characterLattice T) {X : Additive (lieKernel G k)}
    (hX : X ∈ weightSpace i χ) : weightSpaceProjection hT i χ X = X := by
  classical
  exact weightComponentProjection_of_mem _ _ _ hX

theorem weightSpaceProjection_of_mem_ne (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (χ : characterLattice T) {ψ : characterLattice T}
    {X : Additive (lieKernel G k)} (hX : X ∈ weightSpace i ψ) (hψ : ψ ≠ χ) :
    weightSpaceProjection hT i χ X = 0 := by
  classical
  exact weightComponentProjection_of_mem_ne _ _ _ hX hψ

/-- On the actual Lie algebra, a generic cocharacter has exactly the same zero
weight space as its split torus. -/
theorem weightSpace_zero_genericCocharacter (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν) :
    weightSpace (CommGroupScheme.groupHom ν ≫ i) 0 = weightSpace i 0 := by
  classical
  apply submodule_eq_of_weight_restriction (weightSpace i)
    (weightSpace (CommGroupScheme.groupHom ν ≫ i))
    (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSup_eq_top
    (isInternal_weightSpace_of_isSplitTorus k G _ isSplitTorus_gm _)
    (fun χ => ν ≫ χ) (weightSpace_le_comp ν i) 0 0 (by simp)
  intro χ hχ
  by_cases hχ0 : χ = 0
  · subst χ
    exact le_rfl
  · have hbot : weightSpace i χ = ⊥ := by
      by_contra hnonzero
      have h := hν χ ⟨hχ0, hnonzero⟩
      apply h
      rw [latticePairing_apply, hχ, map_zero]
    rw [hbot]
    exact bot_le

end Generic

end Langlands.GroupScheme
