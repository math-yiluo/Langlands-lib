import Langlands.GroupScheme.Rational.GenericLieWeights

/-! # Adjoint weights under restriction between split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section RestrictionMap

variable {R : CommRingCat.{u}} {T T' : CommGroupScheme (Spec R)}
  {G : GroupScheme (Spec R)} [IsAffineHom G.X.hom]

/-- Restrict an actual adjoint root whose character remains nonzero. -/
def rootRestriction (f : T' ⟶ T) (i : T.toGrp ⟶ G) :
    {χ : characterLattice T // χ ∈ roots i ∧ f ≫ χ ≠ 0} →
      roots (CommGroupScheme.groupHom f ≫ i) := fun χ =>
  ⟨f ≫ χ.val, χ.property.2, fun hbot => χ.property.1.2 (bot_unique (by
    have hle := weightSpace_le_comp f i χ.val
    rwa [hbot] at hle))⟩

@[simp]
theorem rootRestriction_val (f : T' ⟶ T) (i : T.toGrp ⟶ G)
    (χ : {χ : characterLattice T // χ ∈ roots i ∧ f ≫ χ ≠ 0}) :
    (rootRestriction f i χ : characterLattice T') = f ≫ χ.val := rfl

end RestrictionMap

theorem submodule_eq_iSup_of_refinement
    {K V I J : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq J]
    (p : I → Submodule K V) (q : J → Submodule K V)
    (hp : iSup p = ⊤) (hq : DirectSum.IsInternal q)
    (f : I → J) (hf : ∀ i, p i ≤ q (f i)) (j : J) :
    q j = ⨆ i : {i // f i = j}, p i.val := by
  classical
  let π := weightComponentProjection q hq j
  have hπ_same {x : V} (hx : x ∈ q j) : π x = x :=
    weightComponentProjection_of_mem q hq j hx
  have hπ_other {j' : J} {x : V} (hx : x ∈ q j') (hj : j' ≠ j) :
      π x = 0 :=
    weightComponentProjection_of_mem_ne q hq j hx hj
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ iSup p := by rw [hp]; trivial
    have hπ : π x ∈ ⨆ i : {i // f i = j}, p i.val := by
      refine Submodule.iSup_induction p
        (motive := fun y => π y ∈ ⨆ i : {i // f i = j}, p i.val) hx' ?_ ?_ ?_
      · intro i y hy
        by_cases hi : f i = j
        · rw [hπ_same (hi ▸ hf i hy)]
          exact Submodule.mem_iSup_of_mem ⟨i, hi⟩ hy
        · rw [hπ_other (hf i hy) hi]
          exact Submodule.zero_mem _
      · simpa only [map_zero] using
          (⨆ i : {i // f i = j}, p i.val).zero_mem
      · intro y z hy hz
        simpa only [map_add] using
          (⨆ i : {i // f i = j}, p i.val).add_mem hy hz
    rwa [hπ_same hx] at hπ
  · refine iSup_le fun i => ?_
    simpa only [i.property] using hf i.val

variable {k : Type u} [Field k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Each weight space of the restricted split-torus action is the sum of the
original weight spaces whose characters have that restriction. -/
theorem weightSpace_comp_eq_iSup (hT : IsSplitTorus T.toGrp)
    (hT' : IsSplitTorus T'.toGrp) (f : T' ⟶ T) (i : T.toGrp ⟶ G)
    (ψ : characterLattice T') :
    weightSpace (CommGroupScheme.groupHom f ≫ i) ψ =
      ⨆ χ : {χ : characterLattice T // f ≫ χ = ψ}, weightSpace i χ.val := by
  classical
  exact submodule_eq_iSup_of_refinement (weightSpace i)
    (weightSpace (CommGroupScheme.groupHom f ≫ i))
    (isInternal_weightSpace_of_isSplitTorus k G T hT i).submodule_iSup_eq_top
    (isInternal_weightSpace_of_isSplitTorus k G T' hT' _)
    (fun χ => f ≫ χ) (weightSpace_le_comp f i) ψ

/-- The roots of a restricted split-torus action are exactly the nonzero
restrictions of the roots of the original action. -/
theorem mem_roots_comp_iff (hT : IsSplitTorus T.toGrp)
    (hT' : IsSplitTorus T'.toGrp) (f : T' ⟶ T) (i : T.toGrp ⟶ G)
    (ψ : characterLattice T') :
    ψ ∈ roots (CommGroupScheme.groupHom f ≫ i) ↔
      ψ ≠ 0 ∧ ∃ χ ∈ roots i, f ≫ χ = ψ := by
  classical
  constructor
  · intro hψ
    have hex : ∃ χ : {χ : characterLattice T // f ≫ χ = ψ},
        weightSpace i χ.val ≠ ⊥ := by
      by_contra h
      apply hψ.2
      rw [weightSpace_comp_eq_iSup hT hT' f i ψ]
      apply iSup_eq_bot.mpr
      intro χ
      exact not_not.mp fun hn => h ⟨χ, hn⟩
    obtain ⟨⟨χ, hχψ⟩, hχ⟩ := hex
    refine ⟨hψ.1, χ, ⟨?_, hχ⟩, hχψ⟩
    intro hz
    apply hψ.1
    rw [← hχψ, hz]
    simp
  · rintro ⟨hψ, χ, hχ, rfl⟩
    refine ⟨hψ, ?_⟩
    intro hbot
    apply hχ.2
    apply bot_unique
    have hle := weightSpace_le_comp f i χ
    rwa [hbot] at hle

/-- Every root for the restricted split-torus action is the restriction of
an original root whose restriction is nonzero. -/
theorem rootRestriction_surjective (hT : IsSplitTorus T.toGrp)
    (hT' : IsSplitTorus T'.toGrp) (f : T' ⟶ T) (i : T.toGrp ⟶ G) :
    Function.Surjective (rootRestriction f i) := by
  intro ψ
  obtain ⟨hψ, χ, hχ, hχψ⟩ := (mem_roots_comp_iff hT hT' f i ψ.val).mp ψ.property
  refine ⟨⟨χ, hχ, ?_⟩, ?_⟩
  · simpa only [hχψ] using hψ
  · exact Subtype.ext hχψ

/-- Negation stability descends along restriction between split tori. -/
theorem neg_mem_roots_comp (hT : IsSplitTorus T.toGrp)
    (hT' : IsSplitTorus T'.toGrp) (f : T' ⟶ T) (i : T.toGrp ⟶ G)
    (hneg : ∀ χ ∈ roots i, -χ ∈ roots i)
    {ψ : characterLattice T'}
    (hψ : ψ ∈ roots (CommGroupScheme.groupHom f ≫ i)) :
    -ψ ∈ roots (CommGroupScheme.groupHom f ≫ i) := by
  rw [mem_roots_comp_iff hT hT' f i] at hψ ⊢
  refine ⟨neg_ne_zero.mpr hψ.1, ?_⟩
  obtain ⟨χ, hχ, hχψ⟩ := hψ.2
  refine ⟨-χ, hneg χ hχ, ?_⟩
  rw [Preadditive.comp_neg, hχψ]

end Langlands.GroupScheme
