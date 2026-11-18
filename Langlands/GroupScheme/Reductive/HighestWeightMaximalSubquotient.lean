import Langlands.GroupScheme.Reductive.HighestWeightSubquotientRepresentation
import Langlands.GroupScheme.Rational.SplitHighestWeightClassificationProof

/-! # The subquotient of a maximal weight of multiplicity one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation

variable {F : Type u} [Field F]
  {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
  {p : SplitPinning H} {n : Type} [Fintype n] [DecidableEq n]
  {ρ : MatrixRepresentation H n} {nu : characterLattice p.torus}

theorem HighestSubquotientData.incl_injective (D : p.HighestSubquotientData ρ nu) :
    Function.Injective D.incl.mulVecLin :=
  coordinateInclusion_injective (R := CommRingCat.of F) D.incl D.retr D.retr_incl

theorem HighestSubquotientData.proj_surjective (D : p.HighestSubquotientData ρ nu) :
    Function.Surjective D.proj.mulVecLin := by
  intro v
  refine ⟨D.sect *ᵥ v, ?_⟩
  change D.proj *ᵥ (D.sect *ᵥ v) = v
  rw [Matrix.mulVec_mulVec, D.proj_sect, Matrix.one_mulVec]

/-- The weight spaces of the subquotient are images of those of the subrepresentation. -/
theorem HighestSubquotientData.weightSpace_quot (D : p.HighestSubquotientData ρ nu)
    (mu : characterLattice p.torus) :
    p.representationWeightSpace D.quot mu =
      (p.representationWeightSpace D.sub mu).map D.proj.mulVecLin :=
  Intertwines.map_weightSpace_eq_of_surjective p D.proj_intertwines D.proj_surjective mu

theorem HighestSubquotientData.weightSpace_sub (D : p.HighestSubquotientData ρ nu)
    (mu : characterLattice p.torus) :
    (p.representationWeightSpace D.sub mu).map D.incl.mulVecLin =
      p.representationWeightSpace ρ mu ⊓ p.highestGenerated ρ nu := by
  rw [Intertwines.map_weightSpace_eq_inf_range p D.incl_intertwines D.retr_incl, D.range_incl]

/-- Every weight of the subquotient is a weight of the ambient representation. -/
theorem HighestSubquotientData.weightSpace_ne_bot (D : p.HighestSubquotientData ρ nu)
    {mu : characterLattice p.torus} (hmu : p.representationWeightSpace D.quot mu ≠ ⊥) :
    p.representationWeightSpace ρ mu ≠ ⊥ := by
  intro h0
  apply hmu
  rw [D.weightSpace_quot, eq_bot_iff]
  rintro _ ⟨u, hu, rfl⟩
  have hmem : D.incl.mulVecLin u ∈ p.representationWeightSpace ρ mu ⊓
      p.highestGenerated ρ nu := by
    rw [← D.weightSpace_sub]
    exact ⟨u, hu, rfl⟩
  rw [h0, bot_inf_eq, Submodule.mem_bot] at hmem
  have hu0 : u = 0 := D.incl_injective (hmem.trans (map_zero _).symm)
  rw [hu0, map_zero]
  exact Submodule.zero_mem _

/-- The `nu` weight space of the subquotient is a line. -/
theorem HighestSubquotientData.finrank_weightSpace_quot (D : p.HighestSubquotientData ρ nu)
    (hmult : Module.finrank F (p.representationWeightSpace ρ nu) = 1) :
    Module.finrank F (p.representationWeightSpace D.quot nu) = 1 := by
  have hsubnu : (p.representationWeightSpace D.sub nu).map D.incl.mulVecLin =
      p.representationWeightSpace ρ nu := by
    rw [D.weightSpace_sub, inf_eq_left.mpr (p.weightSpace_le_highestGenerated ρ nu)]
  have hfin_sub : Module.finrank F (p.representationWeightSpace D.sub nu) = 1 := by
    rw [← hmult, ← hsubnu, finrank_map_of_disjoint _ _ (by
      rw [LinearMap.ker_eq_bot.mpr D.incl_injective, inf_bot_eq])]
  have hdisj : p.representationWeightSpace D.sub nu ⊓ LinearMap.ker D.proj.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨hu, hk⟩ := Submodule.mem_inf.mp hu
    rw [D.ker_proj, Submodule.mem_comap] at hk
    have hu' : D.incl.mulVecLin u ∈ p.representationWeightSpace ρ nu := by
      rw [← hsubnu]
      exact ⟨u, hu, rfl⟩
    have h0 : D.incl.mulVecLin u ∈ p.highestRadical ρ nu ⊓ p.representationWeightSpace ρ nu :=
      Submodule.mem_inf.mpr ⟨hk, hu'⟩
    rw [p.highestRadical_inf_weightSpace ρ nu, Submodule.mem_bot] at h0
    rw [Submodule.mem_bot]
    exact D.incl_injective (h0.trans (map_zero _).symm)
  rw [D.weightSpace_quot, finrank_map_of_disjoint _ _ hdisj, hfin_sub]

/-- The subquotient of a weight of multiplicity one is irreducible. -/
theorem HighestSubquotientData.isIrreducible (D : p.HighestSubquotientData ρ nu)
    (hmult : Module.finrank F (p.representationWeightSpace ρ nu) = 1) :
    D.quot.IsIrreducible := by
  have hinj := D.incl_injective
  have hsurj := D.proj_surjective
  have hfin_quot := D.finrank_weightSpace_quot hmult
  have hnt : Nontrivial (Fin D.r → F) := by
    by_contra h
    have : Subsingleton (Fin D.r → F) := not_nontrivial_iff_subsingleton.mp h
    have h0 : Module.finrank F (p.representationWeightSpace D.quot nu) = 0 := by
      rw [Module.finrank_zero_iff]
      infer_instance
    omega
  refine ⟨hnt, fun W hW => ?_⟩
  have hW' := hW.comap D.proj_intertwines
  have hV := hW'.map D.incl_intertwines
  have hVX : (W.comap D.proj.mulVecLin).map D.incl.mulVecLin ≤ p.highestGenerated ρ nu := by
    rw [← D.range_incl]
    exact LinearMap.map_le_range
  have hYV : p.highestRadical ρ nu ≤ (W.comap D.proj.mulVecLin).map D.incl.mulVecLin := by
    intro y hy
    have hyX : y ∈ LinearMap.range D.incl.mulVecLin := by
      rw [D.range_incl]
      exact p.highestRadical_le ρ nu hy
    obtain ⟨u, rfl⟩ := hyX
    refine ⟨u, ?_, rfl⟩
    show D.proj.mulVecLin u ∈ W
    have hk : u ∈ LinearMap.ker D.proj.mulVecLin := by
      rw [D.ker_proj, Submodule.mem_comap]
      exact hy
    rw [LinearMap.mem_ker] at hk
    rw [hk]
    exact W.zero_mem
  rcases p.eq_highestRadical_or_eq_highestGenerated ρ nu hmult hV hYV hVX with h | h
  · left
    have hW'eq : W.comap D.proj.mulVecLin = LinearMap.ker D.proj.mulVecLin := by
      apply Submodule.map_injective_of_injective hinj
      rw [h, D.ker_proj, Submodule.map_comap_eq, D.range_incl,
        inf_eq_right.mpr (p.highestRadical_le ρ nu)]
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨u, rfl⟩ := hsurj w
    have : u ∈ W.comap D.proj.mulVecLin := hw
    rw [hW'eq, LinearMap.mem_ker] at this
    rw [this, Submodule.mem_bot]
  · right
    have hW'eq : W.comap D.proj.mulVecLin = ⊤ := by
      apply Submodule.map_injective_of_injective hinj
      rw [h, Submodule.map_top, D.range_incl]
    rw [eq_top_iff]
    intro w _
    obtain ⟨u, rfl⟩ := hsurj w
    have : u ∈ W.comap D.proj.mulVecLin := by rw [hW'eq]; trivial
    exact this

/-- The subquotient of a maximal weight of multiplicity one has that weight as highest weight
(Tits 1971, Proposition 3.4), using the highest-weight classification. -/
theorem HighestSubquotientData.isHighestWeight_of_maximal
    (D : p.HighestSubquotientData ρ nu)
    (hmult : Module.finrank F (p.representationWeightSpace ρ nu) = 1)
    (hmaximal : ∀ mu, p.representationWeightSpace ρ mu ≠ ⊥ →
      mu - nu ∈ p.positiveRootMonoid → mu = nu) :
    p.IsHighestWeight D.quot nu := by
  obtain ⟨nu', ⟨-, hnu'⟩, -⟩ := (splitHighestWeightClassification F H p).2.2 D.r D.quot (D.isIrreducible hmult)
  have hquot : p.representationWeightSpace D.quot nu ≠ ⊥ := by
    intro h0
    have := D.finrank_weightSpace_quot hmult
    rw [h0, finrank_bot] at this
    exact zero_ne_one this
  have hquot' : p.representationWeightSpace D.quot nu' ≠ ⊥ := by
    intro h0
    have := hnu'.2.2.1
    rw [h0, finrank_bot] at this
    exact zero_ne_one this
  have heq := hmaximal nu' (D.weightSpace_ne_bot hquot') (hnu'.2.2.2 nu hquot)
  exact heq ▸ hnu'

/-- The maximal weight of multiplicity one of the subquotient is dominant. -/
theorem HighestSubquotientData.isDominantWeight_of_maximal
    (D : p.HighestSubquotientData ρ nu)
    (hmult : Module.finrank F (p.representationWeightSpace ρ nu) = 1)
    (hmaximal : ∀ mu, p.representationWeightSpace ρ mu ≠ ⊥ →
      mu - nu ∈ p.positiveRootMonoid → mu = nu) :
    p.IsDominantWeight nu := by
  obtain ⟨nu', ⟨hdom, hnu'⟩, -⟩ := (splitHighestWeightClassification F H p).2.2 D.r D.quot (D.isIrreducible hmult)
  have hquot : p.representationWeightSpace D.quot nu ≠ ⊥ := by
    intro h0
    have := D.finrank_weightSpace_quot hmult
    rw [h0, finrank_bot] at this
    exact zero_ne_one this
  have hquot' : p.representationWeightSpace D.quot nu' ≠ ⊥ := by
    intro h0
    have := hnu'.2.2.1
    rw [h0, finrank_bot] at this
    exact zero_ne_one this
  have heq := hmaximal nu' (D.weightSpace_ne_bot hquot') (hnu'.2.2.2 nu hquot)
  exact heq ▸ hdom

end Langlands.GroupScheme.SplitPinning

namespace Langlands.GroupScheme

/-- The subquotient of a maximal weight of multiplicity one is irreducible with that dominant
highest weight (Tits 1971, Proposition 3.4), relative to the split highest-weight
classification. -/
def MaximalWeightSubquotientStatement : Prop :=
  ∀ (F : Type u) [Field F] (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom H.X.hom]
      (p : SplitPinning H) (n : Type) [Fintype n] [DecidableEq n]
      (ρ : MatrixRepresentation H n) (nu : characterLattice p.torus)
      (D : p.HighestSubquotientData ρ nu),
      Module.finrank F (p.representationWeightSpace ρ nu) = 1 →
      (∀ mu, p.representationWeightSpace ρ mu ≠ ⊥ → mu - nu ∈ p.positiveRootMonoid → mu = nu) →
        p.IsHighestWeight D.quot nu ∧ p.IsDominantWeight nu

theorem maximalWeightSubquotient : MaximalWeightSubquotientStatement.{u} := by
  intro F _ H _ p n _ _ ρ nu D hmult hmaximal
  exact ⟨D.isHighestWeight_of_maximal hmult hmaximal,
    D.isDominantWeight_of_maximal hmult hmaximal⟩

end Langlands.GroupScheme
