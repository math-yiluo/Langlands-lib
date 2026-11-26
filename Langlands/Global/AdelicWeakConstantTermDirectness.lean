import Langlands.Global.AdelicTemperedVanishingReduction
import Langlands.Global.AdelicLeadingExponentDirectness
import Langlands.Automorphic.GroupSchemeInvariantFormsSubmodule

/-! # Uniqueness and automorphy of weak constant terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

/-- Directness of the polynomial orbits for the normalized labels. -/
theorem eq_zero_of_sum_eq_zero_of_hasExponent
    (s : Finset (ComplexCharacterParameter F (fam.P J)))
    (c : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ)
    (hc : ∀ lam ∈ s, fam.HasExponent J lam (c lam))
    (hz : ∑ lam ∈ s, c lam = 0) : ∀ lam ∈ s, c lam = 0 := by
  classical
  let e := Equiv.addRight (halfModulusParameter F (fam.P J))
  have hshift := fam.eq_zero_of_sum_eq_zero_of_hasUnnormalizedExponent J (s.map e.toEmbedding)
    (fun lam => c (e.symm lam))
  have hsum : ∑ lam ∈ s.map e.toEmbedding, c (e.symm lam) = 0 := by
    simpa only [Finset.sum_map, Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using hz
  have hspec : ∀ lam ∈ s.map e.toEmbedding, fam.HasUnnormalizedExponent J lam (c (e.symm lam)) := by
    intro lam hlam
    obtain ⟨mu, hmu, rfl⟩ := Finset.mem_map.mp hlam
    change fam.HasUnnormalizedExponent J (e mu) (c (e.symm (e mu)))
    rw [Equiv.symm_apply_apply]
    exact (fam.hasExponent_iff J mu (c mu)).mp (hc mu hmu)
  intro lam hlam
  simpa only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using
    hshift hspec hsum (e lam) (Finset.mem_map.mpr ⟨lam, hlam, rfl⟩)

/-- Two finite expansions of the same function give the same partial sum on any subset of
normalized labels. Terms absent from an expansion are interpreted as zero. -/
theorem sum_filter_eq_of_hasExponent
    (s t : Finset (ComplexCharacterParameter F (fam.P J)))
    (c d : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ)
    (hc : ∀ lam ∈ s, fam.HasExponent J lam (c lam))
    (hd : ∀ lam ∈ t, fam.HasExponent J lam (d lam))
    (he : ∑ lam ∈ s, c lam = ∑ lam ∈ t, d lam)
    (S : ComplexCharacterParameter F (fam.P J) → Prop) [DecidablePred S] :
    ∑ lam ∈ s.filter S, c lam = ∑ lam ∈ t.filter S, d lam := by
  classical
  let pad (u : Finset (ComplexCharacterParameter F (fam.P J)))
      (v : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ)
      (lam : ComplexCharacterParameter F (fam.P J)) := if lam ∈ u then v lam else 0
  have hpad (u : Finset (ComplexCharacterParameter F (fam.P J)))
      (v : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ)
      (hv : ∀ lam ∈ u, fam.HasExponent J lam (v lam)) (lam : ComplexCharacterParameter F (fam.P J)) :
      fam.HasUnnormalizedExponent J (lam + halfModulusParameter F (fam.P J)) (pad u v lam) := by
    by_cases h : lam ∈ u
    · simpa only [pad, ite_eq_left h] using (fam.hasExponent_iff J lam (v lam)).mp (hv lam h)
    · simpa only [pad, ite_eq_right h] using fam.hasUnnormalizedExponent_zero J
        (lam + halfModulusParameter F (fam.P J))
  have hsum (u : Finset (ComplexCharacterParameter F (fam.P J))) (hu : u ⊆ s ∪ t)
      (v : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ) :
      ∑ lam ∈ s ∪ t, pad u v lam = ∑ lam ∈ u, v lam := by
    simp only [pad, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hu]
  have hz : ∑ lam ∈ s ∪ t, (pad s c lam - pad t d lam) = 0 := by
    rw [Finset.sum_sub_distrib, hsum s Finset.subset_union_left,
      hsum t Finset.subset_union_right, he, sub_self]
  have hEq (lam : ComplexCharacterParameter F (fam.P J)) (hlam : lam ∈ s ∪ t) :
      pad s c lam = pad t d lam := by
    apply sub_eq_zero.mp
    apply fam.eq_zero_of_sum_eq_zero_of_hasExponent J (s ∪ t) _ (fun mu _ => ?_) hz lam hlam
    apply (fam.hasExponent_iff J mu _).mpr
    exact fam.hasUnnormalizedExponent_sub J (hpad s c hc mu) (hpad t d hd mu)
  have hfilter (u : Finset (ComplexCharacterParameter F (fam.P J))) (hu : u ⊆ s ∪ t)
      (v : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ) :
      ∑ lam ∈ u.filter S, v lam = ∑ lam ∈ (s ∪ t).filter S, pad u v lam := by
    have hInter : (s ∪ t).filter S ∩ u = u.filter S := by
      ext lam
      simp only [Finset.mem_inter, Finset.mem_filter]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hu h.1, h.2⟩, h.1⟩⟩
    simp only [pad, Finset.sum_ite_mem, hInter]
  rw [hfilter s Finset.subset_union_left, hfilter t Finset.subset_union_right]
  exact Finset.sum_congr rfl fun lam hlam => hEq lam (Finset.mem_filter.mp hlam).1

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {fam : StandardParabolicFamily F G} {J : StandardIndex F G fam.i fam.ν}
  {N d : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)} {rho : MatrixRepresentation G (Fin N)}
  {φ ψ χ : AdelicGroupPoints F G → ℂ}

/-- Each weak constant term is automorphic on its parabolic quotient. -/
theorem IsWeakConstantTerm.isAutomorphicOn
    (hψ : fam.IsWeakConstantTerm hsmooth Kinf rho J φ ψ) : fam.IsAutomorphicOn hsmooth Kinf rho J ψ := by
  classical
  obtain ⟨s, c, h, rfl⟩ := hψ
  unfold unitaryExponentSum
  exact (automorphicFunctionsOn _ _ _ _ _).sum_mem
    (fun lam hlam => h.automorphic lam (Finset.mem_filter.mp hlam).1)

/-- The weak constant term at a fixed index is unique whenever an exponent decomposition exists. -/
theorem IsWeakConstantTerm.unique
    (hψ : fam.IsWeakConstantTerm hsmooth Kinf rho J φ ψ)
    (hχ : fam.IsWeakConstantTerm hsmooth Kinf rho J φ χ) : ψ = χ := by
  obtain ⟨s, c, hs, rfl⟩ := hψ
  obtain ⟨t, d, ht, rfl⟩ := hχ
  classical
  exact fam.sum_filter_eq_of_hasExponent J s t c d hs.exponent ht.exponent
    (hs.sum_eq.symm.trans ht.sum_eq) (fun lam => parameterRealPart F (fam.P J) lam = 0)

end Langlands.Global.StandardParabolicFamily
