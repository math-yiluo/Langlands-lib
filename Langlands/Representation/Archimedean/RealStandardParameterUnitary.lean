import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction
import Langlands.Representation.Archimedean.RealStandardNontrivialProof
import Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement

/-!
# Transport to an irreducible real standard module

An injection realizing a real standard parameter of an irreducible module is an isomorphism.
In particular, the canonical standard module inherits genericity and infinitesimal unitarity.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

universe uV

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ds : List RealBlock}
  {A : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] V}

/-- The compact-group intertwiner underlying a real standard intertwiner. -/
def IsRealStandardIntertwiner.toCompactIntertwiningMap
    (hA : IsRealStandardIntertwiner n ρ π ds A) :
    (realStandardRep n ds).IntertwiningMap ρ :=
  A.intertwiningMap_of_isIntertwiningMap _ _ hA.map_realStandardRep

/-- Pull infinitesimal unitarity back along an injective standard-module intertwiner. -/
theorem IsRealStandardIntertwiner.isUnitarizable_of_injective
    (hA : IsRealStandardIntertwiner n ρ π ds A) (hinj : Function.Injective A)
    (hunit : IsRealUnitarizableGKModule n ρ π) :
    IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds) := by
  obtain ⟨b, hb⟩ := hunit
  refine ⟨b.comap hA.toCompactIntertwiningMap hinj, fun X f g => ?_⟩
  change b.inner (A (realStandardLie n ds (1 ⊗ₜ X) f)) (A g) +
    b.inner (A f) (A (realStandardLie n ds (1 ⊗ₜ X) g)) = 0
  simpa only [hA.map_realStandardLie] using hb X (A f) (A g)

/-- Irreducibility, genericity, and infinitesimal unitarity pass to the standard module
realizing the parameter. -/
theorem realStandardParameter_model (hirr : IsIrreducibleGKModule ρ π)
    (hgen : IsRealGenericGKModule n π) (hunit : IsRealUnitarizableGKModule n ρ π)
    (hds : HasRealStandardParameter n ρ π ds) :
    realRank ds = n ∧
      IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) ∧
      IsRealGenericGKModule n (realStandardLie n ds) ∧
      IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds) := by
  obtain ⟨hrank, A, hinj, hA⟩ := hds
  change IsRealStandardIntertwiner n ρ π ds A at hA
  let hnontrivial := realStandardNontrivial n ds hrank
  have hA0 : A ≠ 0 := by
    obtain ⟨f, hf⟩ := exists_ne (0 : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    intro hzero
    exact hf (hinj (by simp [hzero]))
  have hsurj := hA.surjective hirr hA0
  refine ⟨hrank, ⟨hnontrivial, fun U hU₁ hU₂ => ?_⟩, ?_,
    hA.isUnitarizable_of_injective hinj hunit⟩
  · have hU := hA.isGKSubmodule_map ⟨hU₁, hU₂⟩
    have hmap := Submodule.map_injective_of_injective hinj
    rcases hirr.2 _ hU.1 hU.2 with hbot | htop
    · exact Or.inl (hmap (by simpa only [Submodule.map_bot] using hbot))
    · exact Or.inr (hmap (by simpa only [Submodule.map_top, LinearMap.range_eq_top.2 hsurj] using htop))
  · obtain ⟨ℓ, hℓ, a, ha, hact⟩ := hgen
    refine ⟨ℓ.comp A, ?_, a, ha, fun X hX f => ?_⟩
    · intro hzero
      apply hℓ
      ext v
      obtain ⟨f, rfl⟩ := hsurj v
      exact LinearMap.congr_fun hzero f
    · change ℓ (A (realStandardLie n ds (1 ⊗ₜ X) f)) = _
      rw [hA.map_realStandardLie]
      exact hact X hX (A f)

/-- A bound on the canonical standard modules supplies the bound in every carrier universe. -/
theorem realUnitaryGenericExponentBound_of_standard
    (hstandard : ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
      IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) →
      IsRealGenericGKModule n (realStandardLie n ds) →
      IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds) →
      ∀ x ∈ ds, |realBlockExponent x| < 1 / 2) :
    RealUnitaryGenericExponentBoundStatement.{uV} := by
  intro n V _ _ ρ π ds _ hirr _ hgen hunit hds
  obtain ⟨hrank, hirr', hgen', hunit'⟩ := realStandardParameter_model hirr hgen hunit hds
  exact hstandard n ds hrank hirr' hgen' hunit'

end Langlands.Archimedean
