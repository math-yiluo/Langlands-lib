import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepParts
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # The completion of a local noetherian ring

For a local noetherian ring `R` with completion `R̂`, the morphism
`completionMap R : Spec R̂ ⟶ Spec R` is flat, surjective and quasi-compact. Moreover two
morphisms `Spec K ⟶ Spec R̂` from the spectrum of a ring with a point whose ideal is zero
(for instance a field) which agree after `completionMap R` are equal as soon as that point is
sent over the closed point of `Spec R`: the residue fields of `R` and `R̂` agree. -/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent

variable (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R]

lemma faithfullyFlat_completion :
    (algebraMap R (AdicCompletion (maximalIdeal R) R)).FaithfullyFlat := by
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

instance flat_completionMap : Flat (completionMap R) :=
  ((flat_and_surjective_SpecMap_iff _).2 (faithfullyFlat_completion R)).1

instance surjective_completionMap : Surjective (completionMap R) :=
  ((flat_and_surjective_SpecMap_iff _).2 (faithfullyFlat_completion R)).2

instance quasiCompact_completionMap : QuasiCompact (completionMap R) := by
  unfold completionMap
  infer_instance

/-- A ring map `α : R̂ ⟶ K` whose kernel lies over the maximal ideal of `R` kills the maximal
ideal of `R̂`. -/
lemma map_eq_zero_of_mem_maximalIdeal {K : CommRingCat.{u}}
    (α : CommRingCat.of (AdicCompletion (maximalIdeal R) R) ⟶ K) (x : Spec K)
    (hx₀ : x.asIdeal = ⊥) (hx : completionMap R (Spec.map α x) = closedPoint R) :
    ∀ y ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R), α.hom y = 0 := by
  have h₁ : (completionMap R (Spec.map α x)).asIdeal =
      Ideal.comap (algebraMap R (AdicCompletion (maximalIdeal R) R))
        (Ideal.comap α.hom x.asIdeal) := rfl
  rw [hx₀, ← RingHom.ker_eq_comap_bot, hx] at h₁
  have hle : (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ≤
      RingHom.ker α.hom :=
    Ideal.map_le_iff_le_comap.2 h₁.le
  intro y hy
  rw [AdicCompletion.maximalIdeal_eq_map] at hy
  exact RingHom.mem_ker.1 (hle hy)

/-- Two morphisms `Spec K ⟶ Spec R̂` which agree after `Spec R̂ ⟶ Spec R` are equal if `K` has
a point `x` with zero ideal sent over the closed point of `Spec R`. -/
lemma eq_of_comp_completionMap_eq {K : CommRingCat.{u}}
    {a b : Spec K ⟶ Spec (CommRingCat.of (AdicCompletion (maximalIdeal R) R))}
    (hab : a ≫ completionMap R = b ≫ completionMap R) (x : Spec K) (hx₀ : x.asIdeal = ⊥)
    (hx : completionMap R (a x) = closedPoint R) : a = b := by
  obtain ⟨α, rfl⟩ := Spec.map_surjective a
  obtain ⟨β, rfl⟩ := Spec.map_surjective b
  have hx' : completionMap R (Spec.map β x) = closedPoint R := by
    rw [← Scheme.Hom.comp_apply, ← hab, Scheme.Hom.comp_apply, hx]
  have hα := map_eq_zero_of_mem_maximalIdeal R α x hx₀ hx
  have hβ := map_eq_zero_of_mem_maximalIdeal R β x hx₀ hx'
  have hi : CommRingCat.ofHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) ≫ α =
      CommRingCat.ofHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) ≫ β := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact hab
  congr 1
  ext z
  show α.hom z = β.hom z
  obtain ⟨t, ht⟩ := (AdicCompletion.residueField_map_bijective R).2 (residue _ z)
  obtain ⟨r, rfl⟩ := residue_surjective t
  rw [ResidueField.map_residue] at ht
  have hd : algebraMap R (AdicCompletion (maximalIdeal R) R) r - z ∈
      maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
    rw [← residue_eq_zero_iff, map_sub, ht, sub_self]
  have hr : α.hom (algebraMap R (AdicCompletion (maximalIdeal R) R) r) =
      β.hom (algebraMap R (AdicCompletion (maximalIdeal R) R) r) := by
    have := congrArg (fun φ ↦ φ.hom r) hi
    simpa using this
  calc α.hom z = α.hom (algebraMap R _ r) - α.hom (algebraMap R _ r - z) := by
        rw [map_sub, sub_sub_cancel]
    _ = β.hom (algebraMap R _ r) - β.hom (algebraMap R _ r - z) := by
        rw [hα _ hd, hβ _ hd, hr]
    _ = β.hom z := by rw [map_sub, sub_sub_cancel]

end Langlands.AlgebraicGeometry.UnramifiedFunctor.CompletionDescent
