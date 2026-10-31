import Langlands.Representation.Induction.CentralEvaluation
import Langlands.Representation.Classification.MaximalConeLifting

/-! coarse-central evaluation on the actual normalized refined induction. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uR uF uV

namespace GeneralLinear.BlockShape

/-- Repeat the scalar of an outer block at each of its flattened blocks. -/
def repeatCoarseScalars {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (R : Type uR) [CommRing R] :
    (Fin B.length → Rˣ) →* (Fin (B.flatten S).length → Rˣ) where
  toFun a := a ∘ B.flattenOuter S
  map_one' := rfl
  map_mul' _ _ := rfl

end GeneralLinear.BlockShape

namespace Geometric

/-- The actual refined Levi element given by coarse block scalars. -/
def coarseScalarRefinedLevi {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (R : Type uR) [CommRing R] :
    (Fin B.length → Rˣ) →* refinedLevi R B S :=
  (flattenedLeviEquiv R B S).toMonoidHom.comp
    (((B.flatten S).blockScalarLevi R).comp (B.repeatCoarseScalars S R))

@[simp] theorem coarseScalarRefinedLevi_val
    {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (R : Type uR) [CommRing R] (a : Fin B.length → Rˣ) :
    (coarseScalarRefinedLevi B S R a).val = B.blockScalarLevi R a :=
  B.flattenedLeviEquiv_blockScalarLevi_comp S R a

end Geometric

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Evaluation of normalized refined induction intertwines the actual coarse
scalar restrictions, with no residual normalizing character. -/
def refinedCoarseCentralEvaluation
    (σ : Representation ℂ (refinedLevi F.Carrier B S) V) (x : B.Levi F.Carrier) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    Representation.IntertwiningMap
      ((T.normalizedRefinedInduced B S σ).comp (B.blockScalarLevi F.Carrier))
      (σ.comp (coarseScalarRefinedLevi B S F.Carrier)) := by
  letI := T.topology
  letI := T.leviTopologicalGroup B
  refine
    { toFun := fun f => Induction.eval _ _ f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      isIntertwining' := ?_ }
  intro a
  ext f
  change Induction.eval _ _ f (x * B.blockScalarLevi F.Carrier a) =
    σ (coarseScalarRefinedLevi B S F.Carrier a) (Induction.eval _ _ f x)
  have hcov := normalizedRefinedInducedOf_covariant B S
    (T.refinedLeviHalfModulus B S) σ f
    (refinedLeviSection F.Carrier B S (coarseScalarRefinedLevi B S F.Carrier a)) x
  simp only [refinedLeviSection_val, refinedLeviProjection_section,
    coarseScalarRefinedLevi_val] at hcov
  rw [B.blockScalarLevi_commute F.Carrier a x] at hcov
  have hδ : T.refinedLeviHalfModulus B S
      (coarseScalarRefinedLevi B S F.Carrier a) = 1 :=
    T.refinedLeviHalfModulus_blockScalarLevi_comp B S a
  rw [hδ, Units.val_one, one_smul] at hcov
  exact hcov

/-- The exact common power is preserved at every evaluation. -/
theorem refinedCoarse_eval_mem_characterSpace
    (σ : Representation ℂ (refinedLevi F.Carrier B S) V)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) (k : ℕ) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ f, f ∈ characterSpace
      ((T.normalizedRefinedInduced B S σ).comp (B.blockScalarLevi F.Carrier)) χ k →
      ∀ x : B.Levi F.Carrier, Induction.eval _ _ f x ∈
        characterSpace (σ.comp (coarseScalarRefinedLevi B S F.Carrier)) χ k := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro f hf x
  exact map_mem_characterSpace_of_intertwiningMap
    (T.refinedCoarseCentralEvaluation B S σ x) χ k hf

/-- A generalized coarse scalar character of actual normalized refined induction
occurs in the same actual restriction of its inducing representation. -/
theorem normalizedRefinedInduced_coarse_character_reflects
    (σ : Representation ℂ (refinedLevi F.Carrier B S) V)
    (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    IsGeneralizedEigencharacter
      ((T.normalizedRefinedInduced B S σ).comp (B.blockScalarLevi F.Carrier)) χ →
    IsGeneralizedEigencharacter
      (σ.comp (coarseScalarRefinedLevi B S F.Carrier)) χ := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro hχ
  obtain ⟨k, f, hf0, hf⟩ := (isGeneralizedEigencharacter_iff _ _).mp hχ
  obtain ⟨x, hx⟩ := Induction.exists_smoothInduced_eval_ne_zero _ _ hf0
  exact isGeneralizedEigencharacter_of_map_ne_zero
    (T.refinedCoarseCentralEvaluation B S σ x) χ k
      ((mem_characterSpace _ _ _ _).mpr hf) hx

end PadicField.TopologicalData
end Langlands
