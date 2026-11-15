/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 85, 15 November 2026:
Extract M249.020 (localSeparableResidueAlgAction, lines 381–391) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
LocalResidueDatum.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, also in the opened namespaces. The source field
continuous_toFun cites the private source theorem
localSeparableResidueAlgAction_continuous (M249.019, lines 319–379), whose
proof is not published. The body instead proves the published closed target
Langlands.NYLL.PortInternal.M249.d019Statement in place, by the source proof
of lines 328–379, and applies it to K. In that proof the private source
lift localSelectedResidueLift and its lemma (M249.017, M249.018,
lines 306–317) are inlined as a local function and a local fact, and the
source instance localDecompositionResidueFinite (M249.014, lines 252–260) is
inlined as a local fact proved by its source proof. Import the Library
modules that publish the declarations used instead of the source imports.
Omit the open lines this definition does not need and all other
declarations. The docstring, type and toMonoidHom field are the source text.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U019.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U011.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields

/-!
# The continuous local residue action

For a nonarchimedean local field `K`, the residue action of the absolute
Galois group `Gal(SeparableClosure K / K)` on the selected residue field of
the chosen valuation ring of `SeparableClosure K`, as a continuous monoid
homomorphism for the two Krull topologies.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The continuous residue action on the chosen residue algebraic closure. -/
noncomputable def localSeparableResidueAlgAction :
    Gal(SeparableClosure K / K) →ₜ*
      (selectedResidueField (localSeparableValuationSubring K) ≃ₐ[
        decompositionResidueField K (localSeparableValuationSubring K)]
          selectedResidueField (localSeparableValuationSubring K)) where
  toMonoidHom :=
    residueAlgActionOfEqTop K
      (localSeparableValuationSubring K)
      (localSeparableDecompositionGroup_eq_top K)
  continuous_toFun := by
    have h019 : Langlands.NYLL.PortInternal.M249.d019Statement := by
      intro K _ _ _ _
      classical
      -- M249.014 (source instance `localDecompositionResidueFinite`), inlined
      have : Finite (decompositionResidueField K
          (localSeparableValuationSubring K)) := by
        have : Finite (localCompleteDVF K).residueField := by
          change Finite 𝓀[K]
          infer_instance
        exact Finite.of_equiv (localCompleteDVF K).residueField
          (localBaseResidueEquivDecompositionResidue K).toEquiv
      let A := localSeparableValuationSubring K
      let k : Type := decompositionResidueField K A
      let Omega : Type := selectedResidueField A
      let hA := localSeparableDecompositionGroup_eq_top K
      let rho := residueAlgActionOfEqTop K A hA
      -- M249.017 and M249.018 (source private `localSelectedResidueLift` and
      -- `localSelectedResidueLift_residue`), inlined
      let lift : Omega → A := fun x =>
        Classical.choose (IsLocalRing.residue_surjective x)
      have lift_residue : ∀ x : Omega, IsLocalRing.residue A (lift x) = x :=
        fun x => Classical.choose_spec (IsLocalRing.residue_surjective x)
      refine continuous_of_continuousAt_one rho ?_
      rw [ContinuousAt, MonoidHom.map_one, Filter.Tendsto]
      intro s hs
      rw [Filter.mem_map]
      rcases (krullTopology_mem_nhds_one_iff k Omega s).1 hs with
        ⟨E, hE, hEs⟩
      let : Algebra k E := E.algebra
      let : FiniteDimensional k E := hE
      let : Finite E := Module.finite_of_finite
        (decompositionResidueField K (localSeparableValuationSubring K))
      let : Fintype E := Fintype.ofFinite E
      let lifts : Finset (SeparableClosure K) :=
        Finset.univ.image (fun x : E =>
          ((lift (x : Omega) : A) : SeparableClosure K))
      let F : IntermediateField K (SeparableClosure K) :=
        IntermediateField.adjoin K (lifts : Set (SeparableClosure K))
      let : FiniteDimensional K F :=
        IntermediateField.finiteDimensional_adjoin (fun x _hx =>
          Algebra.IsIntegral.isIntegral x)
      refine (krullTopology_mem_nhds_one_iff K (SeparableClosure K)
        (rho ⁻¹' s)).2 ?_
      refine ⟨F, inferInstance, ?_⟩
      intro sigma hsigma
      apply hEs
      change rho sigma ∈ E.fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      let y : E := ⟨x, hx⟩
      let a : A := lift (y : Omega)
      have ha_lifts : (a : SeparableClosure K) ∈ lifts := by
        apply Finset.mem_image.mpr
        exact ⟨y, Finset.mem_univ y, rfl⟩
      have haF : (a : SeparableClosure K) ∈ F :=
        IntermediateField.subset_adjoin (F := K)
          (S := (lifts : Set (SeparableClosure K))) ha_lifts
      have hfix : sigma (a : SeparableClosure K) = (a : SeparableClosure K) :=
        (IntermediateField.mem_fixingSubgroup_iff F sigma).mp hsigma
          (a : SeparableClosure K) haF
      change rho sigma (y : Omega) = (y : Omega)
      rw [← lift_residue (y : Omega)]
      change IsLocalRing.residue A
          ((toDecompositionGroupOfEqTop
            K A hA sigma) • a) = IsLocalRing.residue A a
      congr 1
      apply Subtype.ext
      exact hfix
    exact h019 K

end

end Langlands.NYLL.LocalClassFieldTheory
