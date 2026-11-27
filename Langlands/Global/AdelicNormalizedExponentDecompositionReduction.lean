import Langlands.Global.AdelicAutomorphicExponentDecompositionReduction
import Langlands.Global.AdelicAutomorphicConstantTermStatements

/-! # Normalized exponent decomposition from Harish-Chandra finiteness -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

/-- Parabolic Harish-Chandra finiteness gives the normalized decomposition at every
maximal Iwasawa compact by relabelling the ordinary exponent decomposition. -/
def AdelicNormalizedExponentDecompositionReductionStatement : Prop :=
  ParabolicHarishChandraFinitenessStatement.{0} → AdelicAutomorphicExponentDecompositionStatement

theorem adelicNormalizedExponentDecompositionReduction :
    AdelicNormalizedExponentDecompositionReductionStatement := by
  classical
  intro hHC F _ _ G _ _ _ _ K N d rho hsmooth hKmax hrho fam hIwasawa J f hf
  obtain ⟨s, c, hsum, hcomponents⟩ :=
    fam.exists_exponentDecomposition_of_parabolicHarishChandraFiniteness hHC hKmax hIwasawa
      rho hsmooth hrho J hf
  let delta := halfModulusParameter F (fam.P J)
  let e := (Equiv.addRight delta).symm
  refine ⟨s.map e.toEmbedding, c ∘ e.symm, ⟨?_, ?_, ?_⟩⟩
  · simpa only [Finset.sum_map, Function.comp_apply, Equiv.toEmbedding_apply,
      Equiv.symm_apply_apply] using hsum
  · intro lam hlam
    obtain ⟨mu, hmu, rfl⟩ := Finset.mem_map.mp hlam
    simpa only [Function.comp_apply, Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using
      (hcomponents mu hmu).1
  · intro lam hlam
    obtain ⟨mu, hmu, rfl⟩ := Finset.mem_map.mp hlam
    have hmu' : e mu + delta = mu := (Equiv.addRight delta).apply_symm_apply mu
    rw [fam.hasExponent_iff]
    change fam.HasUnnormalizedExponent J (e mu + delta) (c (e.symm (e mu)))
    rw [hmu', Equiv.symm_apply_apply]
    exact (hcomponents mu hmu).2.1

end Langlands.Global
