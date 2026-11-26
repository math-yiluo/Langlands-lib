import Langlands.GroupScheme.Absolute.ProperParabolicSolvableStatement
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.ParabolicBorelFactorization
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Proper parabolic subgroups and solvability -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 17.17. -/
theorem properParabolicSolvable : ProperParabolicSolvableStatement.{u} := by
  intro k _ _ G _ _ _
  constructor
  · rintro ⟨P, i, hi, hproper⟩ hsolv
    obtain ⟨B, b, f, hb, hf⟩ := hi.exists_isBorelSubgroup_factor
    have hId : IsClosedSubgroup (𝟙 G) :=
      inferInstanceAs (IsClosedImmersion (𝟙 G.X.left))
    have : IsIso b :=
      hb.maximal G (𝟙 G) b hId inferInstance inferInstance hsolv (Category.comp_id b)
    have : Mono i :=
      (Grp.forget _).mono_of_mono_map (f := i) hi.isClosedSubgroup.mono_overHom
    have : IsSplitEpi i := IsSplitEpi.mk' ⟨inv b ≫ f, by
      rw [Category.assoc, hf, IsIso.inv_hom_id]⟩
    exact hproper (isIso_of_mono_of_isSplitEpi i)
  · intro h
    obtain ⟨B, b, hb⟩ := (borelConjugacy k G).1
    have : IsIso (toAlgebraicClosure k) :=
      isIso_SpecMap_iff.mpr IsAlgClosed.algebraMap_bijective_of_isIntegral
    have hpar : IsParabolicSubgroup b :=
      ⟨hb.isClosedSubgroup, hb.smooth, _, _, 𝟙 _, hb.baseChange_of_isIso _, Category.id_comp _⟩
    refine ⟨B, b, hpar, ?_⟩
    intro hIso
    exact h (hb.isSolvableGroupScheme.of_iso (asIso b).symm)

end Langlands.GroupScheme
