import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof

/-!
# Finite irreducible restriction to the determinant-unit subgroup of a product Levi

BZ76 Lemma 3.26, in its reduced spanning form: the restriction of an irreducible smooth
complex representation of a product Levi to its determinant-unit subgroup `G°` is
semisimple and is spanned by finitely many irreducible subrepresentations.

The centre acts by scalars by Schur's lemma in countable dimension, the countable
dimension coming from the Cartan decomposition of the Levi. The subgroup `G°` joined
with the centre has finite index (BZ76 3.20(b)), so Clifford's argument applies.
-/

noncomputable section

namespace Langlands.CuspidalSupport.FiniteRestriction

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- The centre of a product Levi acts by scalars on an irreducible smooth complex
representation. -/
theorem exists_scalar_center {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    IsSmooth ρ → ρ.IsIrreducible →
      ∀ z : Subgroup.center (B.Levi F.Carrier), ∃ c : ℂ, ∀ v : V, ρ z v = c • v := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  intro hρ hirr z
  obtain ⟨ϖ, hϖ⟩ := Iwasawa.exists_isUniformizingElement F.Carrier
  have hrank : Module.rank ℂ V ≤ Cardinal.aleph0 :=
    LeviAdmissibility.rank_le_aleph0_of_doubleCoset_cover ρ hρ hirr
      (LeviAdmissibility.integralLevi B) (LeviAdmissibility.isCompact_integralLevi B)
      (Set.range (LeviAdmissibility.leviTorus B ϖ)) (Set.countable_range _) fun g => by
        obtain ⟨k₁, hk₁, lam, -, k₂, hk₂, hg⟩ := LeviAdmissibility.exists_levi_cartan B hϖ g
        exact ⟨k₁, hk₁, _, ⟨lam, rfl⟩, k₂, hk₂, hg⟩
  exact LeviAdmissibility.exists_scalar_of_central ρ hrank hirr z.val
    (Subgroup.mem_center_iff.mp z.property)

/-- BZ76 Lemma 3.26, reduced form: the restriction of an irreducible smooth complex
representation of a product Levi to the determinant-unit subgroup is semisimple and is
the sum of finitely many irreducible subrepresentations. Only irreducibility is
assumed. -/
theorem leviFiniteRestriction (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}
    (B : BlockShape n) :
    letI := T.topology
    ∀ D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier), D.IsIrreducible →
      let ρD := determinantUnitRestriction T B D.representation
      Representation.IsSemisimpleRepresentation ρD ∧
      ∃ (m : ℕ) (V : Fin m → Subrepresentation ρD),
        (∀ i, Representation.IsIrreducible (V i).toRepresentation) ∧
        (⨆ i, (V i).toSubmodule) = ⊤ := by
  let := T.topology
  intro D hD
  have := determinantUnit_sup_center_finiteIndex T B
  exact FiniteIndexRestriction.finite_irreducible_restriction D.representation
    (determinantUnitSubgroup T B) hD
    (exists_scalar_center T B D.representation D.isSmooth hD)

end Langlands.CuspidalSupport.FiniteRestriction
