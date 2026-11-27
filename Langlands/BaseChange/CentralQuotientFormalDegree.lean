import Langlands.BaseChange.PadicSquareIntegrableNotInduced
import Langlands.Group.GL.CentralQuotientMeasure
import Langlands.Group.GL.LeviCentralQuotientMeasure
import Langlands.Group.GL.LocalFieldTopology
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchurOrthogonality
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Langlands.Representation.LevelZero.Existence

/-!
# Formal degrees on the central quotient of `GL_n`

The predicate `IsCentralFormalDegree μ π d` says that the positive real `d` is the formal
degree of `π` for the measure `μ` on `G / Z(G)`: the Schur orthogonality relations

`∫_{G/Z} ℓ₁(π(g) v₁) ℓ₂(π(g⁻¹) v₂) dμ = d⁻¹ ℓ₂(v₁) ℓ₁(v₂)`

hold for all vectors and smooth functionals (Waldspurger 2003, III.1 (3)). For an irreducible
representation of `GL_n(F)` that is square-integrable modulo the center, such a `d` exists.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory JacquetLanglands

universe uG u uV

section Predicate

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [MeasurableSpace (G ⧸ Subgroup.center G)]

/-- `d` is the formal degree of `π` for the measure `μ` on the central quotient: `d > 0` and
for all vectors `v₁ v₂` and smooth functionals `ℓ₁ ℓ₂` the function
`gZ ↦ ℓ₁(π(g) v₁) ℓ₂(π(g⁻¹) v₂)` is `μ`-integrable with integral `d⁻¹ ℓ₂(v₁) ℓ₁(v₂)`
(Waldspurger 2003, III.1 (3), with `A_G` replaced by the full center). -/
def IsCentralFormalDegree (μ : Measure (G ⧸ Subgroup.center G)) {W : Type uV}
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G W) (d : ℝ) : Prop :=
  0 < d ∧ ∀ (v₁ v₂ : W) (ℓ₁ ℓ₂ : SmoothDual π), ∃ s : G ⧸ Subgroup.center G → ℂ,
    (∀ g : G, s (QuotientGroup.mk g) = ℓ₁.val (π g v₁) * ℓ₂.val (π g⁻¹ v₂)) ∧
    Integrable s μ ∧ ∫ q, s q ∂μ = (d : ℂ)⁻¹ * ℓ₂.val v₁ * ℓ₁.val v₂

end Predicate

section Existence

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (n : ℕ)

/-- Every Borel Haar measure on the central quotient of `GL_n(F)` is invariant under
inversion. -/
theorem centralQuotient_isInvInvariant :
    letI := centralQuotientMeasurableSpace F n
    ∀ (μ : Measure (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)))
      [μ.IsHaarMeasure], μ.IsInvInvariant := by
  let := centralQuotientMeasurableSpace F n
  have := centralQuotientBorelSpace F n
  intro μ _
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_secondCountableTopology F n
  have : IsClosed (Subgroup.center (GeneralLinear n F) : Set (GeneralLinear n F)) := by
    rw [Subgroup.coe_center, ← Set.centralizer_univ]
    exact Set.isClosed_centralizer _
  have : μ.Regular := inferInstance
  have := GeneralLinear.haar_centralQuotient_isMulRightInvariant μ
  exact Langlands.isInvInvariant_of_isMulRightInvariant μ

/-- An irreducible representation of `GL_n(F)` that is square-integrable modulo the center
has a formal degree for every Borel Haar measure on the central quotient. -/
theorem exists_isCentralFormalDegree :
    letI := centralQuotientMeasurableSpace F n
    ∀ (μ : Measure (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)))
      [μ.IsHaarMeasure] {W : Type uV} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear n F) W), IsSquareIntegrable π → π.IsIrreducible →
      ∃ d : ℝ, IsCentralFormalDegree μ π d := by
  let := centralQuotientMeasurableSpace F n
  have := centralQuotientBorelSpace F n
  intro μ _ W _ _ π hπ hi
  have := centralQuotient_isInvInvariant F n μ
  have hsq := (isSquareIntegrableModCentralSubgroup_center_iff π μ).mpr (hπ μ)
  obtain ⟨-, c, -⟩ := hπ μ
  have h : ∀ (a : Subgroup.center (GeneralLinear n F)) (x : W),
      π a x = (c.character a : ℂ) • x := c.acts
  have hcof := LevelZero.compactOpen_cofinal (F := F) n
  refine ⟨HarishChandraSchwartz.formalDegree _ le_rfl μ h hcof hsq hi,
    HarishChandraSchwartz.formalDegree_pos _ le_rfl μ h hcof hsq hi, ?_⟩
  intro v₁ v₂ ℓ₁ ℓ₂
  refine ⟨HarishChandraSchwartz.orthogonalityIntegrand _ h h v₁ ℓ₁.val v₂ ℓ₂.val,
    fun g => rfl,
    HarishChandraSchwartz.integrable_orthogonalityIntegrand _ le_rfl μ h h hsq hsq v₁ ℓ₁ v₂ ℓ₂,
    ?_⟩
  exact HarishChandraSchwartz.orthogonalityIntegral_eq_formalDegree _ le_rfl μ h hcof hsq hi
    v₁ ℓ₁ v₂ ℓ₂

end Existence

end Langlands.BaseChange
