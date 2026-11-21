import Langlands.BaseChange.PseudoCoefficientExistenceStatement
import Langlands.BaseChange.SquareIntegrableNotInducedStatement
import Langlands.BaseChange.TwistedPseudoCoefficientExistenceStatement
import Langlands.Representation.Classification.LeviDiscreteSeriesTemperedProof

/-!
# Pseudo-coefficients of square-integrable representations from the twisted statement

The specialization `E = F`, `σ = 1`, `l = 1` of `TwistedPseudoCoefficientExistenceStatement`
gives `PseudoCoefficientExistenceStatement`, once a square-integrable representation is known
not to be isomorphic to a representation induced from a proper standard parabolic subgroup.
With that fact as the premise `SquareIntegrableNotInducedStatement`, this module shows that
every irreducible square-integrable representation is a σ-discrete series representation for
`σ = 1`, and proves the conditional reduction. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis GeneralLinear

universe uG uV u

/-! ## Twisted pseudo-coefficients for an automorphism equal to the identity -/

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ]

/-- A twisted pseudo-coefficient for an automorphism `θ` equal to the identity, with the
identity intertwiner, is a pseudo-coefficient. -/
theorem isPseudoCoefficient_of_isTwistedPseudoCoefficient_of_eq_refl
    {θ : G ≃* G} (hθ : θ = MulEquiv.refl G) {χ : Subgroup.center G →* ℂˣ}
    {π : Representation ℂ G V} {hπ : IsAdmissible π}
    {A : π.Equiv (π.comp θ.toMonoidHom)} (hA : A.toLinearMap = LinearMap.id)
    {f : SchwartzBruhat G} (h : IsTwistedPseudoCoefficient μ θ χ π hπ A f) :
    IsPseudoCoefficient μ χ π hπ f := by
  subst hθ
  exact isPseudoCoefficient_of_isTwistedPseudoCoefficient_refl μ hA h

end Generic

/-! ## `σ = 1` on `GL_n` -/

section SigmaOne

variable {F : Type u} [Field F]

/-- The entrywise action of the identity automorphism is the identity. -/
theorem entrywiseAut_one_eq_refl (n : ℕ) :
    entrywiseAut (1 : F ≃ₐ[F] F) n = MulEquiv.refl (GeneralLinear n F) :=
  MulEquiv.ext fun g => entrywiseAut_one_apply g

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The identity map of `V`, as an isomorphism of `π` onto `π^σ` for `σ = 1`. -/
def sigmaIntertwinerOne (n : ℕ) (π : Representation ℂ (GeneralLinear n F) V) :
    SigmaIntertwiner (1 : F ≃ₐ[F] F) n π :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) fun g => by
    ext v
    simp [entrywiseAut_one_apply]

@[simp]
theorem sigmaIntertwinerOne_toLinearMap (n : ℕ) (π : Representation ℂ (GeneralLinear n F) V) :
    (sigmaIntertwinerOne n π).toLinearMap = LinearMap.id :=
  rfl

end SigmaOne

/-! ## Square-integrable representations are σ-discrete series for `σ = 1` -/

section SquareIntegrable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A square-integrable representation of `GL_n(F)` is tempered. -/
theorem isTemperedRep_of_isSquareIntegrable {π : Representation ℂ (GeneralLinear n F) V}
    (h : JacquetLanglands.IsSquareIntegrable π) : IsTemperedRep π := by
  let _ : MeasurableSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)) :=
    borel _
  have _ : BorelSpace (GeneralLinear n F ⧸ Subgroup.center (GeneralLinear n F)) := ⟨rfl⟩
  intro μ _
  exact isTemperedModCenter_of_squareIntegrable μ (h μ)

/-- Given `SquareIntegrableNotInducedStatement`, an irreducible square-integrable
representation of `GL_n(F)` is a σ-discrete series representation for `σ = 1`. -/
theorem isSigmaDiscreteSeries_one_of_isSquareIntegrable [CharZero F]
    (hNI : SquareIntegrableNotInducedStatement.{u, uV})
    {π : Representation ℂ (GeneralLinear n F) V} (hirr : π.IsIrreducible)
    (hsq : JacquetLanglands.IsSquareIntegrable π) :
    IsSigmaDiscreteSeries (1 : F ≃ₐ[F] F) n π :=
  ⟨hsq.isAdmissible, hirr, isTemperedRep_of_isSquareIntegrable hsq,
    ⟨sigmaIntertwinerOne n π⟩,
    fun B hB X _ _ Ξ hΞ _ => hNI F n V π hirr hsq B hB X Ξ hΞ⟩

end SquareIntegrable

/-! ## The reduction -/

/-- Conditional form of `PseudoCoefficientExistenceStatement`: the twisted statement (at
equal field universes) and `SquareIntegrableNotInducedStatement` imply it. -/
def PseudoCoefficientExistenceReductionStatement.{v, w} : Prop :=
  TwistedPseudoCoefficientExistenceStatement.{v, v, w} →
    SquareIntegrableNotInducedStatement.{v, w} → PseudoCoefficientExistenceStatement.{v, w}

/-- The reduction: specialize the twisted statement to `E = F`, `σ = 1`, `l = 1` and the
identity intertwiner. -/
theorem pseudoCoefficientExistenceReduction :
    PseudoCoefficientExistenceReductionStatement.{u, uV} := by
  intro hT hNI F _ _ _ _ _ n
  let _ : MeasurableSpace (GeneralLinear n F) := borel _
  have _ : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  intro V _ _ π hπ hirr hsq χ hχ μ _
  have hds := isSigmaDiscreteSeries_one_of_isSquareIntegrable hNI hirr hsq
  obtain ⟨φ, hφ⟩ := hT F F 1 1 n isCyclicAlgebra_one V π hπ hds χ hχ
    (sigmaIntertwinerOne n π) μ
  exact ⟨φ, isPseudoCoefficient_of_isTwistedPseudoCoefficient_of_eq_refl μ
    (entrywiseAut_one_eq_refl n) (sigmaIntertwinerOne_toLinearMap n π) hφ⟩

end Langlands.BaseChange
