import Langlands.Representation.CuspidalSupport.LeviCuspidalQuotientStatement
import Langlands.Representation.CuspidalSupport.RefinedQuasicuspidalEmbeddingProof
import Langlands.Representation.CuspidalSupport.LeviCuspidalContragredientProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement
import Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Parabolic.RefinedInductionAdmissibility
import Langlands.Representation.Parabolic.NaturalInductionDualityProof
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.Induction.Equivalences
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.Shahidi.IntertwiningPadic

/-!
# Upper cuspidal quotients of irreducible admissible product-Levi representations

Apply the normalized refined quasicuspidal embedding theorem to the lifted
smooth dual. Irreducible quasicuspidal data are admissible and their smooth
duals are cuspidal. Exact smooth duality, natural same-parabolic induction
duality, and admissible bidual reflexivity give the actual upper quotient.
-/

noncomputable section

namespace Langlands.CuspidalSupport.QuotientAssembly

open GeneralLinear Geometric

universe uF uV uG uH

section Pullback

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The same functional identifies the smooth dual of a pullback with the
pullback of the smooth dual, using both continuous directions of the group
equivalence to identify smooth functionals. -/
def smoothDualPullbackEquiv (ρ : Representation ℂ G V) (e : H ≃ₜ* G) :
    (smoothContragredient (ρ.comp e.toMonoidHom)).Equiv
      ((smoothContragredient ρ).comp e.toMonoidHom) where
  toFun ℓ := ⟨ℓ.val,
    (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ.val).mp ℓ.property⟩
  invFun ℓ := ⟨ℓ.val,
    (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ.val).mpr ℓ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' h := by
    ext ℓ v
    change ℓ.val (ρ (e h⁻¹) v) = ℓ.val (ρ (e h)⁻¹ v)
    rw [map_inv]

end Pullback

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (D : BlockShape n) (R : BlockRefinement D)

/-- Admissible bidual reflexivity and compact-open separation preserve
irreducibility on the actual product Levi. -/
theorem leviSmoothDual_isIrreducible (σ : Rep.{uV} ℂ (D.Levi F.Carrier)) :
    letI := T.topology
    letI := T.leviTopologicalGroup D
    IsAdmissible σ.ρ → Representation.IsIrreducible σ.ρ →
      Representation.IsIrreducible (smoothContragredient σ.ρ) := by
  let := T.topology
  let := T.leviTopologicalGroup D
  intro hσ hirr
  exact (isIrreducible_smoothContragredient_iff_of_bidual
    (fun _ _ _ ρ hρ => smoothBidual_injective_of_compact_cofinal
      (T.leviCompactOpenCofinal D) ρ hρ)
    σ.ρ hσ.1
    ⟨smoothBidual_injective_of_compact_cofinal
        (T.leviCompactOpenCofinal D) σ.ρ hσ.1,
      smoothBidual_surjective_of_compact_cofinal
        (T.leviCompactOpenCofinal D) σ.ρ hσ⟩).mpr hirr

/-- Lift the input's smooth dual before taking the same-universe embedding.
This places the eventual inducing datum in the target carrier universe. -/
def liftedSmoothDual (σ : Rep.{uV} ℂ (D.Levi F.Carrier)) :
    letI := T.topology
    letI := T.leviTopologicalGroup D
    SmoothRep.{0, uF, max uF uV} ℂ (D.Levi F.Carrier) := by
  letI := T.topology
  letI := T.leviTopologicalGroup D
  exact SmoothRep.of (universeLiftRepresentation.{uF} (smoothContragredient σ.ρ))
    ((isSmooth_universeLift_iff _).mpr (isSmooth_smoothContragredient σ.ρ))

theorem liftedSmoothDual_isIrreducible (σ : Rep.{uV} ℂ (D.Levi F.Carrier)) :
    letI := T.topology
    letI := T.leviTopologicalGroup D
    IsAdmissible σ.ρ → Representation.IsIrreducible σ.ρ →
      (liftedSmoothDual T D σ).IsIrreducible := by
  let := T.topology
  let := T.leviTopologicalGroup D
  intro hσ hirr
  exact (isIrreducible_universeLift_iff _).mpr
    (leviSmoothDual_isIrreducible T D σ hσ hirr)

/-- Inflation, the common positive half modulus, and pointwise postcomposition
transport an actual equivalence through refined induction. -/
def refinedInducedEquiv {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (refinedLevi F.Carrier D R) V}
    {τ : Representation ℂ (refinedLevi F.Carrier D R) W}
    (e : ρ.Equiv τ) :
    letI := T.topology
    letI := T.leviTopologicalGroup D
    (T.normalizedRefinedInduced D R ρ).Equiv
      (T.normalizedRefinedInduced D R τ) := by
  letI := T.topology
  letI := T.leviTopologicalGroup D
  exact Induction.smoothInducedEquiv _
    (twistEquiv (T.refinedParabolicHalfModulus D R)
      (Representation.Equiv.mk e.toLinearEquiv
        (fun g => e.isIntertwining' (refinedLeviProjection F.Carrier D R g))))

/-- Zero exponent is identified propositionally before applying induction. -/
theorem fineTwist_zero (ω : Rep.{uV} ℂ ((D.flatten R).Levi F.Carrier)) :
    (RelativeJacquetMultiplicity.fineTwist T D R ω 0 0).ρ =
      ω.ρ.comp (flattenedLeviEquiv F.Carrier D R).symm.toMonoidHom := by
  change (T.leviRealPowerTwist (D.flatten R) (fun k => -(0 : ℝ) + 0) ω.ρ).comp _ = _
  have hz : (fun _ : Fin (D.flatten R).length => -(0 : ℝ) + 0) = 0 := by
    funext k
    simp
  rw [hz, T.leviRealPowerTwist_zero]

/-- Dualizing a concrete refined-induction embedding produces the exact
surjective quotient map after the induction-duality and canonical bidual
equivalences. The only mathematical input beyond published constructions is
cuspidality of the inducing datum's smooth dual. -/
theorem quotient_of_dual_embedding
    (σ : Rep.{uV} ℂ (D.Levi F.Carrier)) :
    letI := T.topology
    letI := T.leviTopologicalGroup D
    letI := T.leviTopologicalGroup (D.flatten R)
    ∀ (_hσ : IsAdmissible σ.ρ)
      (τ : SmoothRep.{0, uF, max uF uV} ℂ ((D.flatten R).Levi F.Carrier)),
      Representation.IsIrreducible τ.representation →
      IsLeviCuspidal (D.flatten R) τ.representation →
      IsLeviCuspidal (D.flatten R) (smoothContragredient τ.representation) →
      ∀ j : (smoothContragredient σ.ρ).IntertwiningMap
        (T.normalizedRefinedInduced D R
          (τ.representation.comp (flattenedLeviEquiv F.Carrier D R).symm.toMonoidHom)),
        Function.Injective j →
        ∃ (ω : Rep.{max uF uV} ℂ ((D.flatten R).Levi F.Carrier)),
          Representation.IsIrreducible ω.ρ ∧
          IsLeviCuspidal (D.flatten R) ω.ρ ∧
          ∃ q : (RelativeJacquetMultiplicity.innerInduced T D R
            (RelativeJacquetMultiplicity.fineTwist T D R ω 0 0)).ρ.IntertwiningMap σ.ρ,
            Function.Surjective q := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.leviTopologicalGroup D
  let := T.leviTopologicalGroup (D.flatten R)
  intro hσ τ hτirr hτ hτdual j hj
  let ω : Rep.{max uF uV} ℂ ((D.flatten R).Levi F.Carrier) :=
    Rep.of (smoothContragredient τ.representation)
  have hωirr : Representation.IsIrreducible ω.ρ :=
    leviSmoothDual_isIrreducible T (D.flatten R) (Rep.of τ.representation) hτ.1 hτirr
  refine ⟨ω, hωirr, hτdual, ?_⟩
  let φ := (flattenedLeviEquiv F.Carrier D R).symm.toMonoidHom
  let τ' : Rep.{max uF uV} ℂ (refinedLevi F.Carrier D R) :=
    Rep.of (τ.representation.comp φ)
  have hτ' : IsAdmissible τ'.ρ :=
    (Parabolic.isAdmissible_flattenedLeviTransport_iff F T D R τ.representation).mpr hτ.1
  obtain ⟨E, -⟩ := Parabolic.naturalNormalizedInductionDuality.{uF, max uF uV}.2
    p F T n D R
  let eInd := E τ' hτ'
  let ePull := smoothDualPullbackEquiv τ.representation
    (flattenedLeviEquivContinuous F.Carrier D R).symm
  let eTransport := refinedInducedEquiv T D R ePull
  let eBidual := (smoothBidual hσ.1).ofBijective
    ⟨smoothBidual_injective_of_compact_cofinal (T.leviCompactOpenCofinal D) σ.ρ hσ.1,
      smoothBidual_surjective_of_compact_cofinal (T.leviCompactOpenCofinal D) σ.ρ hσ⟩
  let q : (T.normalizedRefinedInduced D R (ω.ρ.comp φ)).IntertwiningMap σ.ρ :=
    eBidual.symm.toIntertwiningMap.comp
      ((contragredientMap j).comp
        ((eInd.symm.toIntertwiningMap).comp eTransport.symm.toIntertwiningMap))
  have hq : Function.Surjective q :=
    eBidual.symm.surjective.comp
      ((contragredientMap_surjective_of_injective_of_compact_cofinal
        (T.leviCompactOpenCofinal D) (isSmooth_smoothContragredient σ.ρ)
        (T.isSmooth_normalizedRefinedInduced D R τ'.ρ) j hj).comp
          (eInd.symm.surjective.comp eTransport.symm.surjective))
  have heq : (RelativeJacquetMultiplicity.fineTwist T D R ω 0 0).ρ = ω.ρ.comp φ :=
    fineTwist_zero T D R ω
  change ∃ q' : (T.normalizedRefinedInduced D R
      (RelativeJacquetMultiplicity.fineTwist T D R ω 0 0).ρ).IntertwiningMap σ.ρ,
    Function.Surjective q'
  rw [heq]
  exact ⟨q, hq⟩

/-- An embedding of the lifted dual with irreducible quasicuspidal data
provides the quotient once the independently owned cuspidal-dual theorem is
supplied. The lift is removed by its actual `up` intertwiner. -/
theorem quotient_of_quasicuspidal_lifted_embedding
    (σ : Rep.{uV} ℂ (D.Levi F.Carrier)) :
    letI := T.topology
    letI := T.leviTopologicalGroup D
    letI := T.leviTopologicalGroup (D.flatten R)
    IsAdmissible σ.ρ →
      ∀ (τ : SmoothRep.{0, uF, max uF uV} ℂ ((D.flatten R).Levi F.Carrier)),
      τ.IsIrreducible →
      IsLeviQuasicuspidal (D.flatten R) τ.representation →
      LeviCuspidalContragredientTheorem.{uF, max uF uV} F T (D.flatten R) →
      ∀ j : (liftedSmoothDual T D σ).representation.IntertwiningMap
        (T.normalizedRefinedInduced D R
          (τ.representation.comp (flattenedLeviEquiv F.Carrier D R).symm.toMonoidHom)),
        Function.Injective j →
        ∃ (ω : Rep.{max uF uV} ℂ ((D.flatten R).Levi F.Carrier)),
          Representation.IsIrreducible ω.ρ ∧
          IsLeviCuspidal (D.flatten R) ω.ρ ∧
          ∃ q : (RelativeJacquetMultiplicity.innerInduced T D R
            (RelativeJacquetMultiplicity.fineTwist T D R ω 0 0)).ρ.IntertwiningMap σ.ρ,
            Function.Surjective q := by
  let := T.topology
  let := T.leviTopologicalGroup D
  let := T.leviTopologicalGroup (D.flatten R)
  intro hσ τ hτirr hτquasi hdual j hj
  have hτ : IsLeviCuspidal (D.flatten R) τ.representation :=
    ⟨LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility
      F T (D.flatten R) τ hτirr hτquasi, hτquasi⟩
  let e := universeLiftEquiv.{uF} (smoothContragredient σ.ρ)
  exact quotient_of_dual_embedding T D R σ hσ τ hτirr hτ (hdual τ hτ)
    (j.comp e.toIntertwiningMap) (hj.comp e.injective)

end Langlands.CuspidalSupport.QuotientAssembly

namespace Langlands.CuspidalSupport

universe uF uV

/-- Every irreducible admissible representation of an actual product Levi is
an actual quotient of normalized upper refined induction from irreducible
cuspidal data, with the exact zero-twist and carrier universes of the statement. -/
theorem leviCuspidalQuotientTheorem : LeviCuspidalQuotientStatement.{uF, uV} := by
  intro p hp F T
  let := T.topology
  intro n _hn D σ hσirr hσadm
  let := T.leviTopologicalGroup D
  obtain ⟨R, τ, hτirr, hτquasi, j, hj⟩ :=
    normalizedRefinedQuasicuspidalEmbedding.{uF, max uF uV} F T n D
      (QuotientAssembly.liftedSmoothDual T D σ)
      (QuotientAssembly.liftedSmoothDual_isIrreducible T D σ hσadm hσirr)
  obtain ⟨ω, hωirr, hωcusp, q, hq⟩ :=
    QuotientAssembly.quotient_of_quasicuspidal_lifted_embedding T D R σ hσadm
      τ hτirr hτquasi (leviCuspidalContragredient F T (D.flatten R)) j hj
  exact ⟨R, ω, hωirr, hωcusp, q, hq⟩

end Langlands.CuspidalSupport
