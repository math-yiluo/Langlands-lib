import Langlands.BaseChange.SigmaLiftCharacterIdentity.Localization
import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.Global.AdelicFunctoriality.LocalNormNeighborhood

/-!
# Cutting ordinary test functions by a norm condition on the determinant

The norms of the units of a finite commutative algebra of positive dimension over a
nonarchimedean local field of characteristic zero form a clopen subgroup of the units of the
field. Cutting the ordinary function of a concordant pair by a conjugation-invariant clopen
condition which holds at every class associated with a twisted class preserves concordance;
the twisted function is left unchanged.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Topology Langlands.HarmonicAnalysis Langlands.TraceFormula
open Langlands.JacquetLanglands Langlands.QuotientIntegration

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

section NormRange

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]

/-- Over a nonarchimedean local field of characteristic zero, the `m`-th powers of units form
a neighborhood of `1` for every `m ≠ 0`. -/
theorem range_pow_mem_nhds_one_of_localField {m : ℕ} (hm : m ≠ 0) :
    Set.range (fun x : Fˣ => x ^ m) ∈ 𝓝 (1 : Fˣ) := by
  let := LocalGalois.localNormedField F
  have := LocalGalois.localNormedField_complete F
  exact Global.AdelicFunctoriality.range_pow_mem_nhds_one hm

/-- Over a nonarchimedean local field of characteristic zero, the norms of the units of a
finite commutative algebra of positive dimension form an open subgroup of the units. -/
theorem isOpen_normUnitsRange {E : Type*} [CommRing E] [Algebra F E]
    (hE : Module.finrank F E ≠ 0) :
    IsOpen ((Units.map (Algebra.norm F : E →* F)).range : Set Fˣ) := by
  apply Subgroup.isOpen_of_mem_nhds
  refine Filter.mem_of_superset (range_pow_mem_nhds_one_of_localField hE) ?_
  rintro _ ⟨u, rfl⟩
  refine ⟨Units.map (algebraMap F E).toMonoidHom u, Units.ext ?_⟩
  exact Algebra.norm_algebraMap (u : F)

/-- Over a nonarchimedean local field of characteristic zero, the norms of the units of a
finite commutative algebra of positive dimension form a clopen subgroup of the units. -/
theorem isClopen_normUnitsRange {E : Type*} [CommRing E] [Algebra F E]
    (hE : Module.finrank F E ≠ 0) :
    IsClopen ((Units.map (Algebra.norm F : E →* F)).range : Set Fˣ) :=
  ⟨Subgroup.isClosed_of_isOpen _ (isOpen_normUnitsRange hE), isOpen_normUnitsRange hE⟩

end NormRange

namespace ConcordanceLocalization

section Concordance

variable {Y : Type*} [TopologicalSpace Y]
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {E : Type*} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
variable {n l : ℕ} {σ : E ≃ₐ[F] E}
variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
variable {μF : Measure (GeneralLinear n F)} {μE : Measure (GeneralLinear n E)}
variable {φ : SchwartzBruhat (GeneralLinear n E)} {f : SchwartzBruhat (GeneralLinear n F)}

/-- Cutting only the ordinary function on a conjugation-invariant parameter preserves both
clauses of concordance, provided the parameter of every class associated with a twisted
class lies in the clopen set. -/
lemma concordant_cutoff_ordinary (h : AreConcordant σ l μF μE φ f)
    {q : GeneralLinear n F → Y} (hq : Continuous q) (hF : ∀ x γ, q (x⁻¹ * γ * x) = q γ)
    {B : Set Y} (hB : IsClopen B)
    (hassoc : ∀ δ γ, IsNormAssociated σ l δ γ → q γ ∈ B) :
    AreConcordant σ l μF μE φ (cutoff (hB.preimage hq) f) := by
  classical
  constructor
  · intro γ hreg hnorm μγ _ _ νγ hνγ
    have horb := orbital_cutoff (MonoidHom.id (GeneralLinear n F)) q hq hB hF γ νγ f
    change orbitalIntegral γ νγ (cutoff (hB.preimage hq) f) =
      (if q γ ∈ B then orbitalIntegral γ νγ f else 0) at horb
    change orbitalIntegral γ νγ (cutoff (hB.preimage hq) f) = 0
    rw [horb, h.1 γ hreg hnorm μγ νγ hνγ, ite_self]
  · intro δ γ ha hreg μδ _ _ μγ _ _ νδ νγ hνδ hνγ hμ
    have horb := orbital_cutoff (MonoidHom.id (GeneralLinear n F)) q hq hB hF γ νγ f
    change orbitalIntegral γ νγ (cutoff (hB.preimage hq) f) =
      (if q γ ∈ B then orbitalIntegral γ νγ f else 0) at horb
    change sigmaOrbitalIntegral σ n δ νδ φ = orbitalIntegral γ νγ (cutoff (hB.preimage hq) f)
    rw [horb, ite_eq_left (hassoc δ γ ha), h.2 δ γ ha hreg μδ μγ νδ νγ hνδ hνγ hμ]

end Concordance

end ConcordanceLocalization

end Langlands.BaseChange
