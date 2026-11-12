import Langlands.ClassFieldTheory.Local.FiniteGaloisArtinRestriction
import Langlands.ClassFieldTheory.Local.CommonClosureReciprocityConstruction

/-! # Finite Artin restrictions of the actual common-closure candidate family -/

noncomputable section

namespace Langlands.LocalClassField.CommonClosure

open Weil.Local FiniteQuotientTransport ClassFieldTheory.Local

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance finiteArtinComparisonBaseCharZero : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier

/-- The finite Galois restriction of a common-closure candidate's unit map. -/
def candidateFiniteRestriction
    (e : CandidateFamily F (canonicalData F) (localResidueDegree F))
    (E : FiniteIntermediateExtension F.Carrier)
    (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : E.field ≤ M.toIntermediateField) :
    letI := finiteRestrictionAlgebra F.Carrier E M h
    letI := (canonicalData F E).topology
    E.fieldˣ →* Abelianization Gal(M/E.field) := by
  letI := finiteRestrictionAlgebra F.Carrier E M h
  letI := (canonicalData F E).topology
  exact (finiteAbelianRestriction F.Carrier E M h).comp
    (galoisHom F (canonicalData F) (localResidueDegree F) e E).toMonoidHom

/-- Transporting standalone geometric reciprocity to the actual fixing
subgroup preserves its finite geometric Artin symbols. -/
theorem candidateFiniteRestriction_familyOfStandalone
    (e : ∀ E : FiniteIntermediateExtension F.Carrier,
      WeilReciprocityCandidate (canonicalData F E)
        (localResidueDegree (E.asPadicField (p := p))))
    (he : ∀ E : FiniteIntermediateExtension F.Carrier,
      GeometricWeilReciprocityRelation (E.asPadicField (p := p)) (canonicalData F E) (e E))
    (E : FiniteIntermediateExtension F.Carrier)
    (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : E.field ≤ M.toIntermediateField) (a : E.fieldˣ) :
    letI := finiteRestrictionAlgebra F.Carrier E M h
    letI : IsScalarTower F.Carrier E.field M := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional E.field M := FiniteDimensional.right F.Carrier E.field M
    letI : Normal E.field M := Normal.tower_top_of_normal F.Carrier E.field M
    letI : IsGalois E.field M := ⟨⟩
    letI := (canonicalData F E).topology
    candidateFiniteRestriction F (familyOfStandalone F e) E M h a =
      FiniteArtinSymbol.abelianizedArtinSymbol (E.asPadicField (p := p)) M a⁻¹ := by
  let := finiteRestrictionAlgebra F.Carrier E M h
  let := (canonicalData F E).topology
  let : IsScalarTower F.Carrier E.field M := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower E.field M (AlgebraicClosure F.Carrier) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional E.field M := FiniteDimensional.right F.Carrier E.field M
  let : IsGalois E.field M :=
    { to_normal := Normal.tower_top_of_normal F.Carrier E.field M
      to_isSeparable := Algebra.isSeparable_tower_top_of_isSeparable F.Carrier E.field M }
  let θ := intermediateClosureEquiv F E
  let φ : M →ₐ[E.field] AlgebraicClosure E.field :=
    θ.symm.toAlgHom.comp (IsScalarTower.toAlgHom E.field M (AlgebraicClosure F.Carrier))
  let : Algebra M (AlgebraicClosure E.field) := φ.toRingHom.toAlgebra
  let : IsScalarTower E.field M (AlgebraicClosure E.field) :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  have hθ (x : M) :
      θ (algebraMap M (AlgebraicClosure E.field) x) = (x : AlgebraicClosure F.Carrier) := by
    change θ (θ.symm (x : AlgebraicClosure F.Carrier)) = _
    exact θ.apply_symm_apply x
  have hres (τ : Gal(AlgebraicClosure E.field/E.field)) :
      finiteRestrictionHom F.Carrier E M h (intermediateGaloisEquiv F E τ) =
        closureFiniteRestriction (E.asPadicField (p := p)) M τ := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap M (AlgebraicClosure E.field)).injective
    change algebraMap M (AlgebraicClosure E.field)
        (finiteRestrictionHom F.Carrier E M h (intermediateGaloisEquiv F E τ) x) =
      algebraMap M (AlgebraicClosure E.field) (τ.restrictNormal M x)
    rw [AlgEquiv.restrictNormal_commutes]
    apply θ.injective
    rw [hθ, finiteRestrictionHom_apply]
    have hh := intermediateClosureEquiv_galoisMap F E τ
      (algebraMap M (AlgebraicClosure E.field) x)
    rw [hθ] at hh
    exact hh
  have hcomp (z : Field.absoluteGaloisGroupAbelianization E.field) :
      finiteAbelianRestriction F.Carrier E M h (intermediateGaloisAbelianEquiv F E z) =
        closureFiniteAbelianRestriction (E.asPadicField (p := p)) M z := by
    induction z using QuotientGroup.induction_on with
    | H τ =>
      change finiteAbelianRestriction F.Carrier E M h
        (abelianizationProjection _ (intermediateGaloisEquiv F E τ)) =
          closureFiniteAbelianRestriction (E.asPadicField (p := p)) M
            (absoluteAbelianizationProjection E.field τ)
      rw [finiteAbelianRestriction_projection, closureFiniteAbelianRestriction_projection]
      change Abelianization.of
        (finiteRestrictionHom F.Carrier E M h (intermediateGaloisEquiv F E τ)) = _
      exact congrArg Abelianization.of (hres τ)
  change finiteAbelianRestriction F.Carrier E M h
    (galoisHom F (canonicalData F) (localResidueDegree F) (familyOfStandalone F e) E a) = _
  rw [galoisHom_familyOfStandalone]
  change finiteAbelianRestriction F.Carrier E M h
    (intermediateGaloisAbelianEquiv F E
      (candidateGaloisHom (canonicalData F E)
        (localResidueDegree (E.asPadicField (p := p))) (e E) a)) = _
  rw [hcomp]
  exact closureFiniteAbelianRestriction_geometric (E.asPadicField (p := p)) M
    (canonicalData F E) _ (he E).2 a

/-- Every finite restriction of the unconditionally constructed family is
the concrete geometric abelianized Artin symbol. -/
theorem candidateFiniteRestriction_constructed
    (E : FiniteIntermediateExtension F.Carrier)
    (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : E.field ≤ M.toIntermediateField) (a : E.fieldˣ) :
    letI := finiteRestrictionAlgebra F.Carrier E M h
    letI : IsScalarTower F.Carrier E.field M := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional E.field M := FiniteDimensional.right F.Carrier E.field M
    letI : Normal E.field M := Normal.tower_top_of_normal F.Carrier E.field M
    letI : IsGalois E.field M := ⟨⟩
    letI := (canonicalData F E).topology
    candidateFiniteRestriction F (constructedReciprocityFamily F) E M h a =
      FiniteArtinSymbol.abelianizedArtinSymbol (E.asPadicField (p := p)) M a⁻¹ :=
  candidateFiniteRestriction_familyOfStandalone F _
    (fun E => canonicalStandaloneReciprocity_geometric (E.asPadicField (p := p))) E M h a

end Langlands.LocalClassField.CommonClosure
