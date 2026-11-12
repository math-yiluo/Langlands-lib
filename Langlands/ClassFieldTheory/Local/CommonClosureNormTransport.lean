import Langlands.ClassFieldTheory.Local.CommonClosureCandidateTransport
import Langlands.ClassFieldTheory.Local.FiniteArtinSystemUniquenessProof

/-! # Norm and degree transport between prescribed intermediate Weil groups -/

noncomputable section

namespace Langlands.LocalClassField.CommonClosureTransport

open Weil Weil.Local LocalFactor.RankOne

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier

variable (E L : FiniteIntermediateExtension F.Carrier) (h : E.field ≤ L.field)

local instance : Algebra (Padic p) E.field := (E.asPadicField (p := p)).algebra
local instance : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra

/-- The literal inclusion of the prescribed finite intermediate fields as a p-adic embedding. -/
def intermediateInclusionEmbedding : E.field →ₐ[Padic p] L.field where
  toRingHom := (IntermediateField.inclusion h).toRingHom
  commutes' _ := rfl

/-- The actual common-closure subgroup inclusion viewed on standalone Weil groups. -/
def intermediateWeilInclusion :
    localWeilGroup (L.asPadicField (p := p)) →ₜ*
      localWeilGroup (E.asPadicField (p := p)) :=
  ((intermediateWeilEquiv F E).symm : _ →ₜ* _).comp
    ((E.weilInclusion L h (localResidueDegree F)).comp
      (intermediateWeilEquiv F L : _ →ₜ* _))

/-- The inclusion of Weil groups commutes with the literal ambient Galois projections. -/
theorem intermediateWeilInclusion_projection
    (y : localWeilGroup (L.asPadicField (p := p))) :
    intermediateGaloisMap F E
      (localProjection (E.asPadicField (p := p)) (intermediateWeilInclusion F E L h y)) =
      intermediateGaloisMap F L (localProjection (L.asPadicField (p := p)) y) := by
  change intermediateGaloisMap F E (localProjection (E.asPadicField (p := p))
    ((intermediateWeilEquiv F E).symm
      (E.weilInclusion L h (localResidueDegree F) (intermediateWeilEquiv F L y)))) = _
  rw [intermediateWeilEquiv_symm_projection]
  rfl

/-- The actual inclusion induces precisely the field norm under standalone geometric reciprocity. -/
theorem reciprocityUnits_intermediateWeilInclusion
    (eE : ReciprocityCandidate (E.asPadicField (p := p)))
    (hE : GeometricWeilReciprocityRelation (E.asPadicField (p := p))
      (CommonClosure.canonicalData F E) eE)
    (eL : ReciprocityCandidate (L.asPadicField (p := p)))
    (hL : GeometricWeilReciprocityRelation (L.asPadicField (p := p))
      (CommonClosure.canonicalData F L) eL)
    (y : localWeilGroup (L.asPadicField (p := p))) :
    reciprocityUnits (E.asPadicField (p := p)) eE (intermediateWeilInclusion F E L h y) =
      E.unitsNorm L h (reciprocityUnits (L.asPadicField (p := p)) eL y) := by
  let θ : AlgebraicClosure E.field ≃+* AlgebraicClosure L.field :=
    (intermediateClosureEquiv F E).toRingEquiv.trans
      (intermediateClosureEquiv F L).symm.toRingEquiv
  have hθ' (x : AlgebraicClosure E.field) :
      intermediateClosureEquiv F L (θ x) = intermediateClosureEquiv F E x :=
    (intermediateClosureEquiv F L).apply_symm_apply _
  have hθ (x : E.field) :
      θ (algebraMap E.field _ x) =
        algebraMap L.field _ (intermediateInclusionEmbedding F E L h x) := by
    apply (intermediateClosureEquiv F L).injective
    rw [hθ', intermediateClosureEquiv_algebraMap, intermediateClosureEquiv_algebraMap]
    rfl
  have hc (y : localWeilGroup (L.asPadicField (p := p))) (x : AlgebraicClosure E.field) :
      θ (AlgEquiv.toAlgHom (localProjection (E.asPadicField (p := p))
        (intermediateWeilInclusion F E L h y)) x) =
      AlgEquiv.toAlgHom (localProjection (L.asPadicField (p := p)) y) (θ x) := by
    apply (intermediateClosureEquiv F L).injective
    rw [hθ', ← intermediateClosureEquiv_galoisMap,
      ← intermediateClosureEquiv_galoisMap, intermediateWeilInclusion_projection, hθ']
  exact reciprocityUnits_compatible_closure (E.asPadicField (p := p))
    (L.asPadicField (p := p)) (intermediateInclusionEmbedding F E L h) θ hθ
    (intermediateWeilInclusion F E L h) hc eE hE eL hL y

/-- Standalone geometric order gives the base-field normalization on the prescribed subgroup. -/
theorem normalizedAbs_intermediateWeilEquiv_symm
    (T : F.TopologicalData)
    (eE : ReciprocityCandidate (E.asPadicField (p := p)))
    (hE : GeometricWeilReciprocityRelation (E.asPadicField (p := p))
      (CommonClosure.canonicalData F E) eE)
    (x : pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)) :
    (CommonClosure.canonicalData F E).normalizedAbs
      (reciprocityUnits (E.asPadicField (p := p)) eE
        ((intermediateWeilEquiv F E).symm x) : E.field) =
      (T.residueCardinality : ℝ) ^ (-localDegreeInt F x) := by
  let y := (intermediateWeilEquiv F E).symm x
  have hord := congrArg Multiplicative.toAdd
    (DFunLike.congr_fun hE.1 (WeilQuotients.projection
      (localResidueDegree (E.asPadicField (p := p))) y))
  change (CommonClosure.canonicalData F E).ord
    (reciprocityUnits (E.asPadicField (p := p)) eE y : E.field) =
      localDegreeInt (E.asPadicField (p := p)) y at hord
  dsimp only [CommonClosure.canonicalData] at hord ⊢
  rw [(E.asPadicField (p := p)).canonicalTopologicalData.normalizedAbs_of_ne_zero
    (Units.ne_zero _),
    hord, FiniteArtinSystemUniqueness.residueCardinality_eq_canonical F T,
    intermediateWeilEquiv_symm_degree, extensionResidueCardinality F
      (E.asPadicField (p := p)) (intermediateEmbedding F E), Nat.cast_pow,
    ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

end Langlands.LocalClassField.CommonClosureTransport
