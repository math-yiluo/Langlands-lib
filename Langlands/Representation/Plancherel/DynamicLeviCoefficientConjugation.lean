import Langlands.Representation.Plancherel.LeviCoefficientConjugation
import Langlands.Representation.Plancherel.DynamicOppositeConjugationScalar
import Langlands.Representation.Plancherel.CompactProductInducedCoefficients

/-! # Rational-point translation on the actual dynamic coefficient fibers -/

noncomputable section

set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.DynamicCoefficientConjugation

open Aubert.General DynamicOppositeStandardIntertwining
open DynamicOppositeCanonicalScalar

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (g : RationalPoint F G.X)

/-- The original conjugation theorem in the inverse-image convention used
by the actual induction translation. -/
theorem parabolic_mem_conjugation (x : RationalPoint F G.X) :
    x ∈ parabolic (χ ≫ (G.innerIso g).hom) ↔ g⁻¹ * x * g ∈ parabolic χ := by
  simpa [rationalPointsConjHomeomorph_apply, mul_assoc] using
    (conjugateParabolic_mem_iff χ g (g⁻¹ * x * g))

/-- The literal dynamic centralizers satisfy the required inverse-image
conjugation relation. -/
theorem levi_mem_conjugation (x : RationalPoint F G.X) :
    x ∈ levi (χ ≫ (G.innerIso g).hom) ↔ g⁻¹ * x * g ∈ levi χ := by
  simpa [rationalPointsConjHomeomorph_apply, mul_assoc] using
    (conjugateLevi_mem_iff χ g (g⁻¹ * x * g))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Functoriality of the actual contracted radical gives its conjugation
relation, without supplying a new subgroup comparison. -/
theorem radical_mem_conjugation (x : RationalPoint F G.X) :
    x ∈ radical (χ ≫ (G.innerIso g).hom) ↔ g⁻¹ * x * g ∈ radical χ := by
  have hc := (Dynamic.mem_unipotent_conj χ g
    (x := g⁻¹ * x * g)).symm
  simpa [radical, BruhatTits.DynamicUnipotentContainment.unipotentPoints,
    constantPoint_self, mul_assoc] using hc

/-- The generic inverse conjugation is the inverse of the already published
actual Levi conjugation. -/
theorem conjugationEquiv_eq :
    conjugationEquiv g (levi_mem_conjugation χ g) = (leviConjugation χ g).symm := by
  ext m
  rfl

/-- The generic construction uses exactly the published conjugate
representation, on the same carrier. -/
theorem conjugationFunctor_obj_eq (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :
    (conjugationFunctor g (levi_mem_conjugation χ g)).obj A =
      conjugateRepresentation χ g A := by
  change SmoothRep.pullback _ A = SmoothRep.pullback _ A
  rw [conjugationEquiv_eq]

variable (hG : IsConnectedReductive G) (A : SmoothRep.{0, u, uV} ℂ (levi χ))

/-- Actual rational-point left translation with the canonical Levi
conjugation and with radical unimodularity discharged. -/
def leftTranslation :
    ((DynamicNormalization.leviTwistedInductionFunctor
      (decomposition χ) (radical_isClosed χ)).obj A).representation.Equiv
      ((DynamicNormalization.leviTwistedInductionFunctor
        (decomposition (χ ≫ (G.innerIso g).hom))
        (radical_isClosed (χ ≫ (G.innerIso g).hom))).obj
          (conjugateRepresentation χ g A)).representation :=
  CoefficientConjugation.leviLeftTranslation (decomposition χ)
    (decomposition (χ ≫ (G.innerIso g).hom)) g
    (parabolic_mem_conjugation χ g) (levi_mem_conjugation χ g)
    (radical_mem_conjugation χ g) (radical_isClosed χ)
    (radical_isClosed (χ ≫ (G.innerIso g).hom))
    (radical_unimodular χ hG) (radical_unimodular (χ ≫ (G.innerIso g).hom) hG) A

/-- The actual rational-point dual translation uses the actual smooth
contragredient of the published conjugate object. -/
def dualLeftTranslation :
    ((DynamicNormalization.leviTwistedInductionFunctor
      (decomposition χ) (radical_isClosed χ)).obj A.contragredient).representation.Equiv
      ((DynamicNormalization.leviTwistedInductionFunctor
        (decomposition (χ ≫ (G.innerIso g).hom))
        (radical_isClosed (χ ≫ (G.innerIso g).hom))).obj
          (conjugateRepresentation χ g A).contragredient).representation :=
  CoefficientConjugation.leviDualLeftTranslation (decomposition χ)
    (decomposition (χ ≫ (G.innerIso g).hom)) g
    (parabolic_mem_conjugation χ g) (levi_mem_conjugation χ g)
    (radical_mem_conjugation χ g) (radical_isClosed χ)
    (radical_isClosed (χ ≫ (G.innerIso g).hom))
    (radical_unimodular χ hG) (radical_unimodular (χ ≫ (G.innerIso g).hom) hG) A

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ x : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K,
      x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

include K hK hPK in
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The supplied compact representatives make the actual source quotient compact. -/
theorem sourceQuotientCompact :
    CompactSpace (Induction.LeftQuotient (parabolic χ)) := by
  apply Induction.compactSpace_leftQuotient_of_compact_representatives (parabolic χ) hK
  intro x
  obtain ⟨p, k, hx⟩ := hPK x
  exact ⟨p, p.property, k, k.property, hx⟩

include K hK hPK in
/-- Actual conjugation supplies compact representatives for the target quotient. -/
theorem targetQuotientCompact :
    CompactSpace (Induction.LeftQuotient (parabolic (χ ≫ (G.innerIso g).hom))) := by
  apply Induction.compactSpace_leftQuotient_of_compact_representatives
    (parabolic (χ ≫ (G.innerIso g).hom))
    (RationalDynamicSource.conjugateCompact_isCompact g K hK)
  intro x
  obtain ⟨p, k, hx⟩ := conjugate_parabolic_mul_compact χ g K hPK x
  exact ⟨p, p.property, k, k.property, hx⟩

/-- The actual source-normalized coefficient comparison for a rational
conjugating point. Quotient compactness comes from the displayed compact
Iwasawa data and its actual conjugate. -/
def coefficientLeftTranslation :
    (leviProductInducedCoefficientObject (decomposition χ) (radical_isClosed χ)
      A).representation.Equiv
      (leviProductInducedCoefficientObject (decomposition (χ ≫ (G.innerIso g).hom))
        (radical_isClosed (χ ≫ (G.innerIso g).hom))
        (conjugateRepresentation χ g A)).representation := by
  letI := sourceQuotientCompact χ K hK hPK
  letI := targetQuotientCompact χ g K hK hPK
  exact CoefficientConjugation.leviCoefficientLeftTranslation (decomposition χ)
    (decomposition (χ ≫ (G.innerIso g).hom)) g
    (parabolic_mem_conjugation χ g) (levi_mem_conjugation χ g)
    (radical_mem_conjugation χ g) (radical_isClosed χ)
    (radical_isClosed (χ ≫ (G.innerIso g).hom))
    (radical_unimodular χ hG) (radical_unimodular (χ ≫ (G.innerIso g).hom) hG) A

/-- The specialized coefficient comparison still commutes with the full
external action. -/
theorem coefficientLeftTranslation_action (z : RationalPoint F G.X × RationalPoint F G.X)
    (v : leviProductInducedCoefficientObject (decomposition χ) (radical_isClosed χ) A) :
    coefficientLeftTranslation χ g hG A K hK hPK
        ((leviProductInducedCoefficientObject (decomposition χ)
          (radical_isClosed χ) A).representation z v) =
      (leviProductInducedCoefficientObject (decomposition (χ ≫ (G.innerIso g).hom))
        (radical_isClosed (χ ≫ (G.innerIso g).hom))
        (conjugateRepresentation χ g A)).representation z
        (coefficientLeftTranslation χ g hG A K hK hPK v) :=
  congrArg (fun T : leviProductInducedCoefficientObject (decomposition χ)
    (radical_isClosed χ) A →ₗ[ℂ]
    leviProductInducedCoefficientObject (decomposition (χ ≫ (G.innerIso g).hom))
      (radical_isClosed (χ ≫ (G.innerIso g).hom)) (conjugateRepresentation χ g A) => T v)
    ((coefficientLeftTranslation χ g hG A K hK hPK).isIntertwining' z)

end Langlands.Plancherel.DynamicCoefficientConjugation
