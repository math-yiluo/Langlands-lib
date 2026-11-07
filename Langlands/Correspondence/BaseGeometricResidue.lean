import Langlands.Correspondence.BaseNormResidue
import Langlands.Weil.Local.ExtensionWeil
import Langlands.ClassFieldTheory.Local.NYLL.SuppliedResidueProof

/-! # Geometric residue normalization of the actual base candidate -/

noncomputable section

universe uF uE

namespace Langlands.Correspondence.GeometricResidue

open LocalClassField LocalFactor LocalFactor.CommonClosure Weil.Local IsLocalRing

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance geometricResidueTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance geometricResidueValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance geometricResidueLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance geometricResidueCharZero : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier
local instance geometricResidueNormedField : NontriviallyNormedField F.Carrier :=
  LocalGalois.localNormedField F.Carrier
local instance geometricResidueUltrametric : IsUltrametricDist F.Carrier :=
  LocalGalois.localNormedField_ultrametric F.Carrier
local instance geometricResidueComplete : CompleteSpace F.Carrier :=
  LocalGalois.localNormedField_complete F.Carrier

/-- The spectral integer ring used by the absolute residue construction is
the supplied integer ring on every actual finite extension. -/
theorem finiteSpectralIntegers_eq (E : PadicField.{uE} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] (S : E.TopologicalData) :
    (LocalGalois.extensionIntegers F.Carrier E.Carrier).toSubring = S.Integers := by
  let TF := F.canonicalTopologicalData
  let := Algebra.compHom E.Carrier
    (algebraMap (ValuativeRel.valuation (Padic p)).integer (Padic p))
  let := TF.integerAlgebra
  let := TF.integers_finite
  let : Algebra TF.Integers E.Carrier :=
    ((algebraMap F.Carrier E.Carrier).comp TF.Integers.subtype).toAlgebra
  let : IsScalarTower (ValuativeRel.valuation (Padic p)).integer TF.Integers E.Carrier :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap (Padic p) E.Carrier a.val =
        algebraMap F.Carrier E.Carrier (algebraMap (Padic p) F.Carrier a.val)
      exact IsScalarTower.algebraMap_apply (Padic p) F.Carrier E.Carrier a.val
  let b : LocalGalois.baseIntegers F.Carrier ≃+* TF.Integers :=
    RingEquiv.subringCongr (LocalGalois.localNormedField_integer F.Carrier)
  ext x
  change x ∈ LocalGalois.extensionIntegers F.Carrier E.Carrier ↔ x ∈ S.Integers
  rw [← LocalGalois.integral_iff_mem_spectralIntegers F.Carrier E.Carrier x]
  rw [b.isIntegral_iff (by ext a; rfl) x]
  rw [← S.isIntegral_iff_mem_integers]
  exact ⟨fun hx => isIntegral_trans (R := (ValuativeRel.valuation (Padic p)).integer) x hx,
    fun hx => hx.tower_top⟩

/-- The identity comparison of spectral and supplied integer rings. -/
def finiteSpectralIntegerEquiv (E : PadicField.{uE} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] (S : E.TopologicalData) :
    LocalGalois.extensionIntegers F.Carrier E.Carrier ≃+* S.Integers :=
  RingEquiv.subringCongr (finiteSpectralIntegers_eq F E S)

/-- Geometric absolute residue action restricts to the inverse cardinality
power action on every actual finite abelian residue extension. -/
theorem finiteResidue_inverse_power (L : LocalFiniteAbelianExtension F)
    (σ : Field.absoluteGaloisGroup F.Carrier)
    (hσ : localResidueMap F σ =
      Galois.FiniteField.geometricFrobenius (localResidueField F))
    (y : ResidueField (LocalGalois.extensionIntegers F.Carrier L.field)) :
    LocalGalois.residueHom F.Carrier L.field ((L.restriction σ)⁻¹) y =
      y ^ F.canonicalTopologicalData.residueCardinality := by
  let j : ResidueField (LocalGalois.extensionIntegers F.Carrier L.field) →+*
      AlgebraicClosure (localResidueField F) :=
    (LocalGalois.localResidueClosureEquiv F.Carrier).toRingHom.comp
      (LocalGalois.residueInclusion F.Carrier (AlgebraicClosure F.Carrier)
        L.field.toIntermediateField)
  have hn : j (LocalGalois.residueHom F.Carrier L.field ((L.restriction σ)⁻¹) y) =
      AlgEquiv.toAlgHom (localResidueMap F σ⁻¹) (j y) := by
    have h := (LocalGalois.absoluteResidueHom_restrict
      F.Carrier L.field.toIntermediateField σ⁻¹ y).symm
    have hτ : (σ⁻¹).restrictNormal L.field.toIntermediateField = (L.restriction σ)⁻¹ := by
      rw [← map_inv L.restriction]
      rfl
    rw [hτ] at h
    exact h
  apply j.injective
  rw [hn, map_pow, map_inv, hσ]
  rw [show (Galois.FiniteField.geometricFrobenius (localResidueField F))⁻¹ =
    Galois.FiniteField.arithmeticFrobenius (localResidueField F) from inv_inv _]
  simp [Galois.FiniteField.arithmeticFrobenius, Galois.FiniteField.arithmetic,
    ← Nat.card_eq_fintype_card, ← localResidueCardinality_eq F]

/-- Convert the discrete bound into membership in the supplied integer ring. -/
theorem mem_integers_of_discreteValuation_le_one (E : PadicField.{uE} p)
    (S : E.TopologicalData) (x : E.Carrier) (hx : S.discreteValuation x ≤ 1) :
    x ∈ S.Integers := by
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  let i := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E.Carrier
  change i (ValuativeRel.valuation E.Carrier x) ≤ 1 at hx
  rw [← map_one i] at hx
  exact i.strictMono.le_iff_le.mp hx

set_option backward.isDefEq.respectTransparency false in
/-- The same geometric action is the exact congruence for every supplied
topological datum on the finite extension. -/
theorem finite_inverse_power_congruence (L : LocalFiniteAbelianExtension F)
    (S : (L.asPadicField (p := p)).TopologicalData)
    (σ : Field.absoluteGaloisGroup F.Carrier)
    (hσ : localResidueMap F σ =
      Galois.FiniteField.geometricFrobenius (localResidueField F))
    (x : L.field) (hx : S.discreteValuation x ≤ 1) :
    S.discreteValuation
      ((L.restriction σ).symm x - x ^ F.canonicalTopologicalData.residueCardinality) < 1 := by
  let : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (Algebra F.Carrier L.field)
  let : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
  let : FiniteDimensional F.Carrier (L.asPadicField (p := p)).Carrier :=
    inferInstanceAs (FiniteDimensional F.Carrier L.field)
  let e := finiteSpectralIntegerEquiv F (L.asPadicField (p := p)) S
  let xS : S.Integers :=
    ⟨x, mem_integers_of_discreteValuation_le_one (L.asPadicField (p := p)) S x hx⟩
  let xR := e.symm xS
  have hr := congrArg (ResidueField.mapEquiv e)
    (finiteResidue_inverse_power F L σ hσ (residue _ xR))
  simp only [map_pow] at hr
  change S.residue
      (e (LocalGalois.integerAut F.Carrier L.field ((L.restriction σ)⁻¹) xR)) =
    S.residue (e xR) ^ F.canonicalTopologicalData.residueCardinality at hr
  rw [← map_pow] at hr
  exact (NYLL.suppliedResidueCongruence (L.asPadicField (p := p)) S _ _).mp hr

/-- The geometric order condition on an actual local Weil candidate already
forces the finite geometric residue-action clause. -/
theorem finite_congruence_of_geometricOrder (e : ReciprocityCandidate F)
    (he : GeometricOrderRelation F.canonicalTopologicalData (localResidueDegree F) e)
    (L : LocalFiniteAbelianExtension F)
    (S : (L.asPadicField (p := p)).TopologicalData)
    (a : F.Carrierˣ) (ha : F.canonicalTopologicalData.ord (a : F.Carrier) = 1)
    (x : L.field) (hx : S.discreteValuation x ≤ 1) :
    S.discreteValuation
      ((finiteFamilyOfHom
          (candidateGaloisHom F.canonicalTopologicalData (localResidueDegree F) e) L a).symm x -
        x ^ F.canonicalTopologicalData.residueCardinality) < 1 := by
  obtain ⟨b, rfl⟩ := e.surjective a
  induction b using QuotientGroup.induction_on with
  | H w =>
    have h := congrArg Multiplicative.toAdd
      (DFunLike.congr_fun he (QuotientGroup.mk w))
    change F.canonicalTopologicalData.ord
        (reciprocityHom F e w : F.Carrier) = localDegreeInt F w at h
    have hw : localDegreeInt F w = 1 := h.symm.trans ha
    have hσ : localResidueMap F (localProjection F w) =
        Galois.FiniteField.geometricFrobenius (localResidueField F) := by
      rw [localResidueMap_projection, hw, zpow_one]
    change S.discreteValuation
      ((finiteFamilyOfHom
          (candidateGaloisHom F.canonicalTopologicalData (localResidueDegree F) e) L
          (reciprocityHom F e w)).symm x -
        x ^ F.canonicalTopologicalData.residueCardinality) < 1
    rw [finiteRestriction_reciprocityHom]
    exact finite_inverse_power_congruence F L S (localProjection F w) hσ x hx

end Langlands.Correspondence.GeometricResidue

namespace Langlands.Correspondence

open LocalClassField LocalFactor LocalFactor.CommonClosure Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance baseGeometricResidueTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- On the actual assembled local Weil group the local candidate relation
also gives the full geometric residue normalization. -/
theorem isGeometricReciprocity_of_localCandidate (e : ReciprocityCandidate F)
    (he : LocalReciprocityCandidateRelation
      F.canonicalTopologicalData (localResidueDegree F) e) :
    IsGeometricReciprocity F e :=
  ⟨he.1, he.2, GeometricResidue.finite_congruence_of_geometricOrder F e he.1⟩

/-- The two original relations agree for the actual geometric degree map. -/
theorem isGeometricReciprocity_iff_localCandidate (e : ReciprocityCandidate F) :
    IsGeometricReciprocity F e ↔
      LocalReciprocityCandidateRelation F.canonicalTopologicalData (localResidueDegree F) e :=
  ⟨fun h => ⟨h.1, h.2.1⟩, isGeometricReciprocity_of_localCandidate F e⟩

/-- A supplied normalized common-closure family has a fully geometric base candidate. -/
def BaseGeometricReciprocityStatement : Prop :=
  ∀ (eC : ReciprocityFamily F), NormalizedReciprocity F eC →
    IsGeometricReciprocity F (baseReciprocityCandidate F eC)

theorem baseGeometricReciprocityProof : BaseGeometricReciprocityStatement F := by
  intro eC he
  exact isGeometricReciprocity_of_localCandidate F _
    (localReciprocity_baseReciprocityCandidate F eC he)

/-- Full geometric reciprocity holds for any candidate compatible with that family. -/
theorem isGeometricReciprocity_of_isBaseReciprocity
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (h : IsBaseReciprocity F e eC) (he : NormalizedReciprocity F eC) :
    IsGeometricReciprocity F e :=
  isGeometricReciprocity_of_localCandidate F e
    (localReciprocity_of_isBaseReciprocity F e eC h he)

end Langlands.Correspondence
