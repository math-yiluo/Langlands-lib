import Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureProof
import Langlands.Galois.Local.AbsoluteDefinitions

/-! # Comparison of supplied and spectral integer rings -/

noncomputable section

namespace Langlands.LocalClassField.NYLL

open IsLocalRing

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData)

local instance suppliedSpectralComparisonProofInstance1 : FiniteDimensional F.Carrier E.Carrier :=
  FiniteDimensional.right (Padic p) F.Carrier E.Carrier
/-- The spectral base valuation ring for the norm constructed from `T`. -/
abbrev suppliedBaseSpectralIntegers : ValuationSubring F.Carrier := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := LocalGalois.localNormedField F.Carrier
  letI := LocalGalois.localNormedField_ultrametric F.Carrier
  exact LocalGalois.baseIntegers F.Carrier

/-- The spectral extension valuation ring for the norm constructed from `T`. -/
abbrev suppliedExtensionSpectralIntegers : ValuationSubring E.Carrier := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := LocalGalois.localNormedField F.Carrier
  letI := LocalGalois.localNormedField_ultrametric F.Carrier
  letI := LocalGalois.localNormedField_complete F.Carrier
  exact LocalGalois.extensionIntegers F.Carrier E.Carrier

/-- The norm constructed from a supplied base realization has its actual integer subring. -/
theorem suppliedSpectralBaseIntegers_eq :
    (suppliedBaseSpectralIntegers F T).toSubring = T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact LocalGalois.localNormedField_integer F.Carrier

/-- Identity on field elements identifies the spectral and supplied base integers. -/
def suppliedSpectralBaseIntegerEquiv :
    suppliedBaseSpectralIntegers F T ≃+* T.Integers :=
  RingEquiv.subringCongr (suppliedSpectralBaseIntegers_eq F T)

/-- Spectral and supplied extension integers are the same actual subring. -/
theorem suppliedSpectralIntegers_eq :
    (suppliedExtensionSpectralIntegers F E T).toSubring = S.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := LocalGalois.localNormedField F.Carrier
  let := LocalGalois.localNormedField_ultrametric F.Carrier
  let := LocalGalois.localNormedField_complete F.Carrier
  let := PadicField.TopologicalData.relativeIntegerAlgebra T S
  let := PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := E) T
  let := (relativeIntegerStructure p F E T S).1
  ext x
  change x ∈ LocalGalois.extensionIntegers F.Carrier E.Carrier ↔ x ∈ S.Integers
  rw [← LocalGalois.integral_iff_mem_spectralIntegers F.Carrier E.Carrier]
  rw [(suppliedSpectralBaseIntegerEquiv F T).isIntegral_iff (by ext; rfl) x]
  rw [IsIntegralClosure.isIntegral_iff (A := S.Integers)]
  exact ⟨by rintro ⟨y, rfl⟩; exact y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

/-- Identity on extension-field elements identifies its spectral and supplied integers. -/
def suppliedSpectralIntegerEquiv :
    suppliedExtensionSpectralIntegers F E T ≃+* S.Integers :=
  RingEquiv.subringCongr (suppliedSpectralIntegers_eq F E T S)

@[simp] theorem suppliedSpectralIntegerEquiv_coe
    (x : suppliedExtensionSpectralIntegers F E T) :
    (suppliedSpectralIntegerEquiv F E T S x : E.Carrier) = x := rfl

/-- The induced isomorphism of the actual residue quotients at the base. -/
def suppliedSpectralBaseResidueEquiv :
    ResidueField (suppliedBaseSpectralIntegers F T) ≃+* T.ResidueField :=
  ResidueField.mapEquiv (suppliedSpectralBaseIntegerEquiv F T)

/-- The induced isomorphism of the actual residue quotients at the extension. -/
def suppliedSpectralResidueEquiv :
    ResidueField (suppliedExtensionSpectralIntegers F E T) ≃+* S.ResidueField :=
  ResidueField.mapEquiv (suppliedSpectralIntegerEquiv F E T S)

@[simp] theorem suppliedSpectralBaseResidueEquiv_residue
    (x : suppliedBaseSpectralIntegers F T) :
    suppliedSpectralBaseResidueEquiv F T (residue _ x) =
      T.residue (suppliedSpectralBaseIntegerEquiv F T x) := rfl

@[simp] theorem suppliedSpectralResidueEquiv_residue
    (x : suppliedExtensionSpectralIntegers F E T) :
    suppliedSpectralResidueEquiv F E T S (residue _ x) =
      S.residue (suppliedSpectralIntegerEquiv F E T S x) := rfl

/-- The residue comparison commutes with the actual map from the base. -/
theorem suppliedSpectralResidueEquiv_base
    (x : ResidueField (suppliedBaseSpectralIntegers F T)) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := LocalGalois.localNormedField F.Carrier
    letI := LocalGalois.localNormedField_ultrametric F.Carrier
    letI := LocalGalois.localNormedField_complete F.Carrier
    suppliedSpectralResidueEquiv F E T S
        (algebraMap (ResidueField (LocalGalois.baseIntegers F.Carrier))
          (ResidueField (LocalGalois.extensionIntegers F.Carrier E.Carrier)) x) =
      PadicField.TopologicalData.relativeResidueMap T S
        (suppliedSpectralBaseResidueEquiv F T x) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := LocalGalois.localNormedField F.Carrier
  let := LocalGalois.localNormedField_ultrametric F.Carrier
  let := LocalGalois.localNormedField_complete F.Carrier
  obtain ⟨x, rfl⟩ := residue_surjective x
  change S.residue (suppliedSpectralIntegerEquiv F E T S (algebraMap _ _ x)) =
    S.residue (PadicField.TopologicalData.relativeIntegerMap T S
      (suppliedSpectralBaseIntegerEquiv F T x))
  congr 1

/-- Residue degrees agree for the spectral and supplied relative residue maps. -/
theorem suppliedSpectralResidue_finrank :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := LocalGalois.localNormedField F.Carrier
    letI := LocalGalois.localNormedField_ultrametric F.Carrier
    letI := LocalGalois.localNormedField_complete F.Carrier
    letI := PadicField.TopologicalData.relativeResidueAlgebra T S
    Module.finrank (ResidueField (LocalGalois.baseIntegers F.Carrier))
        (ResidueField (LocalGalois.extensionIntegers F.Carrier E.Carrier)) =
      Module.finrank T.ResidueField S.ResidueField := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := LocalGalois.localNormedField F.Carrier
  let := LocalGalois.localNormedField_ultrametric F.Carrier
  let := LocalGalois.localNormedField_complete F.Carrier
  let := PadicField.TopologicalData.relativeResidueAlgebra T S
  apply Algebra.finrank_eq_of_equiv_equiv (suppliedSpectralBaseResidueEquiv F T)
    (suppliedSpectralResidueEquiv F E T S)
  ext x
  exact (suppliedSpectralResidueEquiv_base F E T S x).symm

end Langlands.LocalClassField.NYLL
