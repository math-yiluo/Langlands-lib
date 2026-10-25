import Langlands.ClassFieldTheory.Local.NYLL.FiniteInertiaField
import Mathlib.RingTheory.RamificationInertia.Ramification

/-! # Targets for the finite ramified residue bridge -/

namespace Langlands.LocalClassField.NYLL

universe u v

/-- The actual finite inertia fixed field is relatively unramified for every
supplied realization of its integer ring. -/
def FiniteInertiaFieldUnramifiedStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [IsAbelianGalois F.Carrier E.Carrier] (TF : F.TopologicalData)
    (TU : (finiteInertiaPadicField F E TF).TopologicalData),
    letI := PadicField.TopologicalData.relativeIntegerAlgebra TF TU
    (IsLocalRing.maximalIdeal TU.Integers).ramificationIdx TF.Integers = 1

/-- The actual inclusion of the inertia fixed field induces an isomorphism on
the supplied residue fields, expressed as bijectivity of that specific map. -/
def FiniteInertiaResidueMapBijectiveStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [IsAbelianGalois F.Carrier E.Carrier] (TF : F.TopologicalData)
    (TU : (finiteInertiaPadicField F E TF).TopologicalData) (TE : E.TopologicalData),
    Function.Bijective (finiteInertiaResidueMap F E TF TU TE)

/-- Restriction to the actual inertia fixed field commutes with its supplied
residue inclusion and the supplied actions. -/
def FiniteInertiaResidueRestrictionStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [IsAbelianGalois F.Carrier E.Carrier] (TF : F.TopologicalData)
    (TU : (finiteInertiaPadicField F E TF).TopologicalData) (TE : E.TopologicalData)
    (σ : Gal(E.Carrier/F.Carrier)) (y : TU.ResidueField),
    finiteInertiaResidueMap F E TF TU TE
        (finiteInertiaResidueAction F E TF TU (finiteInertiaRestriction F E TF σ) y) =
      Ramification.Padic.residueHom TE F.Carrier σ
        (finiteInertiaResidueMap F E TF TU TE y)

/-- Inverse power action on the actual supplied residue field is equivalent to
the corresponding discrete-valuation congruence on every integral element. -/
def SuppliedInverseResiduePowerStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (TE : E.TopologicalData) (σ : Gal(E.Carrier/F.Carrier)) (q : ℕ),
    (∀ y : TE.ResidueField, (Ramification.Padic.residueHom TE F.Carrier σ)⁻¹ y = y ^ q) ↔
      ∀ x : E.Carrier, TE.discreteValuation x ≤ 1 →
        TE.discreteValuation (σ.symm x - x ^ q) < 1

/-- Unramified normalization and actual restriction for one and the same Artin
family imply the exact supplied-data geometric residue formula at every finite
abelian level, including ramified levels. -/
def RamifiedGeometricNormalizationTransferStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [IsAbelianGalois F.Carrier E.Carrier] (TF : F.TopologicalData)
    (TU : (finiteInertiaPadicField F E TF).TopologicalData) (TE : E.TopologicalData)
    (Artin : ∀ (D : PadicField.{v} p) [Algebra F.Carrier D.Carrier]
      [IsScalarTower (Padic p) F.Carrier D.Carrier]
      [IsAbelianGalois F.Carrier D.Carrier],
      D.TopologicalData → (F.Carrierˣ →* Gal(D.Carrier/F.Carrier))),
    letI := finiteInertiaField_isAbelianGalois F E TF
    (∀ (D : PadicField.{v} p) [Algebra F.Carrier D.Carrier]
      [IsScalarTower (Padic p) F.Carrier D.Carrier]
      [IsAbelianGalois F.Carrier D.Carrier] (TD : D.TopologicalData),
      (letI := PadicField.TopologicalData.relativeIntegerAlgebra TF TD
       (IsLocalRing.maximalIdeal TD.Integers).ramificationIdx TF.Integers = 1) →
      ∀ (a : F.Carrierˣ), TF.ord (a : F.Carrier) = 1 →
        ∀ x : D.Carrier, TD.discreteValuation x ≤ 1 →
          TD.discreteValuation ((Artin D TD a).symm x - x ^ TF.residueCardinality) < 1) →
    ((finiteInertiaRestriction F E TF).comp (Artin E TE) =
      Artin (finiteInertiaPadicField F E TF) TU) →
    ∀ (a : F.Carrierˣ), TF.ord (a : F.Carrier) = 1 →
      ∀ x : E.Carrier, TE.discreteValuation x ≤ 1 →
        TE.discreteValuation ((Artin E TE a).symm x - x ^ TF.residueCardinality) < 1

end Langlands.LocalClassField.NYLL
