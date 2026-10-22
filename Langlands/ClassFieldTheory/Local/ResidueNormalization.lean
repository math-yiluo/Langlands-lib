import Langlands.Galois.Local.SpectralProof
import Langlands.Galois.FiniteField.Frobenius
import Langlands.LocalField.CanonicalProof
import Langlands.ClassFieldTheory.Local.Units

/-!
# Geometric normalization in the actual residue quotient

Geometric Frobenius is defined as a class modulo actual inertia, through the
proved residue quotient equivalence. The normalization predicate concerns a
supplied homomorphism; it does not construct a reciprocity homomorphism.
-/

noncomputable section

open IsLocalRing
open scoped NNReal

namespace Langlands.LocalClassField.ResidueNormalization

universe u v

variable (K : Type u) (L : Type v) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [IsGalois K L]
    [Finite (ResidueField (LocalGalois.baseIntegers K))]

/-- The canonical geometric Frobenius class modulo the actual inertia subgroup.
No representative in the generally nonabelian Galois group is chosen. -/
def geometricFrobeniusClass : Gal(L/K) ⧸ LocalGalois.inertia K L :=
  (LocalGalois.residueQuotientEquiv K L).symm
    (Galois.FiniteField.geometric (ResidueField (LocalGalois.baseIntegers K))
      (ResidueField (LocalGalois.extensionIntegers K L)))

@[simp]
theorem geometricFrobeniusClass_residue :
    LocalGalois.residueQuotientEquiv K L (geometricFrobeniusClass K L) =
      Galois.FiniteField.geometric (ResidueField (LocalGalois.baseIntegers K))
        (ResidueField (LocalGalois.extensionIntegers K L)) :=
  (LocalGalois.residueQuotientEquiv K L).apply_symm_apply _

/-- A Galois automorphism has geometric residue action precisely when its
class is the canonical geometric Frobenius class. -/
def HasGeometricResidueAction (σ : Gal(L/K)) : Prop :=
  LocalGalois.residueHom K L σ =
    Galois.FiniteField.geometric (ResidueField (LocalGalois.baseIntegers K))
      (ResidueField (LocalGalois.extensionIntegers K L))

theorem mk_eq_geometricFrobeniusClass_iff (σ : Gal(L/K)) :
    QuotientGroup.mk' (LocalGalois.inertia K L) σ = geometricFrobeniusClass K L ↔
      HasGeometricResidueAction K L σ := by
  rw [← (LocalGalois.residueQuotientEquiv K L).injective.eq_iff,
    geometricFrobeniusClass_residue]
  rfl

omit [IsGalois K L] in
/-- The inverse-action convention: geometric residue action means that the
inverse automorphism acts by the residue-cardinality power. -/
theorem hasGeometricResidueAction_iff_inverse_power (σ : Gal(L/K)) :
    HasGeometricResidueAction K L σ ↔
      ∀ x : ResidueField (LocalGalois.extensionIntegers K L),
        (LocalGalois.residueHom K L σ)⁻¹ x =
          x ^ Nat.card (ResidueField (LocalGalois.baseIntegers K)) := by
  let := Fintype.ofFinite (ResidueField (LocalGalois.baseIntegers K))
  change LocalGalois.residueHom K L σ =
    (Galois.FiniteField.arithmetic _ _)⁻¹ ↔ _
  constructor
  · intro h x
    rw [h, inv_inv]
    simp [Galois.FiniteField.arithmetic, ← Nat.card_eq_fintype_card]
  · intro h
    apply inv_injective
    rw [inv_inv]
    ext x
    simpa [Galois.FiniteField.arithmetic, ← Nat.card_eq_fintype_card] using h x

/-- Geometric normalization at a finite or algebraic Galois level: the residue
class of the proposed Artin image is geometric Frobenius to the valuation.
The valuation and Artin homomorphism are explicit arguments. -/
def GeometricNormalization (ord : Kˣ →* Multiplicative ℤ)
    (r : Kˣ →* Gal(L/K)) : Prop :=
  ∀ a, QuotientGroup.mk' (LocalGalois.inertia K L) (r a) =
    geometricFrobeniusClass K L ^ Multiplicative.toAdd (ord a)

theorem geometricNormalization_iff_residue (ord : Kˣ →* Multiplicative ℤ)
    (r : Kˣ →* Gal(L/K)) :
    GeometricNormalization K L ord r ↔
      ∀ a, LocalGalois.residueHom K L (r a) =
        Galois.FiniteField.geometric (ResidueField (LocalGalois.baseIntegers K))
          (ResidueField (LocalGalois.extensionIntegers K L)) ^
            Multiplicative.toAdd (ord a) := by
  unfold GeometricNormalization
  apply forall_congr'
  intro a
  rw [← (LocalGalois.residueQuotientEquiv K L).injective.eq_iff,
    map_zpow, geometricFrobeniusClass_residue]
  rfl

theorem normalized_uniformizer (ord : Kˣ →* Multiplicative ℤ)
    (r : Kˣ →* Gal(L/K)) (h : GeometricNormalization K L ord r)
    (a : Kˣ) (ha : Multiplicative.toAdd (ord a) = 1) :
    HasGeometricResidueAction K L (r a) := by
  apply (mk_eq_geometricFrobeniusClass_iff K L (r a)).mp
  simpa [ha] using h a

theorem normalized_unit (ord : Kˣ →* Multiplicative ℤ)
    (r : Kˣ →* Gal(L/K)) (h : GeometricNormalization K L ord r)
    (a : Kˣ) (ha : Multiplicative.toAdd (ord a) = 0) :
    r a ∈ LocalGalois.inertia K L := by
  have hq : QuotientGroup.mk' (LocalGalois.inertia K L) (r a) = 1 := by
    simpa [ha] using h a
  exact (QuotientGroup.eq_one_iff _).mp hq

end Langlands.LocalClassField.ResidueNormalization

namespace Langlands.LocalClassField.ResidueNormalization.Canonical

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField

local instance : IsUltrametricDist F.Carrier :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))

local instance : CompleteSpace F.Carrier := F.canonical_complete_proper.1

/-- Finiteness for the residue field of the actual canonical norm valuation.
The integer rings are compared explicitly before transporting finiteness. -/
theorem residueField_finite :
    Finite (IsLocalRing.ResidueField (LocalGalois.baseIntegers F.Carrier)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : F.canonicalValuation.Compatible := Valuation.Compatible.ofValuation _
  have he : (NormedField.valuation (K := F.Carrier)).integer =
      (ValuativeRel.valuation F.Carrier).integer := by
    ext x
    change F.canonicalValuation x ≤ 1 ↔ ValuativeRel.valuation F.Carrier x ≤ 1
    rw [← F.canonicalValuation.vle_one_iff,
      ← (ValuativeRel.valuation F.Carrier).vle_one_iff]
  exact Finite.of_equiv (IsLocalRing.ResidueField
    (ValuativeRel.valuation F.Carrier).integer)
      (IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr he)).symm.toEquiv

attribute [local instance] residueField_finite

variable (L : Type v) [Field L] [Algebra F.Carrier L]
    [Algebra.IsAlgebraic F.Carrier L] [IsGalois F.Carrier L]

/-- Geometric Frobenius modulo actual inertia over any finite extension of
`Q_p`, using its constructed canonical norm and residue finiteness. -/
def geometricFrobeniusClass :
    Gal(L/F.Carrier) ⧸ LocalGalois.inertia F.Carrier L :=
  ResidueNormalization.geometricFrobeniusClass F.Carrier L

/-- The geometric normalization predicate over an actual finite extension of
`Q_p`, using its constructed integer-valued normalized order. -/
def GeometricNormalization (r : F.Carrierˣ →* Gal(L/F.Carrier)) : Prop :=
  ResidueNormalization.GeometricNormalization F.Carrier L
    F.canonicalTopologicalData.orderHom r

end Langlands.LocalClassField.ResidueNormalization.Canonical
