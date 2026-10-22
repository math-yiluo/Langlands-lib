import Langlands.ClassFieldTheory.Local.UnramifiedArithmeticStatement
import Langlands.LocalField.Normalization.Proof
import Langlands.Galois.Local.SpectralProof
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

noncomputable section

namespace Langlands.ClassFieldTheory.Local

open IsLocalRing

universe u v

namespace ArithmeticCoordinate

variable {p : ℕ} [Fact p.Prime]
variable (F : PadicField.{u} p) (E : PadicField.{v} p)

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance : NormedAlgebra (Padic p) F.Carrier := F.canonicalNormedAlgebra
local instance : IsUltrametricDist F.Carrier :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
local instance : ProperSpace F.Carrier := FiniteDimensional.proper (Padic p) F.Carrier

/-- Identity comparison between the norm integer ring and the canonical integer ring. -/
def baseIntegerEquiv : LocalGalois.baseIntegers F.Carrier ≃+*
    F.canonicalTopologicalData.Integers :=
  RingEquiv.subringCongr (by
    ext x
    exact F.canonicalTopologicalData.canonicalNorm_le_one_iff_mem_integers x)

/-- Comparison of the actual base residue fields. -/
def baseResidueEquiv : ResidueField (LocalGalois.baseIntegers F.Carrier) ≃+*
    F.canonicalTopologicalData.ResidueField :=
  ResidueField.mapEquiv (baseIntegerEquiv F)

variable [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]

/-- Uniqueness of the extended norm compares the two spectral constructions. -/
theorem spectralNorm_eq_canonicalNorm (x : E.Carrier) :
    spectralNorm F.Carrier E.Carrier x = E.canonicalNorm x := by
  let := E.canonicalNormedField
  let : NormedAlgebra F.Carrier E.Carrier :=
    spectralNorm.normedAlgebra' (Padic p) F.Carrier E.Carrier
  exact (NormedAlgebra.norm_eq_spectralNorm F.Carrier x).symm

/-- Identity comparison for extension integer rings. -/
def extensionIntegerEquiv : LocalGalois.extensionIntegers F.Carrier E.Carrier ≃+*
    E.canonicalTopologicalData.Integers :=
  RingEquiv.subringCongr (by
    ext x
    change spectralNorm F.Carrier E.Carrier x ≤ 1 ↔ _
    rw [spectralNorm_eq_canonicalNorm]
    exact E.canonicalTopologicalData.canonicalNorm_le_one_iff_mem_integers x)

/-- Comparison of the actual extension residue fields. -/
def extensionResidueEquiv :
    ResidueField (LocalGalois.extensionIntegers F.Carrier E.Carrier) ≃+*
      E.canonicalTopologicalData.ResidueField :=
  ResidueField.mapEquiv (extensionIntegerEquiv F E)

local instance baseResidueFinite : Finite (ResidueField (LocalGalois.baseIntegers F.Carrier)) :=
  letI := F.canonicalTopologicalData.finite_residueField
  Finite.of_equiv F.canonicalTopologicalData.ResidueField (baseResidueEquiv F).symm.toEquiv

local instance extensionResidueFinite :
    Finite (ResidueField (LocalGalois.extensionIntegers F.Carrier E.Carrier)) :=
  letI := E.canonicalTopologicalData.finite_residueField
  Finite.of_equiv E.canonicalTopologicalData.ResidueField
    (extensionResidueEquiv F E).symm.toEquiv

/-- Equal absolute ramification indices force the full field degree into the
actual residue extension. -/
theorem residue_finrank
    (he : F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex) :
    Module.finrank (ResidueField (LocalGalois.baseIntegers F.Carrier))
      (ResidueField (LocalGalois.extensionIntegers F.Carrier E.Carrier)) =
      Module.finrank F.Carrier E.Carrier := by
  have hdeg : E.canonicalTopologicalData.residueDegree =
      F.canonicalTopologicalData.residueDegree * Module.finrank F.Carrier E.Carrier := by
    apply Nat.eq_of_mul_eq_mul_left F.canonicalTopologicalData.ramificationIndex_pos
    rw [he, E.canonicalTopologicalData.ramificationIndex_mul_residueDegree,
      ← he, ← mul_assoc, F.canonicalTopologicalData.ramificationIndex_mul_residueDegree,
      Module.finrank_mul_finrank]
  have hcard : Nat.card (ResidueField (LocalGalois.extensionIntegers F.Carrier E.Carrier)) =
      Nat.card (ResidueField (LocalGalois.baseIntegers F.Carrier)) ^
        Module.finrank F.Carrier E.Carrier := by
    rw [Nat.card_congr (extensionResidueEquiv F E).toEquiv,
      Nat.card_congr (baseResidueEquiv F).toEquiv]
    change E.canonicalTopologicalData.residueCardinality =
      F.canonicalTopologicalData.residueCardinality ^ _
    rw [E.canonicalTopologicalData.residueCardinality_eq_pow,
      F.canonicalTopologicalData.residueCardinality_eq_pow, hdeg, pow_mul]
  apply Nat.pow_right_injective (show 1 <
    Nat.card (ResidueField (LocalGalois.baseIntegers F.Carrier)) from Finite.one_lt_card)
  dsimp only
  rw [← Module.natCard_eq_pow_finrank, hcard]

variable [IsGalois F.Carrier E.Carrier]

/-- The actual residue action is injective in the unramified case. -/
theorem residueHom_injective
    (he : F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex) :
    Function.Injective (LocalGalois.residueHom F.Carrier E.Carrier) := by
  apply ((LocalGalois.residueHom_surjective F.Carrier E.Carrier).bijective_of_nat_card_le ?_).1
  rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank, residue_finrank F E he]

/-- An arithmetic generator, transferred through the actual residue action,
provides the cyclic coordinate of the field Galois group. -/
theorem coordinate_exists
    (he : F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex) :
    letI : NeZero (Module.finrank F.Carrier E.Carrier) := ⟨Module.finrank_pos.ne'⟩
    ∃ χ : Gal(E.Carrier/F.Carrier) ≃*
        Multiplicative (ZMod (Module.finrank F.Carrier E.Carrier)),
      IsArithmeticUnramifiedCoordinate F E.Carrier χ := by
  let := Fintype.ofFinite (ResidueField (LocalGalois.baseIntegers F.Carrier))
  let r := MulEquiv.ofBijective (LocalGalois.residueHom F.Carrier E.Carrier)
    ⟨residueHom_injective F E he, LocalGalois.residueHom_surjective F.Carrier E.Carrier⟩
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic
    (ResidueField (LocalGalois.baseIntegers F.Carrier))
    (ResidueField (LocalGalois.extensionIntegers F.Carrier E.Carrier))
  have hg : ∀ σ : Gal(E.Carrier/F.Carrier), σ ∈ Subgroup.zpowers (r.symm φ) := by
    intro σ
    obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
      (ResidueField (LocalGalois.baseIntegers F.Carrier))
      (ResidueField (LocalGalois.extensionIntegers F.Carrier E.Carrier))).surjective (r σ)
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨(i.val : ℤ), ?_⟩
    apply r.injective
    simpa only [map_zpow, map_pow, MulEquiv.apply_symm_apply, zpow_natCast] using hi
  let χ := (zmodMulEquivOfGenerator hg (IsGalois.card_aut_eq_finrank F.Carrier E.Carrier)).symm
  refine ⟨χ, residueHom_injective F E he, ?_⟩
  intro x
  change r (χ.symm (Multiplicative.ofAdd 1)) x = _
  dsimp only [χ, MulEquiv.symm_symm]
  rw [zmodMulEquivOfGenerator_apply_ofAdd_one, MulEquiv.apply_symm_apply]
  change x ^ Fintype.card (ResidueField (LocalGalois.baseIntegers F.Carrier)) = _
  rw [Fintype.card_eq_nat_card]

end ArithmeticCoordinate

/-- Arithmetic Frobenius coordinates for every finite unramified Galois
extension of p-adic fields, including degree one. -/
theorem arithmeticUnramifiedCoordinateExistence :
    ArithmeticUnramifiedCoordinateExistence.{u,v} := by
  intro p _ F E _ _ _ _ he
  exact ArithmeticCoordinate.coordinate_exists F E he

end Langlands.ClassFieldTheory.Local
