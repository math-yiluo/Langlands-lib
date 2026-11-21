import Langlands.LocalFactor.BrauerKernel.GaloisType
import Langlands.ClassFieldTheory.Local.UpperGradeNorm
import Langlands.ClassFieldTheory.Local.GradeCoinvariants
import Langlands.ClassFieldTheory.Local.UnramifiedArithmeticProof
import Langlands.LocalFactor.BrauerKernel.ConjugateTransport

/-! # Frobenius lifts and conjugation on the unit grades of the common closure -/

noncomputable section

namespace Langlands.LocalClassField.GradeReciprocity

open IsLocalRing Ramification.Padic ClassFieldTheory.Local
open LocalFactor LocalFactor.CommonClosure Weil.Local UpperGradeNorm

universe uK uM
variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

section Frobenius

variable (M : PadicField.{uM} p)
  [Algebra K.Carrier M.Carrier] [IsScalarTower (Padic p) K.Carrier M.Carrier]
  [FiniteDimensional K.Carrier M.Carrier] [IsGalois K.Carrier M.Carrier]

local instance : NontriviallyNormedField K.Carrier := K.canonicalNormedField
local instance : NormedAlgebra (Padic p) K.Carrier := K.canonicalNormedAlgebra
local instance : IsUltrametricDist K.Carrier :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := Padic p) (L := K.Carrier))
local instance : ProperSpace K.Carrier := FiniteDimensional.proper (Padic p) K.Carrier

/-- A lift of the arithmetic residue Frobenius to an actual Galois
automorphism, on the canonical integer and residue rings. -/
theorem exists_residue_frobenius_lift :
    ∃ σ : Gal(M.Carrier/K.Carrier), ∀ x : M.canonicalTopologicalData.ResidueField,
      IsLocalRing.ResidueField.mapAut
          (integerAutomorphism M.canonicalTopologicalData K.Carrier σ) x =
        x ^ K.canonicalTopologicalData.residueCardinality := by
  let I := LocalGalois.extensionIntegers K.Carrier M.Carrier
  let k := ResidueField (LocalGalois.baseIntegers K.Carrier)
  let L := ResidueField I
  let := K.canonicalTopologicalData.finite_residueField
  let : Finite k := Finite.of_equiv _ (ArithmeticCoordinate.baseResidueEquiv K).symm.toEquiv
  let : Fintype k := Fintype.ofFinite k
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic k L
  obtain ⟨σ, hσ⟩ := LocalGalois.residueHom_surjective K.Carrier M.Carrier φ
  refine ⟨σ, fun x => ?_⟩
  let i := ArithmeticCoordinate.extensionIntegerEquiv K M
  let r := ArithmeticCoordinate.extensionResidueEquiv K M
  have hq : Fintype.card k = K.canonicalTopologicalData.residueCardinality := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (ArithmeticCoordinate.baseResidueEquiv K).toEquiv
  obtain ⟨x, rfl⟩ := residue_surjective x
  obtain ⟨y, rfl⟩ := i.surjective x
  have hInt : integerAutomorphism M.canonicalTopologicalData K.Carrier σ (i y) =
      i (LocalGalois.integerAut K.Carrier M.Carrier σ y) := Subtype.ext rfl
  calc
    _ = residue _ (integerAutomorphism M.canonicalTopologicalData K.Carrier σ (i y)) := rfl
    _ = r (LocalGalois.residueHom K.Carrier M.Carrier σ (residue I y)) := by
      rw [hInt, LocalGalois.residueHom_apply]
      rfl
    _ = r ((residue I y) ^ Fintype.card k) := by rw [hσ]; rfl
    _ = _ := by rw [map_pow, hq]; rfl

end Frobenius

section CommonClosure

variable (E : Extension K) [IsGalois K.Carrier E.field]

/-- Weil restriction for the finite Galois extension, using the normal-extension map. -/
abbrev weilRestriction : localWeilGroup K →* Gal(E.field/K.Carrier) :=
  Langlands.LocalFactor.NonabelianBrauer.galoisRestriction K E

private theorem weilRestriction_ker : (weilRestriction K E).ker = weilSubgroup K E := by
  ext w
  change AlgEquiv.restrictNormalHom E.field (localProjection K w) = 1 ↔
    localProjection K w ∈ E.field.fixingSubgroup
  exact SetLike.ext_iff.mp (IntermediateField.restrictNormalHom_ker E.field) (localProjection K w)

/-- Conjugation by an actual base Weil element, on the normal fixing Weil
subgroup of the intermediate field. -/
def conjugateWeil (g : localWeilGroup K) (w : weilSubgroup K E) : weilSubgroup K E :=
  ⟨g * w.val * g⁻¹, by
    have h : (weilSubgroup K E).Normal := weilRestriction_ker K E ▸ inferInstanceAs
      ((weilRestriction K E).ker.Normal)
    exact h.conj_mem w.val w.property g⟩

@[simp] theorem conjugateWeil_val (g : localWeilGroup K) (w : weilSubgroup K E) :
    (conjugateWeil K E g w).val = g * w.val * g⁻¹ := rfl

/-- Reciprocity on the same normal fixing subgroup transports conjugation by
`g` to the action of its finite Galois restriction on field units. -/
theorem reciprocityUnits_conjugateWeil (eC : ReciprocityFamily K) (heC : NormalizedReciprocity K eC)
    (g : localWeilGroup K) (w : weilSubgroup K E) :
    reciprocityUnits K eC E (conjugateWeil K E g w) =
      Units.map (weilRestriction K E g).toMonoidHom (reciprocityUnits K eC E w) := by
  let : CharZero K.Carrier := Algebra.charZero_of_charZero (Padic p) K.Carrier
  let κ := localProjection K g
  have hfield : (E.conj κ).field = E.field :=
    IntermediateField.normal_iff_forall_map_eq'.mp inferInstance κ
  let z := E.weilConjugation (localResidueDegree K) g w
  let z' := conjugateWeil K E g w
  have h1 := NonabelianBrauer.reciprocityUnits_coe_eq_of_field_eq K eC (E.conj κ) E hfield z z' rfl
  have h2 := NonabelianBrauer.reciprocityUnits_weilConjugation K eC heC E g w
  apply Units.ext
  apply Subtype.ext
  exact h1.symm.trans (h2.trans ((localProjection K g).restrictNormal_commutes E.field
    (reciprocityUnits K eC E w : E.field)).symm)

/-- The norm square makes the base norm invariant under the lifted
conjugation action, since base reciprocity has abelian target. -/
theorem normToBaseUnits_weilRestriction (eC : ReciprocityFamily K) (heC : NormalizedReciprocity K eC)
    (g : localWeilGroup K) (u : E.fieldˣ) :
    normToBaseUnits K E (Units.map (weilRestriction K E g).toMonoidHom u) = normToBaseUnits K E u := by
  obtain ⟨w, rfl⟩ := CommonClosure.reciprocityUnits_surjective K eC E u
  rw [← reciprocityUnits_conjugateWeil K E eC heC g w,
    normToBaseUnits_reciprocityUnits K E eC heC, normToBaseUnits_reciprocityUnits K E eC heC,
    conjugateWeil_val, map_mul, map_mul, map_inv]
  let a := RankOne.reciprocityUnits K (Correspondence.baseReciprocityCandidate K eC) g
  let b := RankOne.reciprocityUnits K (Correspondence.baseReciprocityCandidate K eC) w.val
  change a * b * a⁻¹ = b
  rw [mul_comm a b, mul_assoc, mul_inv_cancel, mul_one]

local instance : Algebra (Padic p) E.field := (E.asPadicField (p := p)).algebra
local instance : IsScalarTower (Padic p) K.Carrier E.field := IsScalarTower.of_algebraMap_eq' rfl

/-- A Weil element whose restriction induces arithmetic Frobenius on the
actual residue ring of the finite intermediate field. -/
theorem exists_weil_residue_frobenius_lift :
    ∃ g : localWeilGroup K, ∀ x : (fieldData K E).ResidueField,
      IsLocalRing.ResidueField.mapAut
          (integerAutomorphism (fieldData K E) K.Carrier (weilRestriction K E g)) x =
        x ^ K.canonicalTopologicalData.residueCardinality := by
  obtain ⟨σ, hσ⟩ := exists_residue_frobenius_lift K (E.asPadicField (p := p))
  obtain ⟨g, hg⟩ := Langlands.LocalFactor.NonabelianBrauer.galoisRestriction_surjective K E σ
  exact ⟨g, fun x => hg.symm ▸ hσ x⟩

omit [IsGalois K.Carrier E.field] in
/-- The induced integer-ring action on a unit level is the original field
automorphism on its underlying field unit. -/
theorem unitFiltrationMap_galois_val (σ : Gal(E.field/K.Carrier)) (n : ℕ)
    (x : (fieldData K E).unitFiltration n) :
    ((fieldData K E).unitFiltrationMap (integerAutomorphism (fieldData K E) K.Carrier σ) n x).val =
      Units.map σ.toMonoidHom x.val := by
  let T := fieldData K E
  let y := T.unitFiltrationMap (integerAutomorphism T K.Carrier σ) n x
  apply Units.ext
  change (y.val : E.field) = σ (x.val : E.field)
  rw [← T.filtrationIntegerUnit_coe n y]
  change ((T.filtrationIntegerUnit n (T.unitFiltrationMap _ n x) : T.Integers) : E.field) = _
  rw [T.filtrationIntegerUnit_unitFiltrationMap]
  change σ (((T.filtrationIntegerUnit n x : T.Integers) : E.field)) = _
  rw [T.filtrationIntegerUnit_coe]

end CommonClosure

end Langlands.LocalClassField.GradeReciprocity
