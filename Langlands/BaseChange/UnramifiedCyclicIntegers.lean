import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.ClassFieldTheory.Local.UnramifiedArithmeticProof
import Langlands.LocalFactor.Ramification.Galois
import Langlands.LocalField.RelativeIdealPowers
import Mathlib.FieldTheory.PrimitiveElement

/-! The action of a cyclic p-adic extension on its integer and residue rings. -/

noncomputable section

namespace Langlands.BaseChange

open IsLocalRing PadicField.TopologicalData

universe u v

section Integers

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
variable [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]

local notation "T" => F.canonicalTopologicalData
local notation "S" => E.canonicalTopologicalData

local instance : Algebra (T).Integers (S).Integers := relativeIntegerAlgebra T S
local instance : Algebra (T).ResidueField (S).ResidueField := relativeResidueAlgebra T S

local notation "integerAction" => Ramification.Padic.integerAutHom S F.Carrier
local notation "residueAction" => Ramification.Padic.residueHom S F.Carrier

/-- The published integer action as automorphisms over the base integer ring. -/
def canonicalIntegerAut : (E.Carrier ≃ₐ[F.Carrier] E.Carrier) →*
    ((S).Integers ≃ₐ[(T).Integers] (S).Integers) where
  toFun σ :=
    { integerAction σ with
      commutes' := fun x => Subtype.ext (σ.commutes (x : F.Carrier)) }
  map_one' := AlgEquiv.ext fun x => DFunLike.congr_fun (map_one integerAction) x
  map_mul' σ τ := AlgEquiv.ext fun x => DFunLike.congr_fun (map_mul integerAction σ τ) x

@[simp] theorem canonicalIntegerAut_coe (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier)
    (x : (S).Integers) : (canonicalIntegerAut F E σ x : E.Carrier) = σ x := rfl

/-- The published residue action as automorphisms over the base residue field. -/
def canonicalResidueAut : (E.Carrier ≃ₐ[F.Carrier] E.Carrier) →*
    ((S).ResidueField ≃ₐ[(T).ResidueField] (S).ResidueField) where
  toFun σ :=
    { residueAction σ with
      commutes' := by
        intro x
        obtain ⟨y, rfl⟩ := residue_surjective x
        exact congrArg (S).residue ((canonicalIntegerAut F E σ).commutes y) }
  map_one' := AlgEquiv.ext fun x => DFunLike.congr_fun (map_one residueAction) x
  map_mul' σ τ := AlgEquiv.ext fun x => DFunLike.congr_fun (map_mul residueAction σ τ) x

@[simp] theorem canonicalResidueAut_residue (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier)
    (x : (S).Integers) : canonicalResidueAut F E σ ((S).residue x) =
      (S).residue (canonicalIntegerAut F E σ x) := rfl

section Unramified

open Langlands.ClassFieldTheory.Local.ArithmeticCoordinate

variable [FiniteDimensional F.Carrier E.Carrier] [IsGalois F.Carrier E.Carrier]

local instance : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance : NormedAlgebra (Padic p) F.Carrier := F.canonicalNormedAlgebra
local instance : IsUltrametricDist F.Carrier :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
local instance : ProperSpace F.Carrier := FiniteDimensional.proper (Padic p) F.Carrier

/-- Faithfulness of the residue action transported to the canonical integer rings. -/
theorem canonicalResidueAut_injective (he : (S).ramificationIndex = (T).ramificationIndex) :
    Function.Injective (canonicalResidueAut F E) := by
  intro σ τ hστ
  apply residueHom_injective F E he.symm
  apply AlgEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := residue_surjective x
  apply (extensionResidueEquiv F E).injective
  change (S).residue (extensionIntegerEquiv F E (LocalGalois.integerAut F.Carrier E.Carrier σ y)) =
    (S).residue (extensionIntegerEquiv F E (LocalGalois.integerAut F.Carrier E.Carrier τ y))
  have hcomm (ρ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) :
      extensionIntegerEquiv F E (LocalGalois.integerAut F.Carrier E.Carrier ρ y) =
        canonicalIntegerAut F E ρ (extensionIntegerEquiv F E y) := Subtype.ext rfl
  rw [hcomm σ, hcomm τ, ← canonicalResidueAut_residue, ← canonicalResidueAut_residue]
  exact DFunLike.congr_fun hστ _

end Unramified

/-- An integral element whose cyclic conjugates are pairwise distinct after reduction. -/
theorem exists_integer_distinct_conjugates {σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier}
    {l : ℕ} (hσ : IsCyclicAlgebra σ l) (he : (S).ramificationIndex = (T).ramificationIndex) :
    ∃ a : (S).Integers, Function.Injective
      (fun i : Fin l => (S).residue (canonicalIntegerAut F E (σ ^ (i : ℕ)) a)) := by
  let := hσ.1
  let := hσ.isGalois
  let := (T).finite_residueField
  let := (S).finite_residueField
  obtain ⟨b, hb⟩ := Field.exists_primitive_element_of_finite_top (T).ResidueField (S).ResidueField
  obtain ⟨a, rfl⟩ := residue_surjective b
  have hgen : Algebra.adjoin (T).ResidueField {(S).residue a} = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra, hb]
    rfl
  refine ⟨a, fun i j hij => Fin.ext ?_⟩
  apply pow_injOn_Iio_orderOf (x := σ)
  · simpa only [Set.mem_Iio, hσ.2.2.2.1] using i.isLt
  · simpa only [Set.mem_Iio, hσ.2.2.2.1] using j.isLt
  apply canonicalResidueAut_injective F E he
  apply AlgEquiv.ext
  intro x
  have h :
      (canonicalResidueAut F E (σ ^ (i : ℕ))).toAlgHom =
        (canonicalResidueAut F E (σ ^ (j : ℕ))).toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top hgen
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    change canonicalResidueAut F E (σ ^ (i : ℕ)) ((S).residue a) =
      canonicalResidueAut F E (σ ^ (j : ℕ)) ((S).residue a)
    simpa only [canonicalResidueAut_residue] using hij
  exact DFunLike.congr_fun h x

/-- In the unramified case the relative integer map extends the maximal ideal. -/
theorem relativeIntegerMap_maximalIdeal (he : (S).ramificationIndex = (T).ramificationIndex) :
    (maximalIdeal (T).Integers).map (relativeIntegerMap T S) = maximalIdeal (S).Integers := by
  simpa only [pow_one] using
    map_maximalIdeal_of_ramificationIndex_eq_mul T S 1 (by simpa only [one_mul] using he)

end Integers

end Langlands.BaseChange
