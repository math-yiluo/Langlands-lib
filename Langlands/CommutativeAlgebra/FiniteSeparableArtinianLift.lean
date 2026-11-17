import Langlands.CommutativeAlgebra.FiniteSeparableNilradicalModel
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Finite free local lifts of finite separable residue extensions -/

noncomputable section

universe u

open scoped TensorProduct
open IsLocalRing

namespace Langlands.CommutativeAlgebra

/-- A surjection with nilpotent kernel reflects units. -/
theorem isLocalHom_of_surjective_nilpotent_ker
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f)) : IsLocalHom f := by
  constructor
  intro a ha
  apply hnil.isUnit_quotient_mk_iff.mp
  let e := f.quotientKerEquivOfSurjective hf
  apply (isUnit_map_iff e _).mp
  exact ha

namespace FiniteSeparableArtinianLift

variable (R : Type u) [CommRing R] [IsLocalRing R]
  (L : Type u) [Field L] [Algebra (ResidueField R) L]
  [FiniteDimensional (ResidueField R) L] [Algebra.IsSeparable (ResidueField R) L]

/-- The actual finite free monic quotient lifting the specified residue extension. -/
def model : FiniteSeparableLiftedPolynomialModel R (ResidueField R) (ResidueField R) L :=
  finiteSeparableLiftedPolynomialModel R (ResidueField R) (ResidueField R) L
    (residue_surjective)

/-- The carrier is the actual monic polynomial quotient, with its original R action. -/
abbrev Carrier := (model R L).Carrier

/-- Its scalar extension to the residue field is the original specified field L. -/
def fibreEquiv : (ResidueField R) ⊗[R] Carrier R L ≃ₐ[ResidueField R] L :=
  (model R L).genericEquiv

/-- The actual surjection from the lifted algebra to the specified field L. -/
def toField : Carrier R L →+* L := (model R L).genericMap

theorem toField_surjective : Function.Surjective (toField R L) :=
  (fibreEquiv R L).surjective.comp
    (Algebra.TensorProduct.includeRight_surjective (Carrier R L) residue_surjective)

@[simp]
theorem toField_algebraMap (r : R) :
    toField R L (algebraMap R (Carrier R L) r) =
      algebraMap (ResidueField R) L (residue R r) :=
  (model R L).genericMap_of r

theorem ker_toField : RingHom.ker (toField R L) =
    (maximalIdeal R).map (algebraMap R (Carrier R L)) := by
  rw [toField, FiniteSeparableLiftedPolynomialModel.genericMap, RingHom.ker_equiv_comp]
  exact ker_includeRight_quotient R (Carrier R L) (maximalIdeal R)

instance : Nontrivial (Carrier R L) := (toField R L).domain_nontrivial

instance : Module.FaithfullyFlat R (Carrier R L) := inferInstance

variable [IsArtinianRing R]

theorem isNilpotent_ker_toField : IsNilpotent (RingHom.ker (toField R L)) := by
  rw [ker_toField]
  have hnil := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hnil
  obtain ⟨n, hn⟩ := hnil
  exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]; rfl⟩

instance : IsLocalHom (toField R L) :=
  isLocalHom_of_surjective_nilpotent_ker _ (toField_surjective R L)
    (isNilpotent_ker_toField R L)

instance : IsLocalRing (Carrier R L) := (toField R L).domain_isLocalRing

theorem maximalIdeal_eq_ker_toField : maximalIdeal (Carrier R L) =
    RingHom.ker (toField R L) := by
  exact (IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective _ (toField_surjective R L))).symm

theorem isNilpotent_maximalIdeal : IsNilpotent (maximalIdeal (Carrier R L)) := by
  rw [maximalIdeal_eq_ker_toField]
  exact isNilpotent_ker_toField R L

instance : IsArtinianRing (Carrier R L) := IsArtinianRing.of_finite R (Carrier R L)

instance : IsLocalHom (algebraMap R (Carrier R L)) := by
  constructor
  intro r hr
  apply isUnit_of_map_unit (residue R) r
  apply isUnit_of_map_unit (algebraMap (ResidueField R) L)
  simpa only [toField_algebraMap] using (toField R L).isUnit_map hr

/-- The specified field extension is the actual quotient by the nilpotent maximal ideal. -/
def residueEquiv : ResidueField (Carrier R L) ≃+* L :=
  (Ideal.quotEquivOfEq (maximalIdeal_eq_ker_toField R L)).trans
    ((toField R L).quotientKerEquivOfSurjective (toField_surjective R L))

@[simp]
theorem residueEquiv_residue (a : Carrier R L) :
    residueEquiv R L (residue (Carrier R L) a) = toField R L a := rfl

end FiniteSeparableArtinianLift

end Langlands.CommutativeAlgebra
