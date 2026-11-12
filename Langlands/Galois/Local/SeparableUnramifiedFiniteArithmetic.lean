import Langlands.Galois.Local.SeparableUnramifiedStatement
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.LocalRing.Quotient

noncomputable section

open IsLocalRing

namespace Langlands.LocalGalois

section SpectralFinite

variable (K L : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

instance spectralIntegers_isIntegralClosure :
    IsIntegralClosure (extensionIntegers K L) (baseIntegers K) L := by
  refine ⟨Subtype.val_injective, ?_⟩
  intro x
  rw [integral_iff_mem_spectralIntegers K L]
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.property⟩

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsPrincipalIdealRing (baseIntegers K)]

instance spectralIntegers_finite : Module.Finite (baseIntegers K) (extensionIntegers K L) :=
  IsIntegralClosure.finite (baseIntegers K) K L (extensionIntegers K L)

instance spectralIntegers_free : Module.Free (baseIntegers K) (extensionIntegers K L) := by
  let : Module.IsTorsionFree (baseIntegers K) L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((algebraMap K L).injective.comp Subtype.val_injective)
  exact IsIntegralClosure.module_free (baseIntegers K) K L (extensionIntegers K L)

theorem spectralIntegers_finrank :
    Module.finrank (baseIntegers K) (extensionIntegers K L) = Module.finrank K L := by
  let : Module.IsTorsionFree (baseIntegers K) L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((algebraMap K L).injective.comp Subtype.val_injective)
  exact IsIntegralClosure.rank (baseIntegers K) K L (extensionIntegers K L)

end SpectralFinite

section LocalAlgebra

variable (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]

attribute [local instance] Ideal.Quotient.field

local notation "I" => Ideal.map (algebraMap R S) (maximalIdeal R)

/-- The canonical map from the closed fiber of a local algebra to its residue field. -/
def residueFiberMap : (S ⧸ I) →ₐ[R ⧸ maximalIdeal R] (S ⧸ maximalIdeal S) :=
  (Ideal.Quotient.factorₐ R (map_maximalIdeal_le (algebraMap R S))).extendScalarsOfSurjective
    (show Function.Surjective (algebraMap R (R ⧸ maximalIdeal R)) from
      Ideal.Quotient.mk_surjective)

variable [Module.Finite R S] [Module.Free R S]

/-- A finite free local algebra has unchanged residue dimension exactly when the
mapped maximal ideal is already maximal. -/
theorem map_maximalIdeal_eq_iff_residue_finrank :
    Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S ↔
      Module.finrank (ResidueField R) (ResidueField S) = Module.finrank R S := by
  change I = maximalIdeal S ↔
    Module.finrank (R ⧸ maximalIdeal R) (S ⧸ maximalIdeal S) = Module.finrank R S
  have hI : I ≤ maximalIdeal S := map_maximalIdeal_le (algebraMap R S)
  let f : (S ⧸ I) →ₐ[R ⧸ maximalIdeal R] (S ⧸ maximalIdeal S) :=
    residueFiberMap R S
  have hsurj : Function.Surjective f := Ideal.Quotient.factor_surjective hI
  have hinj : Function.Injective f ↔ I = maximalIdeal S := by
    constructor
    · intro h
      apply le_antisymm hI
      intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply h
      rw [map_zero]
      change Ideal.Quotient.mk (maximalIdeal S) x = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
    · intro h
      apply (injective_iff_map_eq_zero f).mpr
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk (maximalIdeal S) x = 0 → Ideal.Quotient.mk I x = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem, h]
      exact id
  have hdim : Module.finrank (R ⧸ maximalIdeal R) (S ⧸ I) = Module.finrank R S :=
    finrank_quotient_map
  have : FiniteDimensional (R ⧸ maximalIdeal R) (S ⧸ I) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : FiniteDimensional (R ⧸ maximalIdeal R) (S ⧸ maximalIdeal S) :=
    Module.Finite.of_restrictScalars_finite R _ _
  constructor
  · intro h
    exact ((LinearEquiv.ofBijective f.toLinearMap ⟨hinj.mpr h, hsurj⟩).finrank_eq).symm.trans hdim
  · intro h
    exact hinj.mp
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := f.toLinearMap) (hdim.trans h.symm)).mpr hsurj)

end LocalAlgebra

namespace Separable

open ValuativeRel

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance separableUnramifiedFiniteArithmeticInstance1 : NontriviallyNormedField F := localNormedField F
local instance separableUnramifiedFiniteArithmeticInstance2 : IsUltrametricDist F := localNormedField_ultrametric F
local instance separableUnramifiedFiniteArithmeticInstance3 : CompleteSpace F := localNormedField_complete F
local instance separableUnramifiedFiniteArithmeticInstance4 : Finite (ResidueField (baseIntegers F)) := localResidue_finite F

instance localBaseIntegers_isDiscreteValuationRing : IsDiscreteValuationRing (baseIntegers F) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (RingEquiv.subringCongr (localNormedField_integer F)).symm

variable (E : IntermediateField F (SeparableClosure F)) [FiniteDimensional F E]

instance finiteIntermediate_residue_finite : Finite (ResidueField (extensionIntegers F E)) :=
  ResidueField.finite_of_finite (localResidue_finite F)

theorem arithmeticUnramified_iff_residue_finrank :
    ArithmeticUnramified F E ↔
      Module.finrank (ResidueField (baseIntegers F))
        (ResidueField (extensionIntegers F E)) = Module.finrank F E := by
  have hsep : Algebra.IsSeparable (ResidueField (baseIntegers F))
      (ResidueField (extensionIntegers F E)) := inferInstance
  change (_ ∧ _) ↔ _
  rw [and_iff_left hsep, map_maximalIdeal_eq_iff_residue_finrank,
    spectralIntegers_finrank F E]

end Separable
end Langlands.LocalGalois
