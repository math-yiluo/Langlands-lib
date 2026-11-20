import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.CommonFiniteExtension
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.FiniteDvrExtension
import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.LocalizedFibreTest

/-! # A common finite extension for normalized residue fibre tests -/

open IsLocalRing TensorProduct

noncomputable section

universe u v

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

private abbrev normalizedResidueFibre (S D : Type u) [CommRing S] [IsLocalRing S]
    [CommRing D] [Algebra S D] : Type u :=
  ResidueField S ⊗[S] integralClosure D (D ⊗[S] FractionRing S)

private theorem isReduced_normalizedResidueFibre_of_algEquiv {S D E : Type u}
    [CommRing S] [IsLocalRing S] [CommRing D] [Algebra S D] [CommRing E] [Algebra S E]
    (e : D ≃ₐ[S] E) (h : IsReduced (normalizedResidueFibre S D)) :
    IsReduced (normalizedResidueFibre S E) := by
  let f := Algebra.TensorProduct.congr
    (AlgEquiv.refl : ResidueField S ≃ₐ[ResidueField S] ResidueField S)
    (genericNormalizationCongr e)
  exact isReduced_of_injective f.symm.toRingHom f.symm.injective

section FiniteExtension

variable (R B L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]
    [CommRing B] [Algebra R B] [Field L] [Algebra (FractionRing R) L]
    [Algebra R L] [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]

local notation "S" => integralClosure R L
local notation "D" => S ⊗[R] B

/-- The residue fibre of normalization after the finite extension of the base
fraction field. -/
abbrev finiteExtensionNormalizedResidue : Type u :=
  letI : IsDiscreteValuationRing S :=
    (isDiscreteValuationRing_and_isAdicComplete_of_finiteExtension R L).choose
  normalizedResidueFibre S D

variable (L' : Type u) [Field L'] [Algebra (FractionRing R) L']
    [Algebra R L'] [IsScalarTower R (FractionRing R) L'] [FiniteDimensional (FractionRing R) L']

local notation "T" => integralClosure R L'

set_option maxHeartbeats 1000000 in
/-- Reducedness of a normalized residue fibre over a finite extension of a
complete DVR with algebraically closed residue survives a further finite
extension. -/
theorem isReduced_finiteExtensionNormalizedResidue_of_algHom
    (f : L →ₐ[FractionRing R] L')
    (hred : IsReduced (finiteExtensionNormalizedResidue R B L)) :
    IsReduced (finiteExtensionNormalizedResidue R B L') := by
  obtain ⟨hSDvr, _⟩ := isDiscreteValuationRing_and_isAdicComplete_of_finiteExtension R L
  obtain ⟨hTDvr, _⟩ := isDiscreteValuationRing_and_isAdicComplete_of_finiteExtension R L'
  let g := (f.restrictScalars R).mapIntegralClosure
  let : Algebra S T := g.toRingHom.toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  have hinj : Function.Injective (algebraMap S T) := fun x y h =>
    Subtype.ext (f.injective (congrArg Subtype.val h))
  have : Module.IsTorsionFree S T := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Module.Flat S T := inferInstance
  have : Module.Finite R T := finite_integralClosure_of_finiteExtension R L'
  have : Module.Finite S T := Module.Finite.of_restrictScalars_finite R S T
  have : Module.FaithfullyFlat R S :=
    Langlands.CommutativeAlgebra.DvrFiniteSeparableExtension.faithfullyFlat R L
  have : Module.FaithfullyFlat R T :=
    Langlands.CommutativeAlgebra.DvrFiniteSeparableExtension.faithfullyFlat R L'
  have : IsLocalHom (algebraMap R S) := (inferInstance : Algebra.IsIntegral R S).isLocalHom
  have : IsLocalHom (algebraMap R T) := (inferInstance : Algebra.IsIntegral R T).isLocalHom
  have : IsLocalHom (algebraMap S T) := (inferInstance : Algebra.IsIntegral S T).isLocalHom
  have hsurj : Function.Surjective (algebraMap (ResidueField S) (ResidueField T)) := by
    intro x
    obtain ⟨r, hr⟩ := (residueEquiv_of_finiteExtension R L').surjective x
    exact ⟨algebraMap (ResidueField R) (ResidueField S) r,
      (IsScalarTower.algebraMap_apply (ResidueField R) (ResidueField S) (ResidueField T) r).symm.trans hr⟩
  have h := isReduced_residue_normalization_baseChange_of_reduced S T D hinj hsurj hred
  let e : (T ⊗[S] D) ≃ₐ[T] (T ⊗[R] B) := Algebra.TensorProduct.cancelBaseChange R S T T B
  exact isReduced_normalizedResidueFibre_of_algEquiv e h

end FiniteExtension

section CommonExtension

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]
    {ι : Type v} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]

local notation "K" => FractionRing R

/-- If each member of a finite family has a finite extension with reduced
normalized residue fibre, one finite extension works for the whole family. -/
theorem exists_common_finiteExtensionNormalizedResidue
    (h : ∀ i, ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra R L)
      (_ : IsScalarTower R K L) (_ : FiniteDimensional K L),
        IsReduced (finiteExtensionNormalizedResidue R (B i) L)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra R L)
      (_ : IsScalarTower R K L) (_ : FiniteDimensional K L),
        ∀ i, IsReduced (finiteExtensionNormalizedResidue R (B i) L) := by
  classical
  choose L hField hAlg hAlgR hTower hFinite hReduced using h
  let : ∀ i, Field (L i) := hField
  let : ∀ i, Algebra K (L i) := hAlg
  let : ∀ i, Algebra R (L i) := hAlgR
  let : ∀ i, IsScalarTower R K (L i) := hTower
  let : ∀ i, FiniteDimensional K (L i) := hFinite
  let E := commonFiniteExtension K L
  let : Algebra R E := Algebra.compHom E (algebraMap R K)
  have : IsScalarTower R K E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional K E := finiteDimensional_commonFiniteExtension K L
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, fun i => ?_⟩
  exact isReduced_finiteExtensionNormalizedResidue_of_algHom R (B i) (L i) E
    (commonFiniteExtensionEmb K L i) (hReduced i)

end CommonExtension

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
