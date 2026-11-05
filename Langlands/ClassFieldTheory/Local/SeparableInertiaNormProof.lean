import Langlands.ClassFieldTheory.Local.SeparableInertiaNormAmbient
import Langlands.ClassFieldTheory.Local.SeparableInertiaNormStatement
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof

/-! # Proof of unit norm surjectivity over the separable inertia fixed field

The ambient field is `Ω = SeparableClosure F`, which is Galois over `U = inertiaFixedField F`,
with the spectral valuation `sepClosureValuation F`. The hypotheses of
`SeparableInertiaNorm.AmbientHyp` hold:

* the spectral norm is invariant under every automorphism of `Ω` over `F`;
* the valuation ring of the separably closed field `Ω` is Henselian;
* the residue field of `U` is algebraically closed;
* the valuation ring of `U` is a discrete valuation ring.
-/

noncomputable section

open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped NNReal

namespace Langlands.ClassFieldTheory.Local

universe u

namespace SeparableInertiaNorm

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

instance sepClosure_isGalois_inertiaFixedField :
    IsGalois (inertiaFixedField F) (SeparableClosure F) :=
  IsGalois.tower_top_of_isGalois F (inertiaFixedField F) (SeparableClosure F)

/-- The spectral valuation of `SeparableClosure F` satisfies the ambient hypotheses over the
separable inertia fixed field. -/
theorem ambientHyp_sepClosureValuation :
    AmbientHyp (U := inertiaFixedField F) (sepClosureValuation F) where
  inv σ x := by
    let : NontriviallyNormedField F := localNormedField F
    apply NNReal.coe_injective
    rw [sepClosureValuation_apply, sepClosureValuation_apply]
    exact (spectralNorm_eq_of_equiv (σ.restrictScalars F) x).symm
  hensel :=
    let : HenselianLocalRing (sepClosureValuation F).valuationSubring :=
      sepClosed_henselian (sepClosureIntegers F)
    valHensel_of_henselian (sepClosureValuation F)
  residueRoot := by
    have h := fixedFieldResidueIsAlgClosure F
    let := (residueToFixedField F).toAlgebra
    let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldValuation F).valuationSubring) :=
      h.isAlgClosed
    exact valResidueRoot_of_isAlgClosed (fixedFieldValuation F)
  unif := by
    let : IsDiscreteValuationRing (fixedFieldValuation F).valuationSubring :=
      fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
    exact exists_valUniformizer_of_dvr (fixedFieldValuation F)

end SeparableInertiaNorm

open SeparableInertiaNorm in
/-- **Unit norm surjectivity over the separable inertia fixed field.** For every finite
extension `E` of `inertiaFixedField F` inside `SeparableClosure F` and every finite extension
`L` of `E` inside `SeparableClosure F`, every unit of `E` is the norm of a unit of `L`. -/
theorem separableInertiaUnitNormSurjectivity : SeparableInertiaUnitNormSurjectivity.{u} := by
  intro F _ _ _ _ E _ L _ u hu
  obtain ⟨x, hx, hxN⟩ := (ambientHyp_sepClosureValuation F).exists_norm_eq E L (u : E) hu
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [ZeroMemClass.coe_zero, map_zero] at hx
    exact zero_ne_one hx
  refine ⟨Units.mk0 x hx0, hx, Units.ext ?_⟩
  exact hxN

end Langlands.ClassFieldTheory.Local
