import Langlands.Geometry.FormalGroup.NilpotentReduction
import Langlands.Geometry.FormalGroup.SpecialModule
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Unramified coefficient maps for Drinfeld's residue coordinates -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup

open CategoryTheory

namespace Nilp

variable {O : Type u} [CommRing O] {π : O}
variable {C : Type w} [CommRing C] [Algebra O C] [Algebra.FormallyEtale O C]
variable {B B' : Nilp.{u, v} O π}

/-- Lift a formally étale coefficient map through actual reduction modulo π. -/
def liftEtale (B : Nilp.{u, v} O π) (g : C →ₐ[O] Reduction π B.obj) :
    C →ₐ[O] B.obj :=
  Algebra.FormallySmooth.lift (reductionIdeal π B.obj) (reductionIdeal_isNilpotent B) g

@[simp]
theorem reductionQuotient_comp_liftEtale (B : Nilp.{u, v} O π)
    (g : C →ₐ[O] Reduction π B.obj) :
    (reductionQuotient π B.obj).comp (B.liftEtale g) = g :=
  Algebra.FormallySmooth.comp_lift _ _ _

/-- The reduction equation characterizes the lift. -/
theorem liftEtale_unique (B : Nilp.{u, v} O π) (g : C →ₐ[O] Reduction π B.obj)
    (h : C →ₐ[O] B.obj) (hh : (reductionQuotient π B.obj).comp h = g) :
    h = B.liftEtale g :=
  Algebra.FormallyUnramified.lift_unique (reductionIdeal π B.obj)
    (reductionIdeal_isNilpotent B) _ _ (hh.trans (reductionQuotient_comp_liftEtale B g).symm)

/-- The unique lift commutes with every morphism of Nilp algebras. -/
theorem liftEtale_natural (f : B ⟶ B') (g : C →ₐ[O] Reduction π B.obj) :
    f.hom.hom.comp (B.liftEtale g) =
      B'.liftEtale ((reductionMap f.hom.hom).comp g) := by
  apply liftEtale_unique
  ext c
  have h := AlgHom.congr_fun (reductionQuotient_comp_liftEtale B g) c
  change reductionQuotient π B'.obj (f.hom.hom (B.liftEtale g c)) =
    reductionMap f.hom.hom (g c)
  rw [← reductionMap_quotient, show reductionQuotient π B.obj (B.liftEtale g c) = g c from h]

end Nilp

namespace LocalDivision

open ValuativeRel CentralDivision

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type w} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

/-- The map from the base integer ring to the embedded integer ring is local. -/
theorem subfieldIntegerAlgebra_isLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) where
  map_nonunit a ha := by
    have hv := (DivisionValuation.isUnit_iff_value_eq_one
      (localDivisionSubfieldValuation K D ι) _).mp ha
    change localReducedNormValuation K D (ι (algebraMap K L (a : K))) = 1 at hv
    rw [ι.commutes, localReducedNormValuation_algebraMap] at hv
    exact ((Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one).mpr
      ((pow_eq_one_iff_of_nonneg zero_le (CentralSimple.reducedDegree_pos K D).ne').mp hv)

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ]

/-- Choose a residue-valued character of the actual finite étale integer subfield. -/
def subfieldResidueCharacter [Algebra 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]
    [IsAlgClosure 𝓀[K] κ] (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) :
    SubfieldIntegerRing K D ι →ₐ[𝒪[K]] κ := by
  let C := SubfieldIntegerRing K D ι
  letI : IsLocalHom (algebraMap 𝒪[K] C) := subfieldIntegerAlgebra_isLocalHom ι
  letI : Module.Finite 𝒪[K] C := hL.2.1
  letI : Finite (IsLocalRing.ResidueField C) :=
    IsLocalRing.ResidueField.finite_of_finite (R := 𝒪[K]) (S := C) inferInstance
  letI : IsAlgClosed κ := IsAlgClosure.isAlgClosed 𝓀[K]
  let j : IsLocalRing.ResidueField C →ₐ[𝓀[K]] κ := IsAlgClosed.lift
  exact (j.restrictScalars 𝒪[K]).comp (IsScalarTower.toAlgHom 𝒪[K] C (IsLocalRing.ResidueField C))

variable {ι} {π : 𝒪[K]} {B B' : Nilp.{u, v} 𝒪[K] π}

/-- Lift a chosen residue character through the residue coordinate of a test algebra. -/
def subfieldCoefficientLift (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (χ : SubfieldIntegerRing K D ι →ₐ[𝒪[K]] κ)
    (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj) :
    SubfieldIntegerRing K D ι →ₐ[𝒪[K]] B.obj :=
  letI : Algebra.Etale 𝒪[K] (SubfieldIntegerRing K D ι) := hL.2.2.1
  B.liftEtale (ψ.comp χ)

@[simp]
theorem reductionQuotient_comp_subfieldCoefficientLift
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (χ : SubfieldIntegerRing K D ι →ₐ[𝒪[K]] κ)
    (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj) :
    (Nilp.reductionQuotient π B.obj).comp (subfieldCoefficientLift hL χ ψ) = ψ.comp χ :=
  letI : Algebra.Etale 𝒪[K] (SubfieldIntegerRing K D ι) := hL.2.2.1
  B.reductionQuotient_comp_liftEtale (ψ.comp χ)

/-- The same chosen character gives compatible lifts on all affine base changes. -/
theorem subfieldCoefficientLift_natural
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (χ : SubfieldIntegerRing K D ι →ₐ[𝒪[K]] κ)
    (f : B ⟶ B') (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj) :
    f.hom.hom.comp (subfieldCoefficientLift hL χ ψ) =
      subfieldCoefficientLift hL χ ((Nilp.reductionMap f.hom.hom).comp ψ) :=
  letI : Algebra.Etale 𝒪[K] (SubfieldIntegerRing K D ι) := hL.2.2.1
  Nilp.liftEtale_natural f (ψ.comp χ)

end LocalDivision

end Langlands.FormalGroup
