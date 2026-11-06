import Langlands.GroupScheme.IntegralModel.GenericCoefficientDescent
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Langlands.GroupScheme.Descent.ValuationIntegerCover

/-! # Descent of actual model extensions along arbitrary valued-field extensions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel

private theorem modelIso_ext
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G H : GroupScheme (Spec (CommRingCat.of K))}
    {M : IntegralModel R K G} {N : IntegralModel R K H} {f : G ≅ H}
    {e e' : M.Iso N f} (h : e.iso = e'.iso) : e = e' := by
  cases e
  cases e'
  cases h
  rfl

private theorem modelIso_eq
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G H : GroupScheme (Spec (CommRingCat.of K))}
    {M : IntegralModel R K G} {N : IntegralModel R K H} {f : G ≅ H}
    (e e' : M.Iso N f) : e = e' :=
  modelIso_ext (CategoryTheory.Iso.ext (e.toHom.hom_eq e'.toHom))

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ΓK : Type v} {ΓL : Type w}
    [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
    (vK : Valuation K ΓK) (vL : Valuation L ΓL) [vK.HasExtension vL]
    {G H : GroupScheme (Spec (CommRingCat.of K))}
    {M : IntegralModel vK.integer K G} {N : IntegralModel vK.integer K H}

local instance : Flat (Spec.algebraMap vK.integer vL.integer) :=
  (valuationInteger_fpqc vK vL).2.1

local instance : Surjective (Spec.algebraMap vK.integer vL.integer) :=
  (valuationInteger_fpqc vK vL).1

/-- An extension of the prescribed generic map descends through any extension
of valued fields, with no separate cover or compatibility input. -/
def Hom.valuationCoefficientEquiv {f : G ⟶ H} :
    M.Hom N f ≃ (M.baseChange vL.integer L).Hom (N.baseChange vL.integer L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).map f) :=
  Hom.coefficientEquiv vL.integer L

@[simp]
theorem Hom.valuationCoefficientEquiv_apply_hom {f : G ⟶ H} (φ : M.Hom N f) :
    (Hom.valuationCoefficientEquiv vK vL φ).hom =
      (GroupScheme.baseChange (Spec.algebraMap vK.integer vL.integer)).map φ.hom :=
  rfl

/-- Compatible model isomorphisms are invariant under arbitrary valued-field
extension, retaining the given generic isomorphism. -/
def Iso.valuationCoefficientEquiv {f : G ≅ H} :
    M.Iso N f ≃ (M.baseChange vL.integer L).Iso (N.baseChange vL.integer L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).mapIso f) where
  toFun e := e.baseChangeCoefficients vL.integer L
  invFun e := e.descendFromCoefficients vL.integer L
  left_inv e := modelIso_eq _ e
  right_inv e := modelIso_eq _ e

@[simp]
theorem Iso.valuationCoefficientEquiv_apply_iso {f : G ≅ H} (e : M.Iso N f) :
    (Iso.valuationCoefficientEquiv vK vL e).iso =
      (GroupScheme.baseChange (Spec.algebraMap vK.integer vL.integer)).mapIso e.iso :=
  rfl

/-- The inverse equivalence recovers the entire supplied upstairs isomorphism. -/
theorem Iso.baseChange_valuationCoefficientEquiv_symm {f : G ≅ H}
    (e : (M.baseChange vL.integer L).Iso (N.baseChange vL.integer L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).mapIso f)) :
    (GroupScheme.baseChange (Spec.algebraMap vK.integer vL.integer)).mapIso
      ((Iso.valuationCoefficientEquiv vK vL).symm e).iso = e.iso :=
  e.baseChange_descendFromCoefficients vL.integer L

/-- A generic-identity comparison after any valued-field extension identifies
the original integral-point images. -/
theorem integralPoints_eq_of_valuationCoefficientIso
    {N' : IntegralModel vK.integer K G}
    (e : (M.baseChange vL.integer L).Iso (N'.baseChange vL.integer L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).mapIso
        (CategoryTheory.Iso.refl G))) :
    M.integralPoints = N'.integralPoints :=
  ((Iso.valuationCoefficientEquiv vK vL).symm e).integralPoints_eq

end Langlands.GroupScheme.IntegralModel
