import Langlands.Geometry.Building.RootBuildingFieldExtension
import Langlands.Geometry.Building.GaloisApartmentQuotientAction
import Langlands.GroupScheme.Rational.CharacterBaseChange

/-! # Galois fixation of actual field-extended building points -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.GaloisPointComparison

/-- Actual rational points extended from the base are fixed by coefficient
conjugation, for an arbitrary field extension. -/
@[simp] theorem rationalConjugate_rationalExtend
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (σ : K ≃ₐ[k] K) (g : rationalPoints G) :
    rationalConjugate k K G σ (rationalExtend k K G g) = rationalExtend k K G g := by
  apply (baseChangeCoeffEquiv k K G).injective
  rw [baseChangeCoeffEquiv_rationalConjugate, baseChangeCoeffEquiv_rationalExtend,
    GaloisPoint.conjugate_extend]

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G

namespace RootFunctionFamily

/-- Literal restriction of every actual family is unchanged by coefficient
transport, since both of its restricted arguments descend from the base. -/
@[simp] theorem fieldRestrict_galoisAction (σ : K ≃ₐ[k] K)
    (φ : RootFunctionFamily S_K G_K) :
    fieldRestrict (k := k) (galoisAction k K S G σ φ) =
      fieldRestrict (k := k) φ := by
  ext a g
  rw [fieldRestrict_apply, galoisAction_apply,
    characterLattice.galoisRepresentation_baseChange, rationalConjugate_rationalExtend,
    fieldRestrict_apply]

end RootFunctionFamily

namespace KPApartmentData

variable [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance extendedMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

variable (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
  (ω : Kˣ →* Multiplicative ℝ)
  (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0)

@[simp] theorem fieldRestrictPoint_galoisAction
    (D : KPApartmentData (S := S_K) (G := G_K) i_K (fun t => (ω t).toAdd))
    (hD : GaloisStable k K i D) (σ : K ≃ₐ[k] K) (x : D.Apartment) :
    fieldRestrictPoint i hS hE ω hω D (galoisAction k K i D hD σ x) =
      fieldRestrictPoint i hS hE ω hω D x := by
  apply Apartment.ext
  exact RootFunctionFamily.fieldRestrict_galoisAction σ x.val

include hS hE hω in
/-- For a literal base change of the original split torus, every point of a
supplied stable apartment is fixed by its actual coefficient action. -/
@[simp] theorem galoisAction_eq_self_of_fieldRestrict
    (D : KPApartmentData (S := S_K) (G := G_K) i_K (fun t => (ω t).toAdd))
    (hD : GaloisStable k K i D) (σ : K ≃ₐ[k] K) (x : D.Apartment) :
    galoisAction k K i D hD σ x = x :=
  fieldRestrictPoint_injective i hS hE ω hω D
    (fieldRestrictPoint_galoisAction i hS hE ω hω D hD σ x)

/-- The actual quotient extension lands in the fixed locus of the same
upstairs quotient's coefficient action. -/
@[simp] theorem galoisQuotientAction_fieldExtendBuilding
    (D : KPApartmentData (S := S_K) (G := G_K) i_K (fun t => (ω t).toAdd))
    (hD : GaloisStable k K i D) (σ : K ≃ₐ[k] K)
    (q : (fieldRestrict i hS hE ω hω D).ReducedBuilding) :
    galoisQuotientAction k K i D hD σ (fieldExtendBuilding i hS hE ω hω D q) =
      fieldExtendBuilding i hS hE ω hω D q := by
  obtain ⟨g, x, rfl⟩ := (fieldRestrict i hS hE ω hω D).exists_smul_apartmentMap q
  rw [fieldExtendBuilding_smul, fieldExtendBuilding_apartment,
    galoisQuotientAction_smul, rationalConjugate_rationalExtend,
    galoisQuotientAction_apartmentMap,
    galoisAction_eq_self_of_fieldRestrict i hS hE ω hω D hD σ]

/-- The existing field-extension map with codomain restricted to actual
Galois-fixed points; this asserts containment, without surjectivity. -/
def fieldExtendFixedBuilding
    (D : KPApartmentData (S := S_K) (G := G_K) i_K (fun t => (ω t).toAdd))
    (hD : GaloisStable k K i D) :
    (fieldRestrict i hS hE ω hω D).ReducedBuilding →
      {z : D.ReducedBuilding // ∀ σ : K ≃ₐ[k] K, galoisQuotientAction k K i D hD σ z = z} :=
  fun q => ⟨fieldExtendBuilding i hS hE ω hω D q,
    fun σ => galoisQuotientAction_fieldExtendBuilding i hS hE ω hω D hD σ q⟩

@[simp] theorem fieldExtendFixedBuilding_val
    (D : KPApartmentData (S := S_K) (G := G_K) i_K (fun t => (ω t).toAdd))
    (hD : GaloisStable k K i D)
    (q : (fieldRestrict i hS hE ω hω D).ReducedBuilding) :
    (fieldExtendFixedBuilding i hS hE ω hω D hD q).val =
      fieldExtendBuilding i hS hE ω hω D q := rfl

/-- The same geometric premises as for the original quotient map give
injectivity of its fixed-locus factorization. -/
theorem fieldExtendFixedBuilding_injective
    (D : KPApartmentData (S := S_K) (G := G_K) i_K (fun t => (ω t).toAdd))
    (hD : GaloisStable k K i D)
    (hcommon : ApartmentQuotient.HasCommonTranslatedApartment
      (fieldRestrict i hS hE ω hω D).sharpFixerFamily)
    (hchart : Function.Injective D.apartmentMap) :
    Function.Injective (fieldExtendFixedBuilding i hS hE ω hω D hD) := by
  intro q r hqr
  exact fieldExtendBuilding_injective i hS hE ω hω D hcommon hchart
    (congrArg Subtype.val hqr)

end KPApartmentData

end Langlands.Geometry.Building
