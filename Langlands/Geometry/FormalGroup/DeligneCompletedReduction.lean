import Langlands.Geometry.FormalGroup.DeligneCompletedBase
import Langlands.Geometry.FormalGroup.DeligneResidueAction
import Langlands.Geometry.FormalGroup.DrinfeldResidueFrobenius

/-! # Reduction of the actual completed base coordinate of Deligne points -/

noncomputable section

universe u

namespace Langlands.DeligneFormalSpace

open CategoryTheory ValuativeRel CentralSimple CentralDivision IsLocalRing
open _root_.Langlands.FormalGroup
open Langlands.LocalGalois.Separable.UnramifiedCompletion
open scoped WithZero

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {π : 𝒪[K]} (hπ : Irreducible π)
variable {B B' : Nilp.{u, u} 𝒪[K] π}

/-- The actual completed-base map to a test algebra induces a residue-field
map to its quotient by the uniformizer. -/
def completedCoefficientReduction (φ : Integers K →ₐ[𝒪[K]] B.obj) :
    Residue K →ₐ[𝒪[K]] ((Nilp.reductionFunctor 𝒪[K] π).obj B).obj :=
  Ideal.Quotient.liftₐ (maximalIdeal (Integers K)) ((Nilp.quotientO 𝒪[K] B).comp φ) (by
    intro x hx
    rw [maximalIdeal_eq_span_uniformizer K hπ, Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    change (Nilp.quotientO 𝒪[K] B) (φ ((algebraMap 𝒪[K] (Integers K) π) * y)) = 0
    rw [map_mul, map_mul, AlgHom.commutes]
    change Nilp.reductionQuotient π B.obj (algebraMap _ _ π) *
      Nilp.reductionQuotient π B.obj (φ y) = (0 : Nilp.Reduction π B.obj)
    rw [Nilp.reductionQuotient_uniformizer, zero_mul])

/-- The factorization is the quotient of the original completed-base map. -/
@[simp]
theorem completedCoefficientReduction_residue (φ : Integers K →ₐ[𝒪[K]] B.obj)
    (x : Integers K) :
    completedCoefficientReduction hπ φ (residue (Integers K) x) =
      (Nilp.quotientO 𝒪[K] B) (φ x) := rfl

/-- Coefficient base change commutes with actual reduction of the base map. -/
theorem completedCoefficientReduction_natural (f : B ⟶ B')
    (φ : Integers K →ₐ[𝒪[K]] B.obj) :
    (Nilp.reducedScalarMap 𝒪[K] f).comp (completedCoefficientReduction hπ φ) =
      completedCoefficientReduction hπ (f.hom.hom.comp φ) := by
  apply AlgHom.ext
  intro x
  obtain ⟨x, rfl⟩ := residue_surjective x
  exact (AlgHom.congr_fun (Nilp.quotientO_natural 𝒪[K] f) (φ x)).symm

variable {d : ℕ} [NeZero d]

/-- Forget the lift of the base coordinate by taking its actual residue map. -/
def nilpDeligneCompletedReduction : nilpDeligneCompletedFunctor (d := d) hπ ⟶
    nilpDeligneResidueFunctor (d := d) (Residue K) (coefficientUniformizer_ne_zero (F := K) hπ) where
  app B := ↾(fun x => (x.1, completedCoefficientReduction hπ x.2))
  naturality B B' f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · exact (completedCoefficientReduction_natural hπ f x.2).symm

private def forgetAlgAut (O S : Type*) [CommRing O] [CommRing S] [Algebra O S] :
    (S ≃ₐ[O] S) →* RingAut S where
  toFun e := e.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

omit [NeZero d] in
/-- Every signed power of the completed Frobenius induces the corresponding
signed power on the residue field. -/
theorem residue_arithmeticFrobenius_zpow (n : ℤ) (x : Integers K) :
    residue (Integers K) ((arithmeticFrobenius K ^ n) x) =
      (residueFrobenius (K := K) (Residue K) ^ n) (residue (Integers K) x) := by
  let fromCompleted := ResidueField.mapAut.comp (forgetAlgAut 𝒪[K] (Integers K))
  let fromResidue := forgetAlgAut 𝒪[K] (Residue K)
  have h : fromCompleted (arithmeticFrobenius K) =
      fromResidue (residueFrobenius (K := K) (Residue K)) := by
    apply RingEquiv.ext
    intro y
    obtain ⟨y, rfl⟩ := residue_surjective y
    change residue (Integers K) (arithmeticFrobenius K y) =
      residueFrobenius (K := K) (Residue K) (residue (Integers K) y)
    rw [residue_arithmeticFrobenius, residueFrobenius_apply]
  have hn : fromCompleted (arithmeticFrobenius K ^ n) =
      fromResidue (residueFrobenius (K := K) (Residue K) ^ n) := by
    rw [map_zpow, map_zpow, h]
  exact DFunLike.congr_fun hn (residue (Integers K) x)

omit [NeZero d] in
/-- Reduction of the base map commutes with precomposition by the signed Frobenius. -/
theorem completedCoefficientReduction_precomp (n : ℤ)
    (φ : Integers K →ₐ[𝒪[K]] B.obj) :
    completedCoefficientReduction hπ (φ.comp (arithmeticFrobenius K ^ n).toAlgHom) =
      (completedCoefficientReduction hπ φ).comp
        ((residueFrobenius (K := K) (Residue K)) ^ n).toAlgHom := by
  apply AlgHom.ext
  intro x
  obtain ⟨x, rfl⟩ := residue_surjective x
  change completedCoefficientReduction hπ (φ.comp (arithmeticFrobenius K ^ n).toAlgHom)
      (residue (Integers K) x) = completedCoefficientReduction hπ φ
        ((residueFrobenius (K := K) (Residue K) ^ n) (residue (Integers K) x))
  rw [← residue_arithmeticFrobenius_zpow n x]
  rfl

variable {D : Type u} [DivisionRing D] [Algebra K D]
variable [FiniteDimensional K D] [Algebra.IsCentral K D]

omit [NeZero d] in
/-- Both actions use the same determinant and reduced-norm integer orders. -/
theorem residueActionOrder_eq_exponentHom (g : GL (Fin (reducedDegree K D)) K × Dˣ) :
    residueActionOrder g = LocalDivision.DrinfeldAction.exponentHom K D g := by
  change (residueActionOrder g).toAdd = LocalDivision.DrinfeldAction.exponent K D g
  rw [LocalDivision.DrinfeldAction.exponent_eq, Plancherel.fieldOrderUnits_toAdd,
    LocalDivision.DrinfeldAction.divisionUnitOrder_toAdd]
  rfl

local instance : NeZero (reducedDegree K D) := ⟨(reducedDegree_pos K D).ne'⟩

/-- Reducing the completed base coordinate intertwines the two actual Deligne-side actions. -/
theorem nilpDeligneCompletedReduction_equivariant (g : GL (Fin (reducedDegree K D)) K × Dˣ) :
    (nilpDeligneCompletedDivisionAction hπ g).asIso.hom ≫ nilpDeligneCompletedReduction hπ =
      nilpDeligneCompletedReduction hπ ≫ (nilpDeligneDivisionAction (Residue K) hπ g).asIso.hom := by
  apply NatTrans.ext
  funext B
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · let y : (nilpDeligneResidueFunctor (d := reducedDegree K D) (Residue K)
        (coefficientUniformizer_ne_zero (F := K) hπ)).obj B :=
      (x.1, completedCoefficientReduction hπ x.2)
    change completedCoefficientReduction hπ ((nilpDeligneCompletedDivisionAction hπ g).asIso.hom.app B x).2 =
      ((nilpDeligneDivisionAction (Residue K) hπ g).asIso.hom.app B y).2
    have hcompleted := nilpDeligneCompletedDivisionAction_base hπ g x
    have hresidue := nilpDeligneDivisionAction_residue (Residue K) hπ g B y
    have horder := congrArg (fun n : Multiplicative ℤ => y.2.comp
      ((residueFrobenius (K := K) (Residue K)) ^ (-n.toAdd : ℤ)).toAlgHom)
      (residueActionOrder_eq_exponentHom g)
    exact (congrArg (completedCoefficientReduction hπ) hcompleted).trans
      ((completedCoefficientReduction_precomp hπ _ x.2).trans (horder.symm.trans hresidue.symm))

end Langlands.DeligneFormalSpace
