import Langlands.Geometry.FormalGroup.CompletedUnramifiedFrobenius
import Langlands.Geometry.FormalGroup.CompletedUnramifiedResidueMaps
import Langlands.Geometry.FormalGroup.DeligneResidueAction
import Mathlib.CategoryTheory.Conj

/-! # The projective and completed coefficient actions on the actual Deligne points -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 80000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory IsLocalRing ValuativeRel
open Langlands.LocalGalois.Separable

namespace Langlands.DeligneFormalSpace

open Langlands.FormalGroup

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

local notation "κ" => ResidueField (fixedFieldIntegers K)
local notation "Ĉ" => CompletedUnramifiedIntegers K

private theorem semiconj_algEquiv_zpow {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (r : A → B) (a : A ≃ₐ[R] A) (b : B ≃ₐ[R] B)
    (h : Function.Semiconj r a b) (n : ℤ) (x : A) : r ((a ^ n) x) = (b ^ n) (r x) := by
  have hneg : Function.Semiconj r a.symm b.symm :=
    h.inverses_right a.apply_symm_apply b.symm_apply_apply
  let P : (A ≃ₐ[R] A) × (B ≃ₐ[R] B) → Prop := fun e => Function.Semiconj r e.1 e.2
  have hp : P ((a, b) ^ n) := zpow_induction_left (g := (a, b)) (P := P)
    Function.Semiconj.id_right (fun _ h' => h.comp_right h') (fun _ h' => hneg.comp_right h') n
  have ha : ((a, b) ^ n).1 = a ^ n := map_zpow (MonoidHom.fst _ _) (a, b) n
  have hb : ((a, b) ^ n).2 = b ^ n := map_zpow (MonoidHom.snd _ _) (a, b) n
  change Function.Semiconj r ((a, b) ^ n).1 ((a, b) ^ n).2 at hp
  rw [ha, hb] at hp
  exact hp x

private theorem completedFrobenius_zpow_reduction (n : ℤ) (x : Ĉ) :
    completedUnramifiedReduction K ((completedUnramifiedFrobenius K ^ n) x) =
      (residueFrobenius (K := K) κ ^ n) (completedUnramifiedReduction K x) :=
  semiconj_algEquiv_zpow (completedUnramifiedReduction K) (completedUnramifiedFrobenius K)
    (residueFrobenius (K := K) κ) (fun y => (completedUnramifiedFrobenius_reduction K y).trans
      (residueFrobenius_apply (K := K) κ (completedUnramifiedReduction K y)).symm) n x

variable {π : 𝒪[K]} (hπ : Irreducible π)

private theorem uniformizerIdeal (hπ : Irreducible π) : maximalIdeal 𝒪[K] = Ideal.span {π} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ

/-- The comparison of coefficient maps intertwines precomposition by each
signed power of arithmetic Frobenius. -/
theorem completedCoefficient_precomp_frobenius (B : Nilp.{u, u} 𝒪[K] π)
    (g : Ĉ →ₐ[𝒪[K]] B.obj) (n : ℤ) :
    B.completedUnramifiedResidueMapEquiv (uniformizerIdeal hπ)
      (g.comp ((completedUnramifiedFrobenius K ^ n).toAlgHom)) =
    (B.completedUnramifiedResidueMapEquiv (uniformizerIdeal hπ) g).comp
      ((residueFrobenius (K := K) κ ^ n).toAlgHom) := by
  apply AlgHom.ext
  intro t
  obtain ⟨y, rfl⟩ := residue_surjective t
  let x := toCompletedUnramifiedIntegers K y
  let r := completedUnramifiedReduction K
  let q := Nilp.reductionQuotient π B.obj
  let a := completedUnramifiedFrobenius K ^ n
  let b := residueFrobenius (K := K) κ ^ n
  let e := B.completedUnramifiedResidueMapEquiv (uniformizerIdeal hπ)
  have hx : r x = residue _ y := completedUnramifiedResidueEquiv_residue K y
  change e (g.comp a.toAlgHom) (residue _ y) = e g (b (residue _ y))
  rw [← hx]
  calc
    e (g.comp a.toAlgHom) (r x) = q (g (a x)) :=
      AlgHom.congr_fun (B.completedUnramifiedResidueMapEquiv_comp (uniformizerIdeal hπ)
        (g.comp a.toAlgHom)) x
    _ = e g (r (a x)) := (AlgHom.congr_fun
      (B.completedUnramifiedResidueMapEquiv_comp (uniformizerIdeal hπ) g) (a x)).symm
    _ = e g (b (r x)) := congrArg (e g) (completedFrobenius_zpow_reduction (K := K) n x)

variable {d : ℕ} [NeZero d]

private abbrev nonzeroUniformizer (hπ : Irreducible π) : algebraMap 𝒪[K] K π ≠ 0 :=
  coefficientUniformizer_ne_zero (F := K) hπ

/-- Actual completed base change of Deligne's point functor on base-ring Nilp.
The second coordinate is a map from the completed unramified integers. -/
def nilpDeligneCompletedCoefficientFunctor : Nilp.{u, u} 𝒪[K] π ⥤ Type (u + 1) where
  obj B := (nilpSheafClassFunctor d π K (nonzeroUniformizer hπ)).obj B × (Ĉ →ₐ[𝒪[K]] B.obj)
  map f := ↾(fun x => ((nilpSheafClassFunctor d π K (nonzeroUniformizer hπ)).map f x.1,
    f.hom.hom.comp x.2))
  map_id B := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Prod.ext (ConcreteCategory.congr_hom ((nilpSheafClassFunctor d π K
      (nonzeroUniformizer hπ)).map_id B) x.1) (AlgHom.id_comp x.2)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact Prod.ext (ConcreteCategory.congr_hom ((nilpSheafClassFunctor d π K
      (nonzeroUniformizer hπ)).map_comp f g) x.1) (AlgHom.comp_assoc _ _ _)

private def completedDeligneResidueEquiv (B : Nilp.{u, u} 𝒪[K] π) :
    (nilpDeligneCompletedCoefficientFunctor (d := d) hπ).obj B ≃
      (nilpDeligneResidueFunctor (d := d) κ (nonzeroUniformizer hπ)).obj B :=
  (Equiv.refl ((nilpSheafClassFunctor d π K (nonzeroUniformizer hπ)).obj B)).prodCongr
    (B.completedUnramifiedResidueMapEquiv (uniformizerIdeal hπ))

/-- The same completed base change expressed in the residue coordinates. -/
def nilpDeligneCompletedResidueIso : nilpDeligneCompletedCoefficientFunctor (d := d) hπ ≅
    nilpDeligneResidueFunctor (d := d) κ (nonzeroUniformizer hπ) :=
  NatIso.ofComponents (fun B => (completedDeligneResidueEquiv hπ B).toIso) (by
    intro B B' f
    apply ConcreteCategory.hom_ext
    intro x
    have he := Nilp.completedUnramifiedResidueMapEquiv_natural (B := B)
      (uniformizerIdeal hπ) f x.2
    exact Prod.ext rfl he)

@[simp]
theorem nilpDeligneCompletedResidueIso_hom_app (B : Nilp.{u, u} 𝒪[K] π)
    (x : (nilpDeligneCompletedCoefficientFunctor (d := d) hπ).obj B) :
    (nilpDeligneCompletedResidueIso hπ).hom.app B x =
      (x.1, B.completedUnramifiedResidueMapEquiv (uniformizerIdeal hπ) x.2) := rfl

@[simp]
theorem nilpDeligneCompletedResidueIso_inv_app (B : Nilp.{u, u} 𝒪[K] π)
    (x : (nilpDeligneResidueFunctor (d := d) κ (nonzeroUniformizer hπ)).obj B) :
    (nilpDeligneCompletedResidueIso hπ).inv.app B x =
      (x.1, (B.completedUnramifiedResidueMapEquiv (uniformizerIdeal hπ)).symm x.2) := rfl

variable {D : Type u} [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- The action on actual Deligne points with completed coefficients. -/
def nilpDeligneCompletedResidueDivisionAction : (GL (Fin d) K × Dˣ) →*
    Aut (nilpDeligneCompletedCoefficientFunctor (d := d) hπ) :=
  (nilpDeligneCompletedResidueIso (d := d) hπ).symm.conjAut.toMonoidHom.comp
    (nilpDeligneDivisionAction κ hπ)

/-- The comparison from residue coordinates intertwines the two group actions. -/
theorem nilpDeligneCompletedResidueIso_inv_action (g : GL (Fin d) K × Dˣ) :
    (nilpDeligneDivisionAction κ hπ g).hom ≫ (nilpDeligneCompletedResidueIso hπ).inv =
      (nilpDeligneCompletedResidueIso hπ).inv ≫ (nilpDeligneCompletedResidueDivisionAction hπ g).hom := by
  let e := nilpDeligneCompletedResidueIso (d := d) hπ
  let a := nilpDeligneDivisionAction κ hπ g
  change a.hom ≫ e.inv = e.inv ≫ (e.symm.conjAut a).hom
  rw [Iso.conjAut_apply]
  change a.hom ≫ e.inv = e.inv ≫ e.hom ≫ a.hom ≫ e.inv
  simp

/-- The first coordinate carries the projective action. The second is
precomposition by the inverse power of actual completed Frobenius. -/
theorem nilpDeligneCompletedResidueDivisionAction_apply (g : GL (Fin d) K × Dˣ)
    (B : Nilp.{u, u} 𝒪[K] π) (x : (nilpDeligneCompletedCoefficientFunctor (d := d) hπ).obj B) :
    (nilpDeligneCompletedResidueDivisionAction hπ g).hom.app B x =
      ((nilpSheafProjectiveLeftHom hπ (Matrix.ProjGenLinGroup.mk g.1)).hom.app B x.1,
        x.2.comp ((completedUnramifiedFrobenius K ^ (-(residueActionOrder g).toAdd : ℤ)).toAlgHom)) := by
  let e := nilpDeligneCompletedResidueIso (d := d) hπ
  let a := nilpDeligneDivisionAction κ hπ g
  have hact : nilpDeligneCompletedResidueDivisionAction hπ g = e ≪≫ a ≪≫ e.symm := by
    exact Iso.conjAut_apply e.symm a
  rw [hact]
  apply (e.app B).toEquiv.injective
  change (e.app B).toEquiv ((e.app B).toEquiv.symm (a.hom.app B ((e.app B).toEquiv x))) = _
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact nilpDeligneDivisionAction_deligne κ hπ g B ((e.app B).toEquiv x)
  · exact (nilpDeligneDivisionAction_residue κ hπ g B ((e.app B).toEquiv x)).trans
      (completedCoefficient_precomp_frobenius hπ B x.2 (-(residueActionOrder g).toAdd)).symm

end Langlands.DeligneFormalSpace
