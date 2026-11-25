import Langlands.Geometry.FormalGroup.DeligneNilpAction
import Langlands.Geometry.FormalGroup.HarrisComponentQuotient
import Langlands.Geometry.FormalGroup.DrinfeldFramedClassFunctor
import Mathlib.FieldTheory.Finite.Basic

/-! # Deligne classes with the residue coordinate and its Frobenius action -/

noncomputable section
universe u

namespace Langlands.DeligneFormalSpace

open CategoryTheory ValuativeRel Langlands.CentralDivision
open scoped MatrixGroups WithZero

section ResidueCoordinate

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
variable {F : Type u} [Field F] [Algebra O F]
variable (κ : Type u) [CommRing κ] [Algebra O κ]
variable (hπ : algebraMap O F π ≠ 0)

/-- Actual Deligne points together with a map of the residue scalar algebra into the reduction. -/
def nilpDeligneResidueFunctor : FormalGroup.Nilp.{u, u} O π ⥤ Type (u + 1) where
  obj B := (nilpSheafClassFunctor d π F hπ).obj B ×
    (FormalGroup.Nilp.residueMapFunctor O O π κ).obj B
  map f := ↾(fun x => ((nilpSheafClassFunctor d π F hπ).map f x.1,
    (FormalGroup.Nilp.residueMapFunctor O O π κ).map f x.2))
  map_id B := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · exact ConcreteCategory.congr_hom ((nilpSheafClassFunctor d π F hπ).map_id B) x.1
    · exact ConcreteCategory.congr_hom ((FormalGroup.Nilp.residueMapFunctor O O π κ).map_id B) x.2
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · exact ConcreteCategory.congr_hom ((nilpSheafClassFunctor d π F hπ).map_comp f g) x.1
    · exact ConcreteCategory.congr_hom ((FormalGroup.Nilp.residueMapFunctor O O π κ).map_comp f g) x.2

/-- A natural automorphism on Deligne points and inverse precomposition on residue maps. -/
def nilpDeligneResidueAut (e : Aut (nilpSheafClassFunctor d π F hπ)) (a : κ ≃ₐ[O] κ) :
    Aut (nilpDeligneResidueFunctor (d := d) κ hπ) :=
  Aut.of <| NatIso.ofComponents (fun B => Equiv.toIso
    ((e.asIso.app B).toEquiv.prodCongr {
      toFun := fun ψ => ψ.comp a.symm.toAlgHom
      invFun := fun ψ => ψ.comp a.toAlgHom
      left_inv := fun ψ => by
        change κ →ₐ[O] ((FormalGroup.Nilp.reductionFunctor O π).obj B).obj at ψ
        apply AlgHom.ext
        intro t
        change ψ (a.symm (a t)) = ψ t
        rw [a.symm_apply_apply]
      right_inv := fun ψ => by
        change κ →ₐ[O] ((FormalGroup.Nilp.reductionFunctor O π).obj B).obj at ψ
        apply AlgHom.ext
        intro t
        change ψ (a (a.symm t)) = ψ t
        rw [a.apply_symm_apply] })) (by
    intro B B' f
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (e.asIso.hom.naturality f) x.1
    · rfl)

@[simp]
theorem nilpDeligneResidueAut_hom_app (e : Aut (nilpSheafClassFunctor d π F hπ))
    (a : κ ≃ₐ[O] κ) (B : FormalGroup.Nilp.{u, u} O π)
    (x : (nilpDeligneResidueFunctor (d := d) κ hπ).obj B) :
    (nilpDeligneResidueAut κ hπ e a).asIso.hom.app B x =
      (e.asIso.hom.app B x.1, x.2.comp a.symm.toAlgHom) := rfl

/-- The two independent actions commute and act naturally on the paired points. -/
def nilpDeligneResidueAutHom :
    Aut (nilpSheafClassFunctor d π F hπ) × (κ ≃ₐ[O] κ) →*
      Aut (nilpDeligneResidueFunctor (d := d) κ hπ) where
  toFun x := nilpDeligneResidueAut κ hπ x.1 x.2
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext B
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · change x.2.comp (AlgHom.id O κ) = x.2
      exact AlgHom.comp_id _
  map_mul' e f := by
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext B
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · rfl

end ResidueCoordinate

section LocalField

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
variable [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
variable [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {d : ℕ} [NeZero d] {π : 𝒪[K]}
variable (κ : Type u) [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
variable [IsScalarTower 𝒪[K] 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ]

/-- The card-power Frobenius of the residue field, on the chosen algebraic residue extension. -/
def residueFrobenius : κ ≃ₐ[𝒪[K]] κ := by
  letI := Fintype.ofFinite 𝓀[K]
  exact (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] κ).restrictScalars 𝒪[K]

@[simp]
theorem residueFrobenius_apply (a : κ) :
    residueFrobenius (K := K) κ a = a ^ Nat.card 𝓀[K] := by
  let : Fintype 𝓀[K] := Fintype.ofFinite 𝓀[K]
  change a ^ Fintype.card 𝓀[K] = a ^ Nat.card 𝓀[K]
  rw [Nat.card_eq_fintype_card]

private abbrev localScalarOrder : Kˣ →* Multiplicative ℤ :=
  FormalGroup.Harris.valuationUnitOrder
    ((valuation K).map ⟨(IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidWithZeroHom,
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.monotone⟩)

/-- The exponent in Drinfeld's residue action is the sum of the determinant
and division reduced-norm orders. -/
def residueActionOrder : GL (Fin d) K × Dˣ →* Multiplicative ℤ where
  toFun g := localScalarOrder (K := K) (Matrix.GeneralLinearGroup.det g.1) *
    FormalGroup.Harris.valuationUnitOrder (localReducedNormIntValuation K D) g.2
  map_one' := by simp
  map_mul' g h := by
    change localScalarOrder (K := K) (Matrix.GeneralLinearGroup.det (g.1 * h.1)) *
      FormalGroup.Harris.valuationUnitOrder (localReducedNormIntValuation K D) (g.2 * h.2) = _
    simp only [map_mul]
    ac_rfl

private def residueFrobeniusPowers : Multiplicative ℤ →* (κ ≃ₐ[𝒪[K]] κ) where
  toFun n := residueFrobenius κ ^ n.toAdd
  map_one' := zpow_zero _
  map_mul' m n := zpow_add _ m.toAdd n.toAdd

/-- The ordinary left action on the two Deligne-side coordinates in Drinfeld's theorem. -/
def nilpDeligneDivisionAction (hπ : Irreducible π) :
    (GL (Fin d) K × Dˣ) →* Aut (nilpDeligneResidueFunctor (d := d) κ
      (coefficientUniformizer_ne_zero (F := K) hπ)) :=
  (nilpDeligneResidueAutHom (d := d) κ _).comp
    ((((nilpSheafProjectiveLeftHom hπ).comp Matrix.ProjGenLinGroup.mk).comp
      (MonoidHom.fst (GL (Fin d) K) Dˣ)).prod
      ((residueFrobeniusPowers κ).comp (residueActionOrder (d := d))))

/-- The residue coordinate changes by precomposition with the negative order power. -/
theorem nilpDeligneDivisionAction_residue (hπ : Irreducible π) (g : GL (Fin d) K × Dˣ)
    (B : FormalGroup.Nilp.{u, u} 𝒪[K] π)
    (x : (nilpDeligneResidueFunctor (d := d) κ (coefficientUniformizer_ne_zero (F := K) hπ)).obj B) :
    ((nilpDeligneDivisionAction κ hπ g).asIso.hom.app B x).2 =
      x.2.comp ((residueFrobenius κ ^ (-(residueActionOrder g).toAdd : ℤ)).toAlgHom) := by
  change x.2.comp ((residueFrobenius κ ^ (residueActionOrder g).toAdd).symm.toAlgHom) = _
  rw [zpow_neg]
  rfl

/-- The Deligne coordinate carries the existing ordinary left projective action. -/
theorem nilpDeligneDivisionAction_deligne (hπ : Irreducible π) (g : GL (Fin d) K × Dˣ)
    (B : FormalGroup.Nilp.{u, u} 𝒪[K] π)
    (x : (nilpDeligneResidueFunctor (d := d) κ (coefficientUniformizer_ne_zero (F := K) hπ)).obj B) :
    ((nilpDeligneDivisionAction κ hπ g).asIso.hom.app B x).1 =
      (nilpSheafProjectiveLeftHom hπ (Matrix.ProjGenLinGroup.mk g.1)).asIso.hom.app B x.1 := rfl

omit [NeZero d] in
/-- A scalar matrix and its inverse central division unit have total order zero. -/
theorem residueActionOrder_diagonalScalar (hd : d = CentralSimple.reducedDegree K D) (a : Kˣ) :
    residueActionOrder (Matrix.GeneralLinearGroup.scalar (Fin d) a,
      Units.map (algebraMap K D).toMonoidHom a⁻¹) = 1 := by
  let orderD := FormalGroup.Harris.valuationUnitOrder (localReducedNormIntValuation K D)
  have horder : orderD (Units.map (algebraMap K D).toMonoidHom a) =
      localScalarOrder (a ^ d) := by
    change Multiplicative.ofAdd (-WithZero.log
      (localReducedNormIntValuation K D (algebraMap K D (a : K)))) =
      Multiplicative.ofAdd (-WithZero.log
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (↑(a ^ d) : K))))
    rw [localReducedNormIntValuation_algebraMap, ← hd, Units.val_pow_eq_pow_val, map_pow, map_pow]
  change localScalarOrder (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin d) a)) *
    orderD (Units.map (algebraMap K D).toMonoidHom a⁻¹) = 1
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_inv, map_inv, horder,
    mul_inv_cancel]

/-- The stated diagonal central subgroup acts trivially on both coordinates. -/
theorem nilpDeligneDivisionAction_diagonalScalar (hπ : Irreducible π)
    (hd : d = CentralSimple.reducedDegree K D) (a : Kˣ) :
    nilpDeligneDivisionAction κ hπ (Matrix.GeneralLinearGroup.scalar (Fin d) a,
      Units.map (algebraMap K D).toMonoidHom a⁻¹) = 1 := by
  let g : GL (Fin d) K × Dˣ := (Matrix.GeneralLinearGroup.scalar (Fin d) a,
    Units.map (algebraMap K D).toMonoidHom a⁻¹)
  change nilpDeligneResidueAutHom (d := d) κ (coefficientUniformizer_ne_zero (F := K) hπ)
    (nilpSheafProjectiveLeftHom hπ (Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin d) a)),
      (residueFrobeniusPowers κ) (residueActionOrder g)) = 1
  rw [Matrix.ProjGenLinGroup.mk_scalar, show residueActionOrder g = 1 from
    residueActionOrder_diagonalScalar hd a]
  simp only [map_one]
  exact (nilpDeligneResidueAutHom (d := d) κ (coefficientUniformizer_ne_zero (F := K) hπ)).map_one

end LocalField
end Langlands.DeligneFormalSpace
