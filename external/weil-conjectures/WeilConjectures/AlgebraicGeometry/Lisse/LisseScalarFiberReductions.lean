/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseScalarFiberMaps
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkTensorScalar

/-! # Reductions of the integral scalar comparison

## References

* Deligne, Weil II (1.1.1) b), d), pp. 146-147
* Weil II (1.1.1) b), d), pp. 146-147
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe d
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Pointwise TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

private theorem quotientScalarUnit {R : Type (d + 1)} [CommRing R]
    (I : Ideal R) (M : ModuleCat.{d + 1} R) :
    let adj := ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} (Ideal.Quotient.mk I)
    Function.Surjective (adj.unit.app M).hom ∧
      LinearMap.ker (adj.unit.app M).hom = I • (⊤ : Submodule R M) := by
  let q := Ideal.Quotient.mk I
  let adj := ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} q
  let adj' := ModuleCat.extendRestrictScalarsAdj.{d + 1, d + 1, d + 1} q
  let e := adj.leftAdjointUniq adj'
  let t : ↥((ModuleCat.extendScalars q).obj M) ≃ M ⧸ (I • ⊤ : Submodule R M) :=
    (TensorProduct.quotTensorEquivQuotSMul M I).toEquiv
  let φ := (e.app M).toLinearEquiv.toEquiv.trans t
  have hh (x : M) : φ (adj.unit.app M x) = Submodule.Quotient.mk x := by
    have h := congrArg (fun f ↦ f x) (adj.unit_leftAdjointUniq_hom_app adj' M)
    change (e.app M).hom (adj.unit.app M x) =
      (1 ⊗ₜ[R] x : (R ⧸ I) ⊗[R] M) at h
    change t ((e.app M).hom (adj.unit.app M x)) = _
    rw [h]
    exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I x
  have hz : φ 0 = 0 := by
    simpa only [map_zero, Submodule.Quotient.mk_zero] using hh 0
  constructor
  · intro z
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (I • ⊤ : Submodule R M) (φ z)
    refine ⟨x, φ.injective ?_⟩
    rw [hh]
    exact hx
  · ext x
    change adj.unit.app M x = 0 ↔ x ∈ I • (⊤ : Submodule R M)
    rw [← φ.injective.eq_iff, hh, hz]
    exact Submodule.Quotient.mk_eq_zero _

private theorem scalarMapIsIso {R A : Type (d + 1)} [Ring R] [Ring A]
    (r : R →+* A) {M V : ModuleCat.{d + 1} R} (π : M ⟶ V)
    (hπ : Function.Surjective π.hom)
    (hk : LinearMap.ker π.hom ≤ LinearMap.ker
      ((ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} r).unit.app M).hom) :
    IsIso ((ModuleCat.ringExtendScalars.{d + 1, d + 1} r).map π) := by
  let adj := ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} r
  let E := ModuleCat.ringExtendScalars.{d + 1, d + 1} r
  let δ : V ⟶ (ModuleCat.restrictScalars r).obj (E.obj M) :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars r).obj (E.obj M))
      (((LinearMap.ker π.hom).liftQ (adj.unit.app M).hom hk).comp
      (π.hom.quotKerEquivOfSurjective hπ).symm.toLinearMap)
  have hδ : π ≫ δ = adj.unit.app M := by
    apply ModuleCat.hom_ext
    ext x
    change (LinearMap.ker π.hom).liftQ (adj.unit.app M).hom hk
      ((π.hom.quotKerEquivOfSurjective hπ).symm (π x)) = _
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  let k := (adj.homEquiv V (E.obj M)).symm δ
  have hk₁ : E.map π ≫ k = 𝟙 (E.obj M) := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
    simpa only [Adjunction.homEquiv_apply, E, Functor.map_id, Category.comp_id] using! hδ
  have : Epi π := (ModuleCat.epi_iff_surjective _).mpr hπ
  have hk₂ : k ≫ E.map π = 𝟙 (E.obj V) := by
    apply (adj.homEquiv _ _).injective
    apply (cancel_epi π).mp
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, ← Category.assoc, hδ]
    simpa only [Adjunction.homEquiv_apply, E, Functor.map_id, Category.comp_id,
      Functor.id_map, Functor.comp_map] using! (adj.unit.naturality π).symm
  exact ⟨⟨k, hk₁, hk₂⟩⟩

variable (Y : Scheme.{d}) {Ω : Type d} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y) (l : ℕ) [Fact l.Prime]
  (E : Type (d + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (L : Type (d + 1)) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private lemma uniformizerIdeal_eq (B : Type (d + 1)) [Field B]
    [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B] :
    Ideal.span ({Padic.coefficientExtensionUniformizer l B} :
      Set (Padic.coefficientExtensionIntegers l B)) =
        Padic.coefficientExtensionMaximalIdeal l B :=
  (Padic.coefficientExtensionIntegers_dvr l B).choose_spec
      |>.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec

private lemma scalarIndex_eq (n : ℕ) :
    lisseScalarSourceIndex l E L ι n = n / lisseRamificationIndex l E L ι := by
  have he : 0 < lisseRamificationIndex l E L ι :=
    (lisseRamificationIndex_exists l E L ι).choose_spec.1
  dsimp only [lisseScalarSourceIndex]
  have hn : n + 1 + lisseRamificationIndex l E L ι - 1 =
      n + lisseRamificationIndex l E L ι := by omega
  rw [hn, Nat.add_div_right _ he]
  exact Nat.add_sub_cancel _ 1

private lemma scalarIndex_ideal (n : ℕ) :
    Ideal.map (lisseIntegerInclusion l E L ι)
        (Padic.coefficientExtensionIdeal l E (lisseScalarSourceIndex l E L ι n + 1)) ≤
      Padic.coefficientExtensionIdeal l L (n + 1) := by
  have he : 0 < lisseRamificationIndex l E L ι :=
    (lisseRamificationIndex_exists l E L ι).choose_spec.1
  have hr : Ideal.map (lisseIntegerInclusion l E L ι)
      (Padic.coefficientExtensionMaximalIdeal l E) =
        Padic.coefficientExtensionMaximalIdeal l L ^ lisseRamificationIndex l E L ι :=
    (lisseRamificationIndex_exists l E L ι).choose_spec.2
  dsimp only [Padic.coefficientExtensionIdeal]
  rw [Ideal.map_pow, uniformizerIdeal_eq l E, hr, ← uniformizerIdeal_eq l L,
    ← pow_mul]
  apply Ideal.pow_le_pow_right
  rw [scalarIndex_eq l E L ι n]
  exact Nat.lt_mul_div_succ n he

private lemma sourceProjectionIsIso (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    IsIso ((ModuleCat.ringExtendScalars.{d + 1, d + 1}
      (lisseScalarCoefficientMap l E L ι n)).map
        (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{d + 1}.sheafFiber)
          (op (lisseScalarSourceIndex l E L ι n)))) := by
  let r := lisseScalarCoefficientMap l E L ι n
  let M := lisseIntegralFiber l E Y y F
  let adj := ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} r
  apply scalarMapIsIso r _ (lisseIntegralFiber_projection Y y l E F _).1
  rw [(lisseIntegralFiber_projection Y y l E F _).2]
  apply Submodule.smul_le.mpr
  intro a ha x _
  change adj.unit.app M (a • x) = 0
  rw [map_smul, ModuleCat.restrictScalars.smul_def]
  have hra : r a = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply scalarIndex_ideal l E L ι n
    exact Ideal.mem_map_of_mem _ ha
  rw [hra, zero_smul]

local instance scalarReductionSheafify (B : Type (d + 1)) [Ring B] :
    HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{d + 1} B) :=
  (GrothendieckTopology.hasSheafify_smallEtaleTopology
    (ModuleCat.{d + 1} B) Y).isRightAdjoint

private def stalkScalarIso {R A : Type (d + 1)} [Ring R] [Ring A]
    (r : R →+* A) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{d + 1} R)) :
    (ModuleCat.ringExtendScalars.{d + 1, d + 1} r).obj
        ((pointSmallEtale y).ulift.{d + 1}.sheafFiber.obj F) ≅
      (pointSmallEtale y).ulift.{d + 1}.sheafFiber.obj
        ((Sheaf.ringExtendScalars.{d + 1, d + 1} Y.smallEtaleTopology r).obj F) :=
  let p := (pointSmallEtale y).ulift.{d + 1}
  let E := ModuleCat.ringExtendScalars.{d + 1, d + 1} r
  let := (ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} r).isLeftAdjoint
  ((p.presheafFiberCompIso E).app F.obj).symm ≪≫
    ((p.presheafToSheafCompSheafFiberIso (ModuleCat.{d + 1} A)).app (F.obj ⋙ E)).symm

private lemma scalarCompUnit {R S A : Type (d + 1)} [Ring R] [Ring S] [Ring A]
    (α : R →+* S) (q : S →+* A) (M : ModuleCat.{d + 1} R) (z : M) :
    (ModuleCat.ringExtensionComp.{d + 1, d + 1} α q).hom.app M
        ((ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} q).unit.app _
          ((ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} α).unit.app M z)) =
      (ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} (q.comp α)).unit.app M z := by
  let adj₁ := ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} α
  let adj₂ := ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} q
  let adj₃ := ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} (q.comp α)
  have h := congrArg (fun f ↦ f z)
    ((adj₁.comp adj₂).unit_leftAdjointUniq_hom_app
      (adj₃.ofNatIsoRight (ModuleCat.restrictScalarsComp α q)) M)
  exact h

private def reductionComparison (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    let q := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1))
    let W := (ModuleCat.ringExtendScalars.{d + 1, d + 1}
      (lisseIntegerInclusion l E L ι)).obj (lisseIntegralFiber l E Y y F)
    (ModuleCat.restrictScalars.{d + 1} q).obj
      ((ModuleCat.ringExtendScalars.{d + 1, d + 1} q).obj W) ≅
      (pointSmallEtale y).ulift.{d + 1}.sheafFiber.obj
        (((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F).obj.obj (op n)) := by
  let p := (pointSmallEtale y).ulift.{d + 1}
  let α := lisseIntegerInclusion l E L ι
  let q := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1))
  let r := lisseScalarCoefficientMap l E L ι n
  let Fₙ := F.obj.obj (op (lisseScalarSourceIndex l E L ι n))
  let π := limit.π (F.obj ⋙ p.sheafFiber) (op (lisseScalarSourceIndex l E L ι n))
  let D := (Sheaf.ringExtendScalars.{d + 1, d + 1} Y.smallEtaleTopology r).obj Fₙ
  have := sourceProjectionIsIso Y y l E L ι F n
  let c := (ModuleCat.ringExtensionComp.{d + 1, d + 1} α q).app
    (lisseIntegralFiber l E Y y F) ≪≫
      asIso ((ModuleCat.ringExtendScalars.{d + 1, d + 1} r).map π) ≪≫
        stalkScalarIso Y y r Fₙ
  let := (ModuleCat.restrictCoextendScalarsAdj.{d + 1, d + 1, d + 1} q).isLeftAdjoint
  exact (ModuleCat.restrictScalars.{d + 1} q).mapIso c ≪≫
    ((p.sheafFiberCompIso (ModuleCat.restrictScalars.{d + 1} q)).app D).symm ≪≫
      (p.sheafFiber.mapIso ((lisseIntegralScalarExtensionData l E Y L ι).levelIso F n)).symm

private lemma reductionComparison_unit (F : LisseIntegralSheaf l E Y) (n : ℕ)
    (z : lisseIntegralFiber l E Y y F) (U : Y.Etale)
    (x : (pointSmallEtale y).ulift.{d + 1}.fiber.obj U)
    (s : (F.obj.obj (op (lisseScalarSourceIndex l E L ι n))).obj.obj (op U))
    (hs : limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{d + 1}.sheafFiber)
      (op (lisseScalarSourceIndex l E L ι n)) z =
        (pointSmallEtale y).ulift.{d + 1}.toPresheafFiber U x
          (F.obj.obj (op (lisseScalarSourceIndex l E L ι n))).obj s) :
    let α := lisseIntegerInclusion l E L ι
    let q := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1))
    let W := (ModuleCat.ringExtendScalars.{d + 1, d + 1} α).obj
      (lisseIntegralFiber l E Y y F)
    (pointSmallEtale y).ulift.{d + 1}.sheafFiber.map
      ((lisseIntegralScalarExtensionData l E Y L ι).levelIso F n).hom
        ((reductionComparison Y y l E L ι F n).hom
          ((ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} q).unit.app W
            ((ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} α).unit.app _ z))) =
      (pointSmallEtale y).ulift.{d + 1}.toPresheafFiber U x
        (lisseIntegralScalarLevel l E Y L ι F n).obj
          (lisseIntegralScalarGenerator l E Y L ι F n U 1 s) := by
  let p := (pointSmallEtale y).ulift.{d + 1}
  let α := lisseIntegerInclusion l E L ι
  let q := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1))
  let r := lisseScalarCoefficientMap l E L ι n
  let M := lisseIntegralFiber l E Y y F
  let Fₙ := F.obj.obj (op (lisseScalarSourceIndex l E L ι n))
  let π := limit.π (F.obj ⋙ p.sheafFiber) (op (lisseScalarSourceIndex l E L ι n))
  let D := (Sheaf.ringExtendScalars.{d + 1, d + 1} Y.smallEtaleTopology r).obj Fₙ
  let Efun := ModuleCat.ringExtendScalars.{d + 1, d + 1} r
  let adj := ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} r
  let c := stalkScalarIso Y y r Fₙ
  let := (ModuleCat.restrictCoextendScalarsAdj.{d + 1, d + 1, d + 1} q).isLeftAdjoint
  let e := p.sheafFiberCompIso (ModuleCat.restrictScalars.{d + 1} q)
  let t := p.sheafFiber.mapIso ((lisseIntegralScalarExtensionData l E Y L ι).levelIso F n)
  have hπ := congrArg (fun f ↦ f z) (adj.unit.naturality π)
  change adj.unit.app _ (π z) = Efun.map π (adj.unit.app M z) at hπ
  have hc := congrArg (fun f ↦ f s)
    ((etale_stalk_scalar_component_unique y r Efun adj Fₙ).2.1 U x)
  change c.hom (adj.unit.app _ (p.toPresheafFiber U x Fₙ.obj s)) =
    p.toPresheafFiber U x D.obj
      ((toSheafify Y.smallEtaleTopology (Fₙ.obj ⋙ Efun)).app (op U)
        (adj.unit.app _ s)) at hc
  have he := congrArg (fun f ↦ f
    ((toSheafify Y.smallEtaleTopology (Fₙ.obj ⋙ Efun)).app (op U)
      (adj.unit.app _ s)))
    (p.toPresheafFiber_presheafFiberCompIso_hom_app
      (ModuleCat.restrictScalars.{d + 1} q) U x D.obj)
  have hgen : lisseIntegralScalarGenerator l E Y L ι F n U 1 s =
      (toSheafify Y.smallEtaleTopology (Fₙ.obj ⋙ Efun)).app (op U)
        (adj.unit.app _ s) := by
    simp only [lisseIntegralScalarGenerator, ModuleCat.ringExtensionTmul, one_smul]
    rfl
  change e.hom.app D
      (p.toPresheafFiber U x (lisseIntegralScalarLevel l E Y L ι F n).obj
        ((toSheafify Y.smallEtaleTopology (Fₙ.obj ⋙ Efun)).app (op U)
          (adj.unit.app _ s))) =
      p.toPresheafFiber U x D.obj
        ((toSheafify Y.smallEtaleTopology (Fₙ.obj ⋙ Efun)).app (op U)
          (adj.unit.app _ s)) at he
  change t.hom (t.inv (e.inv.app D (c.hom (Efun.map π
    ((ModuleCat.ringExtensionComp.{d + 1, d + 1} α q).hom.app M
      ((ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} q).unit.app _
        ((ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} α).unit.app M z))))))) = _
  rw [scalarCompUnit]
  change t.hom (t.inv (e.inv.app D (c.hom (Efun.map π (adj.unit.app M z))))) = _
  rw [← hπ, hs, hc, ← he, ← hgen]
  rw [← ConcreteCategory.comp_apply, t.inv_hom_id]
  exact ConcreteCategory.congr_hom (e.hom_inv_id_app D) _

/-- Every target-level projection of the scalar comparison is the coefficient quotient. -/
theorem lisseIntegralScalarFiberComparison_reductions (F : LisseIntegralSheaf l E Y)
    (n : ℕ) :
    let S := Padic.coefficientExtensionIntegers l L
    let J := Ideal.span ({Padic.coefficientExtensionUniformizer l L} : Set S)
    let M := (ModuleCat.ringExtendScalars.{d + 1, d + 1}
      (lisseIntegerInclusion l E L ι)).obj (lisseIntegralFiber l E Y y F)
    let D := ((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F).obj ⋙
      (pointSmallEtale y).ulift.{d + 1}.sheafFiber
    let q := (lisseIntegralScalarFiberComparison Y y l E L ι F ≫ limit.π D (op n)).hom
    Function.Surjective q ∧ LinearMap.ker q = J ^ (n + 1) • (⊤ : Submodule S M) := by
  let p := (pointSmallEtale y).ulift.{d + 1}
  let α := lisseIntegerInclusion l E L ι
  let q := Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1))
  let W := (ModuleCat.ringExtendScalars.{d + 1, d + 1} α).obj
    (lisseIntegralFiber l E Y y F)
  let D := ((lisseIntegralScalarExtensionData l E Y L ι).functor.obj F).obj ⋙ p.sheafFiber
  let c := lisseIntegralScalarFiberComparison Y y l E L ι F
  let η := (ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} q).unit.app W
  let e := reductionComparison Y y l E L ι F n
  have hc : c ≫ limit.π D (op n) = η ≫ e.hom := by
    let adj := ModuleCat.ringExtendScalarsAdj.{d + 1, d + 1} α
    apply (adj.homEquiv _ _).injective
    apply ModuleCat.hom_ext
    ext z
    apply (ConcreteCategory.bijective_of_isIso
      (p.sheafFiber.map ((lisseIntegralScalarExtensionData l E Y L ι).levelIso F n).hom)).1
    obtain ⟨U, x, s, hs⟩ := p.toPresheafFiber_jointly_surjective
      (P := (F.obj.obj (op (lisseScalarSourceIndex l E L ι n))).obj)
        (limit.π (F.obj ⋙ p.sheafFiber) (op (lisseScalarSourceIndex l E L ι n)) z)
    have h₁ := lisseIntegralScalarFiberComparison_spec Y y l E L ι F n z U x s hs.symm
    have h₂ := reductionComparison_unit Y y l E L ι F n z U x s hs.symm
    change p.sheafFiber.map
        ((lisseIntegralScalarExtensionData l E Y L ι).levelIso F n).hom
          (limit.π D (op n) (c (adj.unit.app _ z))) =
      p.sheafFiber.map ((lisseIntegralScalarExtensionData l E Y L ι).levelIso F n).hom
        (e.hom (η (adj.unit.app _ z)))
    simpa only [ModuleCat.ringExtensionTmul, one_smul] using h₁.trans h₂.symm
  change Function.Surjective (c ≫ limit.π D (op n)).hom ∧
    LinearMap.ker (c ≫ limit.π D (op n)).hom = _
  rw [hc]
  have hη := quotientScalarUnit (Padic.coefficientExtensionIdeal l L (n + 1)) W
  have he := ConcreteCategory.bijective_of_isIso e.hom
  refine ⟨he.2.comp hη.1, ?_⟩
  change LinearMap.ker (e.hom.hom.comp η.hom) = _
  rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr he.1, Submodule.comap_bot]
  exact hη.2

end
end AlgebraicGeometry.Scheme
